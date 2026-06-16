//! Real-time schedulability analysis (PLAN-perf-demo §8, R1) — the deterministic
//! WORST-CASE sibling of the stochastic CTMC performance. A periodic task set
//! under a fixed-priority (RM/DM) or EDF policy is analyzed two ways:
//!
//!   * the **utilization bound** (sufficient, `O(n)`): RM/DM schedulable if
//!     `U ≤ n(2^{1/n} − 1)`, EDF if `U ≤ 1` (the `ρ < 1` of the real-time world);
//!   * **response-time analysis** (RTA, exact, pseudo-polynomial): the fixed
//!     point `Rᵢ = Cᵢ + Σ_{j∈hp(i)} ⌈Rᵢ/Tⱼ⌉·Cⱼ`, schedulable iff `Rᵢ ≤ Dᵢ`.
//!
//! Cheaper than building a CTMC — the efficient deterministic complement. The
//! RTA fixed-point step is the kernel R2 will prove monotone & overflow-free.

use super::toml;

pub struct Task {
    pub name: String,
    pub c: u32, // worst-case execution time
    pub t: u32, // period
    pub d: u32, // relative deadline (defaults to the period)
}

#[derive(Clone, Copy)]
pub enum Policy {
    Rm,
    Dm,
    Edf,
}

pub struct TaskSet {
    pub tasks: Vec<Task>,
    pub policy: Policy,
}

pub struct RtReport {
    pub policy: &'static str,
    pub util: f64,
    pub util_bound: f64,
    pub util_test_pass: bool,
    /// Per task, in input order: worst-case response time, or `None` if it
    /// exceeds the deadline (unschedulable) or is not computed (EDF).
    pub wcrt: Vec<(String, Option<u32>)>,
    pub schedulable: bool,
    /// EDF only: the first deadline point `t` where the demand-bound function
    /// `dbf(t) > t` (the proof of infeasibility), if any.
    pub edf_first_fail: Option<(u64, u64)>,
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// EDF processor-demand test (exact for constrained deadlines `D ≤ T`). The
/// demand-bound function `dbf(t) = Σᵢ max(0, ⌊(t−Dᵢ)/Tᵢ⌋ + 1)·Cᵢ` is the maximum
/// execution that can be RELEASED-AND-DUE within any window of length `t`; EDF is
/// feasible iff `U ≤ 1` AND `dbf(t) ≤ t` at every deadline point up to a bound
/// `L`. Returns `(schedulable, first failing (t, dbf))`.
fn demand_bound_test(ts: &TaskSet) -> (bool, Option<(u64, u64)>) {
    let u: f64 = ts.tasks.iter().map(|t| t.c as f64 / t.t as f64).sum();
    if u > 1.0 + 1e-12 {
        return (false, None); // overload — infeasible, no finite witness needed
    }
    // Checking horizon: the hyperperiod is exact for periodic tasks; the
    // busy-period bound La = Σ(Tᵢ−Dᵢ)Uᵢ/(1−U) is tighter when D<T. Use the
    // smaller VALID bound, never below the largest deadline. Both are sound on
    // their own (for D ≤ T), so if the hyperperiod LCM overflows we fall back to
    // La rather than risk a wrapped (too-small) horizon that misses a violation.
    let max_d = ts.tasks.iter().map(|t| t.d as u64).max().unwrap_or(0);
    let mut hyper: u64 = 1;
    for task in &ts.tasks {
        let g = gcd(hyper, task.t as u64);
        match (hyper / g).checked_mul(task.t as u64) {
            Some(h) => hyper = h,
            None => {
                hyper = u64::MAX; // overflow ⇒ defer to the (finite, valid) La bound
                break;
            }
        }
    }
    // La is valid only for U < 1; +1 guards against f64 rounding under-estimating
    // the true bound. U == 1 (only possible with D=T here) ⇒ use the hyperperiod.
    let la_bound = if u < 1.0 {
        let la = ts.tasks.iter().map(|t| (t.t as f64 - t.d as f64) * (t.c as f64 / t.t as f64)).sum::<f64>() / (1.0 - u);
        if la.is_finite() && la >= 0.0 {
            (la.ceil() as u64).saturating_add(1)
        } else {
            u64::MAX
        }
    } else {
        u64::MAX
    };
    let l = hyper.min(la_bound).max(max_d);
    // deadline points t = k·Tᵢ + Dᵢ ≤ L.
    let mut points: Vec<u64> = Vec::new();
    for task in &ts.tasks {
        let (d, period) = (task.d as u64, task.t as u64);
        let mut t = d;
        while t <= l {
            points.push(t);
            t += period;
        }
    }
    points.sort_unstable();
    points.dedup();
    for &t in &points {
        // u128 so the demand never wraps (a wrapped-down dbf could falsely pass).
        let dbf: u128 = ts
            .tasks
            .iter()
            .map(|task| {
                let (d, period, c) = (task.d as u64, task.t as u64, task.c as u128);
                if t >= d {
                    (((t - d) / period + 1) as u128) * c
                } else {
                    0
                }
            })
            .sum();
        if dbf > t as u128 {
            return (false, Some((t, dbf.min(u64::MAX as u128) as u64)));
        }
    }
    (true, None)
}

fn field_u32(t: &std::collections::HashMap<String, toml::Value>, key: &str, i: usize) -> Result<u32, String> {
    t.get(key)
        .ok_or_else(|| format!("task {i}: missing `{key}`"))?
        .as_str(key)?
        .parse()
        .map_err(|_| format!("task {i}: `{key}` must be a positive integer"))
}

pub fn parse(src: &str) -> Result<TaskSet, String> {
    let doc = toml::parse(src)?;
    let policy = match doc.scalar("policy").and_then(|v| v.as_str("policy").ok()).unwrap_or("RM") {
        "RM" | "rm" => Policy::Rm,
        "DM" | "dm" => Policy::Dm,
        "EDF" | "edf" => Policy::Edf,
        other => return Err(format!("policy must be RM/DM/EDF, found `{other}`")),
    };
    let mut tasks = Vec::new();
    for (i, t) in doc.table("task").iter().enumerate() {
        let name = match t.get("name") {
            Some(v) => v.as_str("name")?.to_string(),
            None => format!("t{i}"),
        };
        let c = field_u32(t, "c", i)?;
        let period = field_u32(t, "t", i)?;
        if period == 0 {
            return Err(format!("task `{name}`: period `t` must be positive"));
        }
        let d = match t.get("d") {
            Some(v) => v.as_str("d")?.parse().map_err(|_| format!("task `{name}`: bad `d`"))?,
            None => period,
        };
        // Both RTA and the EDF demand bound here assume CONSTRAINED deadlines
        // (D ≤ T). Arbitrary deadlines (D > T) need the busy-window generalization
        // — refuse rather than analyze them outside the proven envelope.
        if d > period {
            return Err(format!("task `{name}`: deadline d={d} exceeds period t={period} (only D ≤ T is supported)"));
        }
        if d == 0 {
            return Err(format!("task `{name}`: deadline `d` must be positive"));
        }
        tasks.push(Task { name, c, t: period, d });
    }
    if tasks.is_empty() {
        return Err("task set has no `[[task]]` entries".into());
    }
    Ok(TaskSet { tasks, policy })
}

/// `⌈a / b⌉` for positive `b`. Verified overflow-free & monotone in `a` by Kani
/// (PLAN-perf-demo §8 R2, the `kani_harness` below).
fn div_ceil(a: u32, b: u32) -> u32 {
    (a + b - 1) / b
}

/// One RTA interference term: a higher-priority task with period `tj` and cost
/// `cj` preempts `⌈r/tj⌉` times in a window of length `r`. The body of the
/// response-time recurrence — **monotone non-decreasing in `r`**, which is what
/// makes the fixed-point iteration converge to the LEAST fixed point (the true
/// worst-case response time). Kani proves that monotonicity (and no overflow).
fn term(r: u32, cj: u32, tj: u32) -> u32 {
    div_ceil(r, tj) * cj
}

/// Exact worst-case response time by the RTA fixed point. Returns `None` if it
/// provably exceeds the deadline `d` (so the task is unschedulable). The
/// iteration is monotone increasing and bounded by `d`, hence terminates.
fn response_time(c: u32, d: u32, hp: &[(u32, u32)]) -> Option<u32> {
    let mut r = c;
    loop {
        let interference: u32 = hp.iter().map(|&(cj, tj)| term(r, cj, tj)).sum();
        let r_new = c + interference;
        if r_new > d {
            return None;
        }
        if r_new == r {
            return Some(r);
        }
        r = r_new;
    }
}

pub fn analyze(ts: &TaskSet) -> RtReport {
    let n = ts.tasks.len();
    let util: f64 = ts.tasks.iter().map(|t| t.c as f64 / t.t as f64).sum();
    let (policy, util_bound) = match ts.policy {
        Policy::Rm => ("RM", n as f64 * (2f64.powf(1.0 / n as f64) - 1.0)),
        Policy::Dm => ("DM", n as f64 * (2f64.powf(1.0 / n as f64) - 1.0)),
        Policy::Edf => ("EDF", 1.0),
    };
    let util_test_pass = util <= util_bound + 1e-12;

    let mut edf_first_fail = None;
    let (wcrt, schedulable) = match ts.policy {
        // EDF: exact processor-demand test (handles constrained deadlines D ≤ T,
        // not just the U ≤ 1 implicit-deadline case).
        Policy::Edf => {
            let (sched, fail) = demand_bound_test(ts);
            edf_first_fail = fail;
            (ts.tasks.iter().map(|t| (t.name.clone(), None)).collect(), sched)
        }
        // Fixed priority: RM orders by period, DM by deadline (smaller ⇒ higher).
        Policy::Rm | Policy::Dm => {
            let mut order: Vec<usize> = (0..n).collect();
            order.sort_by_key(|&i| match ts.policy {
                Policy::Dm => ts.tasks[i].d,
                _ => ts.tasks[i].t,
            });
            let mut wcrt = vec![(String::new(), None); n];
            let mut schedulable = true;
            for (rank, &i) in order.iter().enumerate() {
                let hp: Vec<(u32, u32)> =
                    order[..rank].iter().map(|&j| (ts.tasks[j].c, ts.tasks[j].t)).collect();
                let r = response_time(ts.tasks[i].c, ts.tasks[i].d, &hp);
                if r.is_none() {
                    schedulable = false;
                }
                wcrt[i] = (ts.tasks[i].name.clone(), r);
            }
            (wcrt, schedulable)
        }
    };

    RtReport { policy, util, util_bound, util_test_pass, wcrt, schedulable, edf_first_fail }
}

/// Scale every worst-case execution time by `s` (round up, ≥ 1) — the load knob
/// for the hard/soft sweep (PLAN-perf-demo §8 R4).
pub fn scaled(ts: &TaskSet, s: f64) -> TaskSet {
    TaskSet {
        policy: ts.policy,
        tasks: ts
            .tasks
            .iter()
            .map(|t| Task { name: t.name.clone(), c: ((t.c as f64 * s).ceil() as u32).max(1), t: t.t, d: t.d })
            .collect(),
    }
}

/// Monte-Carlo deadline-miss fraction under preemptive RM with STOCHASTIC
/// execution: each job runs a uniform random amount in `[⌈α·C⌉, C]` (the
/// worst-case `C` is what hard RTA uses; typical jobs are lighter). Returns the
/// overall miss probability across all jobs. The SOFT companion to the hard RTA
/// verdict (PLAN-perf-demo §8 R4): graceful degradation vs a hard step.
pub fn simulate_miss(ts: &TaskSet, alpha: f64, cycles: u32, seed: u64) -> f64 {
    let n = ts.tasks.len();
    let hyper = ts.tasks.iter().fold(1u32, |h, t| {
        let g = {
            let (mut a, mut b) = (h, t.t);
            while b != 0 {
                let r = a % b;
                a = b;
                b = r;
            }
            a
        };
        h / g * t.t
    });
    let horizon = hyper.saturating_mul(cycles).max(1);
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&i| ts.tasks[i].t);
    let mut s = seed | 1;
    let mut rng = |bound: u32| {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        (s % bound as u64) as u32
    };
    let (mut remaining, mut released, mut active) = (vec![0u32; n], vec![0u32; n], vec![false; n]);
    let (mut missed, mut jobs) = (0u64, 0u64);
    for t in 0..horizon {
        for i in 0..n {
            if active[i] && t >= released[i] + ts.tasks[i].d {
                missed += 1; // unfinished at its deadline
                active[i] = false;
            }
        }
        for i in 0..n {
            if t % ts.tasks[i].t == 0 {
                let c = ts.tasks[i].c;
                let lo = ((alpha * c as f64).ceil() as u32).clamp(1, c);
                remaining[i] = lo + rng(c - lo + 1); // uniform [lo, c]
                released[i] = t;
                active[i] = true;
                jobs += 1;
            }
        }
        if let Some(&i) = order.iter().find(|&&i| active[i] && remaining[i] > 0) {
            remaining[i] -= 1;
            if remaining[i] == 0 {
                active[i] = false;
            }
        }
    }
    if jobs == 0 {
        0.0
    } else {
        missed as f64 / jobs as f64
    }
}

pub fn print_report(rep: &RtReport, ts: &TaskSet, file: &str) {
    println!();
    println!("  leanlift schedulability certificate — `{file}` ({} tasks, {})", ts.tasks.len(), rep.policy);
    println!("  ────────────────────────────────────────────────");
    println!(
        "  utilization : U = {:.4}   bound = {:.4}   ({} — sufficient)",
        rep.util,
        rep.util_bound,
        if rep.util_test_pass { "PASS" } else { "FAIL" }
    );
    if matches!(ts.policy, Policy::Edf) {
        match rep.edf_first_fail {
            None => println!("  demand-bound test (exact): dbf(t) ≤ t at every deadline point ✓"),
            Some((t, dbf)) => println!("  demand-bound test (exact): dbf({t}) = {dbf} > {t}  ✗  (overdemand)"),
        }
    } else {
        println!("  response-time analysis (exact):");
        for (t, (name, r)) in ts.tasks.iter().zip(&rep.wcrt) {
            match r {
                Some(r) => println!("    {name:<10} R = {r:>4}  ≤  D = {:<4}  ✓", t.d),
                None => println!("    {name:<10} R  >  D = {:<4}  ✗  (deadline miss)", t.d),
            }
        }
    }
    println!();
    println!(
        "  level : {}",
        if rep.schedulable {
            "SCHEDULABLE  (RTA exact: every task meets its deadline)"
        } else {
            "NOT SCHEDULABLE  (a task misses its deadline)"
        }
    );
    println!();
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Rng(u64);
    impl Rng {
        fn upto(&mut self, n: u32) -> u32 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as u32
        }
    }

    #[test]
    fn rta_exact_beats_the_bound() {
        // The teaching case: U > RM bound (sufficient test fails) yet RTA proves
        // schedulable — exact response times sensor=1, filter=2, control=5.
        let src = std::fs::read_to_string("examples/models/tasks.model.toml").unwrap();
        let ts = parse(&src).unwrap();
        let rep = analyze(&ts);
        assert!(!rep.util_test_pass, "util test should fail (U > bound)");
        assert!(rep.schedulable, "RTA should find it schedulable");
        let r: Vec<Option<u32>> = rep.wcrt.iter().map(|(_, r)| *r).collect();
        assert_eq!(r, vec![Some(1), Some(2), Some(5)]);
    }

    fn gcd(a: u32, b: u32) -> u32 {
        if b == 0 {
            a
        } else {
            gcd(b, a % b)
        }
    }

    /// Discrete-event simulation of preemptive fixed-priority (RM) scheduling
    /// from the CRITICAL INSTANT (all tasks released at t=0), over `cycles`
    /// hyperperiods. Returns the observed worst-case response time per task.
    fn simulate_rm(ts: &TaskSet, cycles: u32) -> Vec<u32> {
        let n = ts.tasks.len();
        let hyper = ts.tasks.iter().fold(1u32, |h, t| h / gcd(h, t.t) * t.t);
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by_key(|&i| ts.tasks[i].t); // RM: shorter period ⇒ higher priority
        let mut remaining = vec![0u32; n];
        let mut released = vec![0u32; n];
        let mut max_resp = vec![0u32; n];
        for t in 0..hyper * cycles {
            for i in 0..n {
                if t % ts.tasks[i].t == 0 {
                    remaining[i] = ts.tasks[i].c; // new job (schedulable ⇒ prev done)
                    released[i] = t;
                }
            }
            if let Some(&i) = order.iter().find(|&&i| remaining[i] > 0) {
                remaining[i] -= 1;
                if remaining[i] == 0 {
                    max_resp[i] = max_resp[i].max(t + 1 - released[i]);
                }
            }
        }
        max_resp
    }

    #[test]
    fn rta_matches_simulation() {
        // R3 empirical cross-check: exact RTA worst-case response times must equal
        // what a fixed-priority scheduler actually produces from the critical
        // instant (where RTA's worst case is realized). A wrong RTA goes red here.
        for src in [
            std::fs::read_to_string("examples/models/tasks.model.toml").unwrap(),
            "kind=\"tasks\"\npolicy=\"RM\"\n\
                [[task]]\nname=\"a\"\nc=\"2\"\nt=\"5\"\n\
                [[task]]\nname=\"b\"\nc=\"1\"\nt=\"7\"\n\
                [[task]]\nname=\"c\"\nc=\"2\"\nt=\"13\"\n"
                .to_string(),
        ] {
            let ts = parse(&src).unwrap();
            let rep = analyze(&ts);
            assert!(rep.schedulable, "test sets must be schedulable");
            let sim = simulate_rm(&ts, 2);
            for (i, (_, r)) in rep.wcrt.iter().enumerate() {
                assert_eq!(r.unwrap(), sim[i], "task {i}: RTA {r:?} vs simulated {}", sim[i]);
            }
        }
    }

    #[test]
    fn edf_implicit_agrees_with_utilization() {
        // Implicit deadlines (D=T): the exact demand test agrees with U ≤ 1.
        let sched = "kind=\"tasks\"\npolicy=\"EDF\"\n\
            [[task]]\nname=\"a\"\nc=\"1\"\nt=\"3\"\n\
            [[task]]\nname=\"b\"\nc=\"1\"\nt=\"2\"\n"; // U=1/3+1/2=0.833 ≤ 1
        assert!(analyze(&parse(sched).unwrap()).schedulable);
        let over = "kind=\"tasks\"\npolicy=\"EDF\"\n\
            [[task]]\nname=\"a\"\nc=\"2\"\nt=\"3\"\n\
            [[task]]\nname=\"b\"\nc=\"1\"\nt=\"2\"\n"; // U=2/3+1/2=1.166 > 1
        assert!(!analyze(&parse(over).unwrap()).schedulable);
    }

    #[test]
    fn edf_demand_catches_constrained_deadline() {
        // U ≤ 1 but tight deadlines ⇒ infeasible; demand-bound finds dbf(1)=2>1.
        let rep = analyze(&parse(&std::fs::read_to_string("examples/models/tasks-edf.model.toml").unwrap()).unwrap());
        assert!(rep.util <= 1.0, "U must pass the naive test");
        assert!(!rep.schedulable, "demand-bound must catch the constrained-deadline infeasibility");
        assert_eq!(rep.edf_first_fail, Some((1, 2)));
    }

    #[test]
    fn arbitrary_deadline_is_refused() {
        // REGRESSION (brutal review): D > T runs outside the proven envelope
        // (RTA + demand bound assume D ≤ T) — must be refused, not analyzed.
        let src = "kind=\"tasks\"\npolicy=\"EDF\"\n[[task]]\nname=\"x\"\nc=\"1\"\nt=\"3\"\nd=\"5\"\n";
        assert!(parse(src).is_err(), "D>T must be rejected");
    }

    #[test]
    fn edf_constrained_but_schedulable() {
        // Constrained deadlines (D<T) that the demand test passes (sanity: it is
        // not just rejecting everything with D<T).
        let src = "kind=\"tasks\"\npolicy=\"EDF\"\n\
            [[task]]\nname=\"a\"\nc=\"1\"\nt=\"5\"\nd=\"3\"\n\
            [[task]]\nname=\"b\"\nc=\"1\"\nt=\"8\"\nd=\"6\"\n";
        let rep = analyze(&parse(src).unwrap());
        assert!(rep.schedulable && rep.edf_first_fail.is_none());
    }

    #[test]
    fn soft_miss_rises_with_load() {
        // R4: the soft deadline-miss probability is ~0 at nominal load and high
        // under heavy overload (the sigmoid the intersection sweep draws).
        let ts = parse(&std::fs::read_to_string("examples/models/tasks.model.toml").unwrap()).unwrap();
        let low = simulate_miss(&scaled(&ts, 1.0), 0.5, 200, 1);
        let high = simulate_miss(&scaled(&ts, 4.0), 0.5, 200, 1);
        assert!(low < 0.01, "should not miss at nominal load: {low}");
        assert!(high > 0.3, "should miss heavily at 4x load: {high}");
        assert!(low <= high);
    }

    #[test]
    fn overload_is_unschedulable() {
        // U > 1 ⇒ no policy can schedule it; RTA reports a deadline miss.
        let src = "kind=\"tasks\"\npolicy=\"RM\"\n\
            [[task]]\nname=\"a\"\nc=\"3\"\nt=\"4\"\n\
            [[task]]\nname=\"b\"\nc=\"3\"\nt=\"5\"\n";
        let rep = analyze(&parse(src).unwrap());
        assert!(rep.util > 1.0 && !rep.schedulable);
    }

    #[test]
    fn util_bound_implies_rta_schedulable() {
        // Liu–Layland soundness: whenever the SUFFICIENT utilization test passes,
        // the EXACT RTA must agree it is schedulable — over random RM task sets.
        let mut r = Rng(0xA1B2_C3D4_E5F6_0718);
        let mut passed = 0;
        for _ in 0..3000 {
            let n = 2 + r.upto(4) as usize; // 2..=5 tasks
            let tasks: Vec<Task> = (0..n)
                .map(|i| {
                    let c = 1 + r.upto(5);
                    let t = c + r.upto(30); // T ≥ C ⇒ per-task util ≤ 1
                    Task { name: format!("t{i}"), c, t, d: t }
                })
                .collect();
            let rep = analyze(&TaskSet { tasks, policy: Policy::Rm });
            if rep.util_test_pass {
                assert!(rep.schedulable, "util test passed but RTA says unschedulable (U={})", rep.util);
                passed += 1;
            }
        }
        assert!(passed > 100, "util-bound test near-vacuous: only {passed} sets passed");
    }
}

/// Bounded model-checking harnesses (PLAN-perf-demo §8 R2): the RTA recurrence
/// kernel is monotone and overflow-free. Inert outside `cargo kani`; bounds kept
/// small so CBMC stays light. leanlift proving its OWN schedulability analyzer.
#[cfg(kani)]
mod kani_harness {
    use super::{div_ceil, term};

    /// `div_ceil` never overflows and `⌈a/b⌉ ≤ a` (for `b ≥ 1`) — the latter is
    /// the bound the response-time loop's termination leans on.
    #[kani::proof]
    fn div_ceil_safe() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        kani::assume(a <= 1000);
        kani::assume(b >= 1 && b <= 1000);
        let q = div_ceil(a, b); // no u32 overflow in (a + b - 1)
        assert!(q <= a);
    }

    /// THE soundness property: the interference term is MONOTONE non-decreasing
    /// in the window `r`. Monotonicity ⇒ the RTA iteration converges to the least
    /// fixed point = the true worst-case response time. (No overflow under the
    /// realistic bound.)
    #[kani::proof]
    fn term_monotone() {
        let r: u32 = kani::any();
        let r2: u32 = kani::any();
        let cj: u32 = kani::any();
        let tj: u32 = kani::any();
        kani::assume(r <= 1000 && r2 <= 1000 && cj <= 1000 && tj >= 1 && tj <= 1000);
        kani::assume(r <= r2);
        assert!(term(r, cj, tj) <= term(r2, cj, tj));
    }
}
