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
        tasks.push(Task { name, c, t: period, d });
    }
    if tasks.is_empty() {
        return Err("task set has no `[[task]]` entries".into());
    }
    Ok(TaskSet { tasks, policy })
}

/// `⌈a / b⌉` for positive `b`.
fn div_ceil(a: u32, b: u32) -> u32 {
    (a + b - 1) / b
}

/// Exact worst-case response time by the RTA fixed point. Returns `None` if it
/// provably exceeds the deadline `d` (so the task is unschedulable). The
/// iteration is monotone increasing and bounded by `d`, hence terminates.
fn response_time(c: u32, d: u32, hp: &[(u32, u32)]) -> Option<u32> {
    let mut r = c;
    loop {
        let interference: u32 = hp.iter().map(|&(cj, tj)| div_ceil(r, tj) * cj).sum();
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

    let (wcrt, schedulable) = match ts.policy {
        // EDF with implicit deadlines: U ≤ 1 is exact (necessary & sufficient).
        Policy::Edf => (
            ts.tasks.iter().map(|t| (t.name.clone(), None)).collect(),
            util <= 1.0 + 1e-12,
        ),
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

    RtReport { policy, util, util_bound, util_test_pass, wcrt, schedulable }
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
    if !matches!(ts.policy, Policy::Edf) {
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
