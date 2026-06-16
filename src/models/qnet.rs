//! Open queueing-network analysis (PLAN-qnet-rta §Q) — the multi-station
//! generalization of the single-server `link`. An OPEN JACKSON NETWORK: stations
//! with exponential service and probabilistic routing, Poisson external arrivals.
//! Product-form, so it solves EXACTLY and cheaply (no state space):
//!
//!   traffic equations   λᵢ = λ⁰ᵢ + Σⱼ λⱼ·pⱼᵢ      ⇒  (I − Pᵀ) λ = λ⁰
//!   utilization         ρᵢ = λᵢ / (cᵢ·μᵢ)
//!   M/M/1 per station   Lᵢ = ρᵢ/(1−ρᵢ),  Wᵢ = 1/(μᵢ − λᵢ)
//!   network             L = Σ Lᵢ,  W = L / Σ λ⁰ᵢ     (Little)
//!   stable iff max ρᵢ < 1;  bottleneck = argmax ρᵢ.
//!
//! As external load scales, the bottleneck's ρ → 1 and its queue diverges — the
//! same phase transition as `link`, now located at a network bottleneck.

use super::toml;

pub struct Station {
    pub name: String,
    pub mu: f64,      // service rate per server
    pub servers: u32, // c (default 1)
    pub lambda0: f64, // external arrival rate (default 0)
}

pub struct QNet {
    pub stations: Vec<Station>,
    /// routing[i][j] = P(a job leaving station i goes next to station j). Each
    /// row sums to ≤ 1; the remainder leaves the network.
    pub routing: Vec<Vec<f64>>,
}

pub struct StationResult {
    pub name: String,
    pub lambda: f64, // throughput (solved arrival rate)
    pub rho: f64,    // utilization
    pub l: f64,      // mean number in station (NaN if ρ ≥ 1)
    pub w: f64,      // mean sojourn time   (NaN if ρ ≥ 1)
}

pub struct QNetReport {
    pub stations: Vec<StationResult>,
    pub stable: bool,
    pub bottleneck: usize, // index of max-ρ station
    pub l_total: f64,
    pub w_total: f64,
    pub throughput: f64, // Σ λ⁰ (= network departure rate in steady state)
}

fn field_f64(t: &std::collections::HashMap<String, toml::Value>, key: &str) -> Result<f64, String> {
    t.get(key)
        .ok_or_else(|| format!("station: missing `{key}`"))?
        .as_str(key)?
        .parse()
        .map_err(|_| format!("station: `{key}` must be a number"))
}

pub fn parse(src: &str) -> Result<QNet, String> {
    let doc = toml::parse(src)?;
    let mut stations = Vec::new();
    for (i, s) in doc.table("station").iter().enumerate() {
        let name = match s.get("name") {
            Some(v) => v.as_str("name")?.to_string(),
            None => format!("s{i}"),
        };
        let mu = field_f64(s, "mu")?;
        if mu <= 0.0 {
            return Err(format!("station `{name}`: `mu` must be positive"));
        }
        let servers = match s.get("servers") {
            Some(v) => v.as_str("servers")?.parse().map_err(|_| format!("station `{name}`: bad `servers`"))?,
            None => 1u32,
        };
        // M/M/c (Erlang-C) is a future extension; only single-server stations are
        // computed exactly today. Refuse >1 rather than emit silently-wrong L/W.
        if servers != 1 {
            return Err(format!(
                "station `{name}`: only single-server stations (servers=1) are supported; M/M/c (Erlang-C) is a future extension"
            ));
        }
        let lambda0 = match s.get("lambda") {
            Some(v) => {
                let x: f64 = v.as_str("lambda")?.parse().map_err(|_| format!("station `{name}`: bad `lambda`"))?;
                if x < 0.0 {
                    return Err(format!("station `{name}`: `lambda` must be ≥ 0"));
                }
                x
            }
            None => 0.0,
        };
        stations.push(Station { name, mu, servers, lambda0 });
    }
    if stations.is_empty() {
        return Err("queueing network has no `[[station]]` entries".into());
    }
    let index = |n: &str| stations.iter().position(|s| s.name == n);

    let n = stations.len();
    let mut routing = vec![vec![0.0; n]; n];
    for (i, r) in doc.table("route").iter().enumerate() {
        let from = r.get("from").ok_or_else(|| format!("route {i}: missing `from`"))?.as_str("from")?;
        let to = r.get("to").ok_or_else(|| format!("route {i}: missing `to`"))?.as_str("to")?;
        let prob: f64 = r.get("prob").ok_or_else(|| format!("route {i}: missing `prob`"))?.as_str("prob")?
            .parse().map_err(|_| format!("route {i}: `prob` must be a number"))?;
        if !(0.0..=1.0).contains(&prob) {
            return Err(format!("route {i}: `prob` must be in [0,1]"));
        }
        let fi = index(from).ok_or_else(|| format!("route {i}: station `{from}` not declared"))?;
        let ti = index(to).ok_or_else(|| format!("route {i}: station `{to}` not declared"))?;
        routing[fi][ti] += prob;
    }
    // Each row's out-probability must not exceed 1 (the remainder exits).
    for (i, row) in routing.iter().enumerate() {
        let out: f64 = row.iter().sum();
        if out > 1.0 + 1e-9 {
            return Err(format!("station `{}`: routing probabilities sum to {out} > 1", stations[i].name));
        }
    }
    if stations.iter().map(|s| s.lambda0).sum::<f64>() <= 0.0 {
        return Err("open network needs a positive external arrival (`lambda`) somewhere".into());
    }
    Ok(QNet { stations, routing })
}

/// Scale every external arrival rate by `s` (the load knob for the bottleneck
/// sweep, PLAN-qnet-rta §Q5). ρ is linear in λ⁰, so `max ρ` scales with `s` and
/// the network goes unstable at `s* = 1 / max ρ(1)`.
pub fn scaled(net: &QNet, s: f64) -> QNet {
    QNet {
        stations: net
            .stations
            .iter()
            .map(|st| Station { name: st.name.clone(), mu: st.mu, servers: st.servers, lambda0: st.lambda0 * s })
            .collect(),
        routing: net.routing.clone(),
    }
}

/// Solve `A x = b` by Gaussian elimination with partial pivoting (small, dense).
/// Returns `None` if `A` is (numerically) SINGULAR — for `(I − Pᵀ)` that means
/// the routing traps jobs (a closed sub-network with no exit), so the open-network
/// traffic equations have no well-posed solution. Never returns silent garbage.
fn solve(mut a: Vec<Vec<f64>>, mut b: Vec<f64>) -> Option<Vec<f64>> {
    let n = b.len();
    for col in 0..n {
        let piv = (col..n).max_by(|&i, &j| a[i][col].abs().partial_cmp(&a[j][col].abs()).unwrap()).unwrap();
        a.swap(col, piv);
        b.swap(col, piv);
        let d = a[col][col];
        if d.abs() < 1e-12 {
            return None; // singular ⇒ not a well-posed open network
        }
        for row in (col + 1)..n {
            let f = a[row][col] / d;
            if f != 0.0 {
                for k in col..n {
                    a[row][k] -= f * a[col][k];
                }
                b[row] -= f * b[col];
            }
        }
    }
    let mut x = vec![0.0; n];
    for i in (0..n).rev() {
        let mut s = b[i];
        for k in (i + 1)..n {
            s -= a[i][k] * x[k];
        }
        x[i] = s / a[i][i]; // pivot magnitude ≥ 1e-12 guaranteed above
    }
    Some(x)
}

pub fn analyze(net: &QNet) -> Result<QNetReport, String> {
    let n = net.stations.len();
    // (I − Pᵀ) λ = λ⁰.
    let mut a = vec![vec![0.0; n]; n];
    for i in 0..n {
        for j in 0..n {
            a[i][j] = if i == j { 1.0 } else { 0.0 } - net.routing[j][i]; // Pᵀ[i][j] = routing[j][i]
        }
    }
    let lambda0: Vec<f64> = net.stations.iter().map(|s| s.lambda0).collect();
    let lambda = solve(a, lambda0.clone()).ok_or_else(|| {
        "network is not open: the routing traps jobs (the traffic equations are singular) — every station needs a path that eventually exits".to_string()
    })?;
    // Physical sanity: solved arrival rates must be finite and non-negative.
    // A negative/NaN λ means an ill-posed (non-open) network, not a verdict.
    for (i, &li) in lambda.iter().enumerate() {
        if !li.is_finite() || li < -1e-9 {
            return Err(format!(
                "network ill-posed: station `{}` has non-physical solved arrival rate {li:.4} (check routing / openness)",
                net.stations[i].name
            ));
        }
    }

    let mut stations = Vec::with_capacity(n);
    let mut stable = true;
    let mut bottleneck = 0;
    let mut max_rho = f64::NEG_INFINITY;
    let mut l_total = 0.0;
    for (i, s) in net.stations.iter().enumerate() {
        let rho = lambda[i] / (s.servers as f64 * s.mu); // servers == 1 (enforced in parse)
        if rho > max_rho {
            max_rho = rho;
            bottleneck = i;
        }
        // M/M/1 metrics; ρ ≥ 1 ⇒ unstable ⇒ L/W undefined (NaN).
        let (l, w) = if rho < 1.0 {
            let l = rho / (1.0 - rho);
            let w = if lambda[i] > 0.0 { l / lambda[i] } else { 0.0 }; // idle station: W = 0
            (l, w)
        } else {
            stable = false;
            (f64::NAN, f64::NAN)
        };
        l_total += l; // finite when stable; if any station is unstable we don't report L/W
        stations.push(StationResult { name: s.name.clone(), lambda: lambda[i], rho, l, w });
    }
    let throughput: f64 = lambda0.iter().sum();
    let (l_total, w_total) = if stable {
        (l_total, l_total / throughput)
    } else {
        (f64::NAN, f64::NAN) // a saturated station makes network totals meaningless
    };
    Ok(QNetReport { stations, stable, bottleneck, l_total, w_total, throughput })
}

/// Discrete-event (SSA) simulation of the open network: external Poisson
/// arrivals (rate λ⁰ᵢ), exponential service (rate μᵢ when busy), probabilistic
/// routing on completion. Returns the time-average number in each station — the
/// EMPIRICAL cross-check of the product-form `Lᵢ` (PLAN-qnet-rta §Q4). Requires
/// a stable network (else the queue grows without bound).
pub fn simulate(net: &QNet, horizon: f64, seed: u64) -> Vec<f64> {
    let n = net.stations.len();
    let mu: Vec<f64> = net.stations.iter().map(|s| s.mu).collect();
    let lam0: Vec<f64> = net.stations.iter().map(|s| s.lambda0).collect();
    let mut s = seed | 1;
    let mut u = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        ((s >> 11) as f64 / (1u64 << 53) as f64).max(1e-15) // (0,1]
    };
    let mut q = vec![0u64; n]; // queue length per station
    let mut area = vec![0.0f64; n]; // ∫ q dt
    let mut t = 0.0;
    while t < horizon {
        // total event rate: all external arrivals + service at busy stations.
        let mut rate = 0.0;
        for i in 0..n {
            rate += lam0[i];
            if q[i] > 0 {
                rate += mu[i];
            }
        }
        if rate <= 0.0 {
            break;
        }
        let dt = -(u().ln()) / rate;
        for i in 0..n {
            area[i] += q[i] as f64 * dt;
        }
        t += dt;
        // pick the event proportional to its rate.
        let mut x = u() * rate;
        let mut fired = None;
        'pick: for i in 0..n {
            if x < lam0[i] {
                q[i] += 1; // external arrival
                fired = Some(());
                break 'pick;
            }
            x -= lam0[i];
            if q[i] > 0 {
                if x < mu[i] {
                    // service completion at i: depart, then route.
                    q[i] -= 1;
                    let mut y = u();
                    for j in 0..n {
                        let p = net.routing[i][j];
                        if y < p {
                            q[j] += 1;
                            break;
                        }
                        y -= p;
                    }
                    fired = Some(());
                    break 'pick;
                }
                x -= mu[i];
            }
        }
        let _ = fired;
    }
    area.iter().map(|a| a / t).collect()
}

pub fn print_report(rep: &QNetReport, file: &str) {
    println!();
    println!("  leanlift queueing-network certificate — `{file}` ({} stations)", rep.stations.len());
    println!("  ────────────────────────────────────────────────");
    println!("  {:<12} {:>10} {:>8} {:>10} {:>10}", "station", "λ", "ρ", "L", "W");
    for (i, s) in rep.stations.iter().enumerate() {
        let mark = if i == rep.bottleneck { " ◀ bottleneck" } else { "" };
        println!("  {:<12} {:>10.4} {:>8.4} {:>10.4} {:>10.4}{mark}", s.name, s.lambda, s.rho, s.l, s.w);
    }
    println!();
    if rep.stable {
        println!("  network L = {:.4}   W = {:.4}   throughput = {:.4}", rep.l_total, rep.w_total, rep.throughput);
        println!("  level : STABLE  (every station ρ < 1)");
    } else {
        println!("  level : UNSTABLE  (bottleneck `{}` saturated, ρ ≥ 1)", rep.stations[rep.bottleneck].name);
    }
    println!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_mm1_closed_form() {
        let rep = analyze(&parse("kind=\"qnet\"\n[[station]]\nname=\"s\"\nmu=\"10.0\"\nlambda=\"4.0\"\n").unwrap()).unwrap();
        let s = &rep.stations[0];
        assert!((s.lambda - 4.0).abs() < 1e-9);
        assert!((s.rho - 0.4).abs() < 1e-9);
        assert!((s.l - 0.4 / 0.6).abs() < 1e-9); // ρ/(1-ρ)
        assert!((s.w - 1.0 / (10.0 - 4.0)).abs() < 1e-9); // 1/(μ-λ)
        assert!(rep.stable && rep.bottleneck == 0);
    }

    #[test]
    fn tandem_traffic_equations() {
        // a → b, all of a's output flows to b; both see the external rate.
        let src = "kind=\"qnet\"\n\
            [[station]]\nname=\"a\"\nmu=\"5\"\nlambda=\"2\"\n\
            [[station]]\nname=\"b\"\nmu=\"5\"\n\
            [[route]]\nfrom=\"a\"\nto=\"b\"\nprob=\"1.0\"\n";
        let rep = analyze(&parse(src).unwrap()).unwrap();
        assert!((rep.stations[0].lambda - 2.0).abs() < 1e-9);
        assert!((rep.stations[1].lambda - 2.0).abs() < 1e-9);
    }

    #[test]
    fn feedback_loop_matches_hand_solution() {
        // The example: worker λ = 2/(1-0.3) = 2.857…; worker is the bottleneck.
        let rep = analyze(&parse(&std::fs::read_to_string("examples/models/qnet.model.toml").unwrap()).unwrap()).unwrap();
        let w = rep.stations.iter().find(|s| s.name == "worker").unwrap();
        assert!((w.lambda - 2.0 / 0.7).abs() < 1e-6, "worker λ = {}", w.lambda);
        assert!((w.rho - (2.0 / 0.7) / 4.0).abs() < 1e-6);
        assert_eq!(rep.bottleneck, 1, "worker is the bottleneck");
        // network Little's law: W = L / throughput.
        assert!((rep.w_total - rep.l_total / rep.throughput).abs() < 1e-9);
        // flow balance: external in == throughput (steady-state departures).
        assert!((rep.throughput - 2.0).abs() < 1e-9);
    }

    #[test]
    fn overload_is_unstable() {
        let rep = analyze(&parse("kind=\"qnet\"\n[[station]]\nname=\"s\"\nmu=\"3.0\"\nlambda=\"5.0\"\n").unwrap()).unwrap();
        assert!(!rep.stable, "ρ>1 must be unstable");
        assert!(rep.stations[0].rho > 1.0);
        assert!(rep.stations[0].l.is_nan(), "unstable station L is undefined");
    }

    #[test]
    fn bottleneck_diverges_with_load() {
        // The phase transition: as external load scales, the bottleneck ρ → 1 and
        // its queue L → ∞; the network goes unstable past λ* (here worker first).
        let base = "kind=\"qnet\"\n[[station]]\nname=\"s\"\nmu=\"4.0\"\nlambda=\"{L}\"\n";
        let l_at = |lam: f64| {
            let rep = analyze(&parse(&base.replace("{L}", &lam.to_string())).unwrap()).unwrap();
            (rep.stable, rep.stations[0].l)
        };
        let (s_lo, l_lo) = l_at(1.0); // ρ=0.25
        let (s_hi, _) = l_at(4.5); // ρ>1
        assert!(s_lo && l_lo < 1.0);
        assert!(!s_hi); // unstable past μ
        // monotone growth toward the boundary
        assert!(l_at(3.6).1 > l_at(2.0).1);
    }

    #[test]
    fn simulation_matches_analytic() {
        // Q4 empirical cross-check: SSA simulation of the open network must match
        // the product-form per-station L (Monte-Carlo tolerance).
        let net = parse(&std::fs::read_to_string("examples/models/qnet.model.toml").unwrap()).unwrap();
        let rep = analyze(&net).unwrap();
        let sim = simulate(&net, 300_000.0, 7);
        for (i, s) in rep.stations.iter().enumerate() {
            let tol = (0.12 * s.l).max(0.08);
            assert!((sim[i] - s.l).abs() <= tol, "{}: analytic L={:.4} vs sim {:.4}", s.name, s.l, sim[i]);
        }
    }

    #[test]
    fn trapped_cycle_is_rejected_not_falsely_stable() {
        // REGRESSION (brutal review CRITICAL #1): a closed cycle (a⇄b, each row
        // sums to 1) traps jobs ⇒ (I−Pᵀ) singular. Must ERROR, never report a
        // bogus STABLE verdict.
        let src = "kind=\"qnet\"\n\
            [[station]]\nname=\"a\"\nmu=\"10\"\nlambda=\"2\"\n\
            [[station]]\nname=\"b\"\nmu=\"10\"\n\
            [[route]]\nfrom=\"a\"\nto=\"b\"\nprob=\"1.0\"\n\
            [[route]]\nfrom=\"b\"\nto=\"a\"\nprob=\"1.0\"\n";
        assert!(analyze(&parse(src).unwrap()).is_err(), "trapped network must be rejected");
    }

    #[test]
    fn multiserver_is_refused_not_silently_wrong() {
        // REGRESSION (brutal review CRITICAL #2): M/M/c (servers>1) is not yet
        // computed — must be refused at parse, never emit L=W=0 for a busy station.
        let src = "kind=\"qnet\"\n[[station]]\nname=\"s\"\nmu=\"3.0\"\nservers=\"2\"\nlambda=\"5.0\"\n";
        assert!(parse(src).is_err(), "servers>1 must be refused");
    }

    #[test]
    fn idle_station_has_zero_wait_not_nan() {
        // REGRESSION (brutal review MEDIUM #3): a stable station with λ=0 has W=0,
        // not NaN. `sink` receives nothing (source routes all to exit).
        let src = "kind=\"qnet\"\n\
            [[station]]\nname=\"src\"\nmu=\"5\"\nlambda=\"2\"\n\
            [[station]]\nname=\"sink\"\nmu=\"5\"\n";
        let rep = analyze(&parse(src).unwrap()).unwrap();
        let sink = rep.stations.iter().find(|s| s.name == "sink").unwrap();
        assert_eq!(sink.lambda, 0.0);
        assert!(sink.w == 0.0 && sink.l == 0.0, "idle station: L=W=0, got W={}", sink.w);
        assert!(rep.stable);
    }
}
