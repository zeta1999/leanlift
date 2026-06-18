# PLAN — optimizer convergence: ℝ → f64 under conditions

> Today the float optimizers (`opt-gd`, `opt-hj`, `opt-gss`) get **L1 bit-exact
> differential testing + a runtime-checked descent postcondition** — no *proof* of
> anything. This plan adds the real thing for **`opt-gd`** (fixed-step gradient
> descent): an **L3 convergence theorem** that lifts the textbook ℝ result to the
> actual f64 implementation under explicit conditions, plus an **independent
> certified-interval corroboration** over a bounded input box.
>
> Two tracks, chosen deliberately to cross-check each other:
> - **Track 1 (analytic, A→B):** prove convergence in exact ℝ, then transport it
>   to f64 through a trusted IEEE rounding model. The literal answer to "prove
>   convergence for floats, assuming specific conditions."
> *(The proofs live in the isolated lake project `leanproofs/` — Mathlib-pinned,
> separate from the Mathlib-free runtime `lean/`.)*
>
> - **Track 3 (computational, D):** certify `f(best) ≤ f₀` over a bounded box by
>   verified interval arithmetic with directed rounding — no analytic limit, but
>   a machine-checked enclosure that must agree with Track 1.
>
> **Quality bar (unchanged): bugs are not an option.** Every step ends with BOTH
> `./ci.sh` GREEN AND a **brutally-honest review subagent** over the diff —
> *especially* over the **axiom surface**: the trusted base must be minimal,
> standard (Higham §2), and explicitly enumerated, with zero hidden assumptions.
> Cross-check every bound against the closed form, the analysis, AND the existing
> L1 simulation (the 190 conformant vectors already compute `f_K` numerically).

## Why `opt-gd` is the ideal first target

`f(x,y) = (x−1)² + (y−2)²`, `∇f = (2(x−1), 2(y−2))`, step `p ← p − η∇f`, 200
iterations, return `f(x₂₀₀, y₂₀₀)` (see `examples/opt/{gd.cpp,Gd.lean}` — op-for-op
mirrors, already L1-conformant on 190 vectors).

Change coordinates `u_k = x_k − 1`, `v_k = y_k − 2`. The iteration **decouples and
linearizes exactly**:

```
u_{k+1} = x_{k+1} − 1 = (x_k − η·2(x_k−1)) − 1 = (1 − 2η)·u_k
v_{k+1} = (1 − 2η)·v_k
```

so with `ρ := 1 − 2η`:

```
u_k = ρ^k·u₀,   v_k = ρ^k·v₀,   f(x_K,y_K) = ρ^{2K}·f(x₀,y₀)      (★ closed form)
```

This is the cleanest convergence object possible: a pure geometric contraction with
ratio `ρ`. The structural constants are `μ = L = 2` (the Hessian is `2I`), the
textbook safe step is `η ≤ 1/L = ½`, and the **exact** contraction condition is
`|ρ| < 1 ⇔ η ∈ (0,1)` — which is *precisely* the `η ≤ 1` guard the current
`postcondition` already encodes (`src/compare.rs`, `Profile::OptGd`). At `η = 1`,
`ρ = −1`: `f_K = f₀` (marginal, oscillating, never diverges); for `η > 1`,
`|ρ| > 1`, diverges → postcondition returns `None`. The plan makes that guard a
*theorem*, not a comment.

---

## Track 1 — analytic ℝ → f64

### Phase A — exact-ℝ convergence (the reference)  ★

Model gd over `ℝ` and prove (★ closed form) and its consequences:

- **A1 (closed form):** `f_real K x₀ y₀ η = ρ^(2K) · f_real 0 x₀ y₀ η`, `ρ = 1−2η`.
  Proof: induction on `K`, one `ring` step per layer (the per-step identity
  `u_{k+1} = ρ·u_k` is polynomial).
- **A2 (descent):** `η ∈ (0,1] → f_real K ≤ f_real 0` (`ρ² ≤ 1`).
- **A3 (convergence):** `η ∈ (0,1) → Tendsto (fun K => f_real K) atTop (𝓝 0)`
  (`|ρ| < 1 ⇒ ρ^{2K} → 0`, Mathlib `tendsto_pow_atTop_nhds_zero_of_lt_one`).

Deliverable: `lean-proofs/Convergence/GdReal.lean`, sorry-free. **A3 needs Mathlib**
(ℝ, limits, `ring`/`nlinarith`) — so the proofs live in a **separate lake project**
`lean-proofs/` with a Mathlib dependency, *not* in the Mathlib-free runtime `lean/`
(which must stay fast for `lean --run`). **Reuse check:** the Aeneas backend
(`backends/lean`) already pins Mathlib; if its `.olean` cache is usable we ride it
and avoid a fresh ~45-min Mathlib build (Phase 0).

### Phase B — transport to f64 through a rounding model  ★ (axiom-gated)

Introduce the **standard IEEE-754 model** (Higham, *Accuracy and Stability*, §2.2)
as **explicitly trusted axioms** in `lean-proofs/Convergence/FloatModel.lean`:

```
-- u = 2⁻⁵³ (f64 unit roundoff), η_sub = 2⁻¹⁰⁷⁴ (subnormal abs floor)
axiom round_mul (a b : ℝ) : ∃ δ ε, |δ| ≤ u ∧ |ε| ≤ η_sub ∧ fl(a*b) = (a*b)(1+δ)+ε
axiom round_sub (a b : ℝ) : ∃ δ,   |δ| ≤ u ∧                fl(a−b) = (a−b)(1+δ)
-- (subtraction of representables near each other is exact / no subnormal term
--  under our bounded-operand precondition; stated conservatively)
```

These map Lean's opaque `Float` ops to perturbed-ℝ ops. **They are the trusted base
— the review gate's primary scrutiny target.** They are not derived here (Track C /
FloatSpec-Flean would derive them; out of scope), but they are *standard, auditable,
and not LLM-produced*, so they don't touch the no-LLM invariant.

Then prove, under the **conditions** `η ∈ [η_lo, η_hi] ⊂ (0,1)` and
**bounded operands** (no overflow; inputs in a stated box):

- **B1 (per-step perturbation):** each f64 step satisfies
  `u_{k+1}^fl = ρ·u_k^fl·(1+θ_k) + (abs term)`, `|θ_k| ≤ c·u` with `c` a small
  explicit constant counting the ops on the critical path (`x−1`, `2·`, `η·`, `x−`
  ⇒ c ≈ 4).
- **B2 (forward-error / contraction):** `|ρ|(1+cu) < 1` (true for `η` bounded off
  `0,1`) ⇒ `|u_K^fl| ≤ |u₀|·(|ρ|(1+cu))^K + O(η_sub/(1−|ρ|))`.
- **B3 (the headline theorem):** for `η ∈ [η_lo,η_hi]`,
  `f_K^fl ≤ ρ^{2K}·f₀·(1+cu)^{2K} + Φ`  with `Φ = O(K·η_sub)` the rounding floor —
  i.e. **the f64 optimizer converges to an `O(u)` neighborhood of the true minimum**,
  and in particular `f_K^fl ≤ f₀·(1+ε)`, `ε = O(Ku)` — the descent postcondition,
  now *proven* (with an explicit rounding slack) rather than vector-tested.

Deliverable: `lean-proofs/Convergence/GdFloat.lean`, sorry-free, importing the
axioms. **Numeric cross-check:** evaluate the `(1+cu)^{2K}` slack at `K=200`
(`≈ 1 + 1600u ≈ 1 + 1.8e-13`) and confirm it bounds the *observed* L1 residuals
across the 190 conformant vectors (they must all sit inside the proven envelope).

---

## Track 3 — certified bounded-box enclosure (independent corroboration)

### Phase D — verified interval arithmetic  ★

Over a **bounded box** `x₀,y₀ ∈ [−B,B]`, `η ∈ [η_lo,η_hi]`, certify
`f(best) ≤ f₀` *without* the analytic limit, by **verified interval arithmetic with
directed (outward) rounding**:

- **D1:** an `Interval` type `[lo,hi]` over ℝ with op lemmas (`add/sub/mul` produce a
  provably-containing enclosure, widened by the directed-rounding bound from the
  Phase-B axioms — so D and B share *exactly one* trusted base, reinforcing the
  audit rather than enlarging it).
- **D2:** an interval evaluator for the 200-step gd iteration; prove by `iterate`
  induction that the true f64 trajectory is enclosed (`f64 ∈ interval` at every step,
  via the rounding axioms).
- **D3:** the certificate: the output interval's `hi ≤` the input `f₀` interval's
  `lo` over the box ⇒ `f(best) ≤ f₀` for *every* start in the box, machine-checked.

Deliverable: `lean-proofs/Convergence/GdInterval.lean`, sorry-free. **D corroborates
B:** B's analytic envelope and D's computed enclosure bound the *same* `f_K^fl`; the
plan asserts and checks `D's hi ≤ B's envelope` at the box corners. Disagreement =
a bug in one of them (the cross-check the quality bar demands).

---

## Harness & CI integration

- **New float-prove backend.** `lift prove` is **Aeneas-only** today
  (`src/main.rs:204`). Add a dispatch: for `Profile::OptGd`, `prove` emits/realizes
  the `lean-proofs/Convergence/*.lean` obligations and certifies them sorry-free via
  `lake env lean` (the proofs project), reporting `L3 proved, axioms: [list], N
  obligations`. The **axiom list is surfaced in the report** — trusted base is never
  hidden.
- **`ci.sh`:** add `prove opt-gd` (Track 1: proved, axioms enumerated, sorry-free) and
  the Track-3 box certificate; add **teeth** — perturb a theorem (wrong `ρ`, or drop
  the `η<1` hypothesis) and assert the proof *fails* (no vacuous green).
- The runtime `lean/` stays Mathlib-free; all heavy proving is isolated in
  `lean-proofs/`.

## Phasing & gates

| Phase | Deliverable | Gate |
|---|---|---|
| **0** | `lean-proofs/` lake project; Mathlib available (reuse Aeneas cache if possible) | `lake build` green |
| **A** | `GdReal.lean` — A1/A2/A3 sorry-free | ci + review |
| **B** | `FloatModel.lean` axioms + `GdFloat.lean` B1/B2/B3 | ci + review (**axiom audit**) |
| **D** | `GdInterval.lean` D1/D2/D3 + B↔D cross-check | ci + review |
| **H** | `lift prove opt-gd` float backend + `ci.sh` regressions + teeth | ci + review |

## Trusted base (must stay this short)

1. The IEEE-754 rounding model axioms (`FloatModel.lean`) — Higham §2.2, f64
   `u = 2⁻⁵³`, subnormal floor `η_sub = 2⁻¹⁰⁷⁴`.
2. Lean's `Float` ⇄ `ℝ` correspondence on `+ − *` is *correctly rounded* (already
   asserted in `lean/LeanLift/Float.lean`'s header; the axioms formalize it).
3. The bounded-operand precondition (no overflow/inf/nan; inputs in the stated box) —
   discharged for the test domain, *assumed* in the theorem hypotheses.

Everything else (the closed form, the contraction, the limit, the interval
enclosure) is **proven**. Track C (derive base #1 from a Flocq/Flean formalization,
removing it from the trusted list) is the documented future upgrade — not in scope.
