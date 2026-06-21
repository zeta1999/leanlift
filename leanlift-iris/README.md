# leanlift-iris

Phase 0 sandbox for the **Iris-in-Lean concurrency lane** (see
[`../docs/PLAN-concurrency.md`](../docs/PLAN-concurrency.md)).

This package depends on the upstream Lean 4 port of Iris
([leanprover-community/iris-lean](https://github.com/leanprover-community/iris-lean)),
pinned to **v4.28.0** to match the repo's installed toolchain. It uses the **core
`Iris` library only** (Qq dependency, no Mathlib) — `IrisMath` is deferred to
Phase A, when the camera/algebra layer is actually needed.

## Status

- **0.1 — iris-lean as a dependency, build green.** ✅ `lake build` succeeds.
- **0.2 — MoSeL "hello world".** ✅ `LeanliftIris/Hello.lean` proves three generic
  separation-logic tautologies (`ent_refl`, `sep_comm`, `wand_elim`) through the
  proof mode (`iintro`/`isplitl`/`iexact`/`iapply`). All three **depend on no
  axioms** (verified via `#print axioms`).

- **A3 — first functional proofs (SC), the pure-function warm-up.** ✅ Done as
  standalone core-Lean proofs (no Iris/program-logic dependency yet), turning the
  C++ corpus' fuzz-tested properties into universally-quantified theorems:
  - `LeanliftIris/PhaseA/Sweep.lean` (#10 effective-best): exact `filled =
    min Q total`, completion ⇔ `Q ≤ total`, over-ask, drained-level skipping, and
    the VWAP bracket `best_ask·filled ≤ notional ≤ touch·filled` (notional in
    unbounded `Nat`, so *exactly* the C++ 128-bit accumulator with no overflow).
  - `LeanliftIris/PhaseA/OrderBook.lean` (#9 l2-order-book): `maxOcc`/`minOcc`
    characterised as the greatest/least occupied tick (the spec the bitmap's
    `clz`/`ctz` must meet), bid- and ask-side **fall-back** on cancel, and the
    microprice bracket `[best_bid, best_ask]`.
  - All sorry-free; `LeanliftIris/PhaseA/Axioms.lean` audits them (`propext`,
    `Quot.sound` only — no `sorryAx`, no `Classical.choice`).

  Deferred follow-ons (not required by A3): the hierarchical-bitmap `clz`/`ctz`
  refinement of `maxOcc`/`minOcc`, and the optional `sweep_linear == prefix.query`
  two-engine equivalence.

- **A1 — the `λ-conc` object language.** ✅ `LeanliftIris/PhaseA/Lang.lean`: a
  minimal HeapLang-style concurrent core (closures, pairs, int/bool ops, a heap
  with `alloc`/`load`/`store`, atomic `CAS`/`FAA`, `fork`) with a
  **sequentially-consistent** small-step semantics — `Head` reduction under
  evaluation contexts (`prim_step`), lifted to a thread-pool interleaving `step`
  / `steps`. SC = every step threads the single shared heap (no per-location
  order); Phase B swaps this layer for weak memory. Sanity lemmas: values are not
  redexes (progress), plus worked `alloc`/`load`/atomic-`CAS`/`fork` reductions.
  Next: **A2** lifts an Iris `wp` over this language and proves adequacy; **A4**
  (Treiber, SC) builds on both.

## Build

```sh
lake update    # fetches iris (v4.28.0) + Qq (v4.28.0)
lake build
```

Audit the Phase-A proofs are axiom-clean:

```sh
lake env lean LeanliftIris/PhaseA/Axioms.lean
```

## Notes

- Qq is pinned to the `v4.28.0` tag in `lakefile.toml` to override iris's moving
  `git#stable` require, whose old commit had been GC'd upstream.
- The class is `Iris.BI`; from a foreign namespace use `open Iris Iris.BI` so the
  bare name `BI` resolves and the `∗`/`-∗`/`⊢` notation is in scope.
