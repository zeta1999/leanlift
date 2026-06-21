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

## Build

```sh
lake update    # fetches iris (v4.28.0) + Qq (v4.28.0)
lake build
```

## Notes

- Qq is pinned to the `v4.28.0` tag in `lakefile.toml` to override iris's moving
  `git#stable` require, whose old commit had been GC'd upstream.
- The class is `Iris.BI`; from a foreign namespace use `open Iris Iris.BI` so the
  bare name `BI` resolves and the `∗`/`-∗`/`⊢` notation is in scope.
