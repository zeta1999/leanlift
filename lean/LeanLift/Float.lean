/-
  LeanLift — audited support library: IEEE-754 floating-point arithmetic.

  The float companion to `Checked.lean`. Where the integer library models
  *checked* arithmetic (overflow ⇒ `fail`), floats need no such monad: leanlift
  certifies a float kernel by **bit-exact differential execution** against the
  C++ `double` oracle. Lean's native `Float` is IEEE-754 binary64 (`@[extern]`),
  and on the basic operations it is *correctly rounded* — so `+ - * /` and
  `Float.sqrt` agree bit-for-bit with C++ `double` compiled `-ffp-contract=off`
  (verified on arm64). A value travels as its bit pattern (`Float.toBits` /
  `Float.ofBits`); the runner canonicalizes NaN and `-0.0`.

  The audited surface a candidate may target is therefore small and explicit:
  the four arithmetic ops, `Float.sqrt`, comparisons, `Float` literals, and the
  one bounded looping combinator below. No transcendentals (not bit-reproducible).

  Caveat (SPEC §13 / docs/float-formats.md): `Float` is opaque to the kernel, so
  this path is L1 (testing) only — *no* L3 proof is provable about native
  `Float`. The certified-rounding-bound track (FloatSpec/Flean/FLoPS) is separate.

  No Aeneas, no Mathlib: plain Lean 4 core, runnable with `lean --run`.
-/

namespace LeanLift

/-- Bounded iteration: apply `f` to the state `s` exactly `n` times. This is the
    single looping combinator a float candidate may use, so every model stays
    structurally terminating (no `partial`, no unbounded `while`). A fixed-step
    optimizer of `K` iterations is `Float.iterate K step s₀`. -/
def Float.iterate {σ : Type} (n : Nat) (f : σ → σ) (s : σ) : σ :=
  match n with
  | 0       => s
  | (m + 1) => Float.iterate m f (f s)

end LeanLift
