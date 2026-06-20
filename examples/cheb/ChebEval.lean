/-
  Candidate Lean model of `cheb_eval4`, plus a vector runner.

      cheb_eval4(c0,c1,c2,c3, x) = Σ_{k=0}^{3} c_k · T_k(x)   over f64

  Clenshaw evaluation of a degree-3 Chebyshev series — the fixed-arity
  reformulation of `quantum-core/src/linalg/chebyshev.rs::eval_chebyshev`, the
  QSVT/QLSS inversion-polynomial kernel (LEAN_ERROR_PLAN LE1-a). The Rust loop
  folds the tail coefficients [c3, c2, c1] through the recurrence
  `b0 = 2·x·b1 − b2 + c`; this is that fold unrolled, op-for-op, so it agrees
  with the C++ `double` oracle (examples/cheb/cheb_eval.cpp) bit-for-bit. Only
  `+ - *` are used (no transcendentals), so native binary64 `Float` is the
  faithful model — the honest ceiling is L1 (Float is opaque to Aeneas, so no
  L3 here).

  Inputs/outputs travel as IEEE-754 bit patterns (decimal `Nat`s); NaN → `NAN`
  and -0.0 → `0` so the comparison is canonical. Args arrive c0 c1 c2 c3 x.
-/
import LeanLift.Float

open LeanLift

namespace Candidate

/-- The model: Clenshaw recurrence over the four coefficients, unrolled. -/
def cheb_eval4 (c0 c1 c2 c3 x : Float) : Float :=
  let b1₀ : Float := 0.0
  let b2₀ : Float := 0.0
  -- fold c3
  let b0a := 2.0 * x * b1₀ - b2₀ + c3
  let b2a := b1₀
  let b1a := b0a
  -- fold c2
  let b0b := 2.0 * x * b1a - b2a + c2
  let b2b := b1a
  let b1b := b0b
  -- fold c1
  let b0c := 2.0 * x * b1b - b2b + c1
  let b2c := b1b
  let b1c := b0c
  c0 + x * b1c - b2c

end Candidate

/-- Format one float result: the bit pattern, or `NAN`; -0.0 collapses to 0. -/
def fmtF (x : Float) : String :=
  if x.isNaN then "NAN"
  else
    let b := x.toBits
    if b == (0x8000000000000000 : UInt64) then "0" else toString b

def main : IO Unit := do
  let path := (← IO.getEnv "LEANLIFT_VECTORS").getD "vectors.txt"
  for line in (← IO.FS.lines path) do
    let nums := (line.splitOn " ").filterMap (·.toNat?)
    match nums with
    | [c0, c1, c2, c3, x] =>
        let f := fun (n : Nat) => Float.ofBits n.toUInt64
        let r := Candidate.cheb_eval4 (f c0) (f c1) (f c2) (f c3) (f x)
        IO.println s!"{c0} {c1} {c2} {c3} {x} => {fmtF r}"
    | _ => pure ()
