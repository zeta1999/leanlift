/-
  Candidate Lean model of `fdot4`, plus a runner.

      fdot4(a0..a3, b0..b3) = (a0*b0 + a1*b1) + (a2*b2 + a3*b3)   over f32

  PAIRWISE (tree) summation of the four products — the same four rounded products
  the C++ oracle (examples/fdot/fdot4.cpp) sums LEFT-TO-RIGHT, but reassociated.
  Reassociation changes the rounding, so this is bit-exact with the oracle on many
  inputs and differs by a few ULPs on the rest: it conforms only under a
  `--float-tol` tolerance (e.g. `rel:1e-6`), validating a reordered reduction.

  Inputs/outputs travel as 32-bit IEEE patterns; NaN → `NAN`, -0.0 → `0`
  (canonical, matching the oracle). Args arrive in the order a0 a1 a2 a3 b0 b1 b2 b3.
-/
import LeanLift.Float

open LeanLift

namespace Candidate

/-- The model: pairwise (tree) summation of the four f32 products. -/
def fdot4 (a0 a1 a2 a3 b0 b1 b2 b3 : Float32) : Float32 :=
  let p0 := a0 * b0 + a1 * b1
  let p1 := a2 * b2 + a3 * b3
  p0 + p1

end Candidate

def fmtF (x : Float32) : String :=
  if x.isNaN then "NAN"
  else
    let b := x.toBits
    if b == (0x80000000 : UInt32) then "0" else toString b

def main : IO Unit := do
  let path := (← IO.getEnv "LEANLIFT_VECTORS").getD "vectors.txt"
  for line in (← IO.FS.lines path) do
    let nums := (line.splitOn " ").filterMap (·.toNat?)
    match nums with
    | [a0, a1, a2, a3, b0, b1, b2, b3] =>
        let f := fun (n : Nat) => Float32.ofBits n.toUInt32
        let r := Candidate.fdot4 (f a0) (f a1) (f a2) (f a3) (f b0) (f b1) (f b2) (f b3)
        IO.println s!"{a0} {a1} {a2} {a3} {b0} {b1} {b2} {b3} => {fmtF r}"
    | _ => pure ()
