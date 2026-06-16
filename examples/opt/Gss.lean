/-
  Candidate Lean model of the golden-section search `gss`, plus a vector runner.

      gss(a, b, tol): minimize f(x) = (x-3)² + 1 on [a, b] by golden-section
      search; return the bracket midpoint once the width ≤ tol.

  This is the *candidate* — untrusted; the engine validates it bit-for-bit
  against the C++ `double` oracle. The bounded loop is the `Float.iterate`
  combinator from the audited `LeanLift.Float` library: 100 steps, where a step
  is the identity once `h ≤ tol` (mirroring the C++ `break`, so the final
  bracket — and its midpoint — are bit-identical). Inputs/outputs travel as IEEE
  bit patterns; NaN → `NAN`, -0.0 → `0`.
-/
import LeanLift.Float

open LeanLift

namespace Candidate

/-- The objective f(x) = (x-3)² + 1, op-for-op with the C++ source. -/
def f (x : Float) : Float := (x - 3.0) * (x - 3.0) + 1.0

/-- Golden-section search, returning the final bracket midpoint. -/
def gss (a b tol : Float) : Float :=
  let s5 := Float.sqrt 5.0
  let invphi := (s5 - 1.0) / 2.0
  let invphi2 := (3.0 - s5) / 2.0
  let step := fun (ab : Float × Float) =>
    let a := ab.1
    let b := ab.2
    let h := b - a
    if h ≤ tol then (a, b)
    else
      let c := a + invphi2 * h
      let d := a + invphi * h
      let fc := f c
      let fd := f d
      if fc < fd then (a, d) else (c, b)
  let r := Float.iterate 100 step (a, b)
  (r.1 + r.2) / 2.0

end Candidate

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
    | [a, b, t] =>
        let r := Candidate.gss (Float.ofBits a.toUInt64) (Float.ofBits b.toUInt64)
                   (Float.ofBits t.toUInt64)
        IO.println s!"{a} {b} {t} => {fmtF r}"
    | _ => pure ()
