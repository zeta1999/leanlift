/-
  Candidate Lean model of fixed-step gradient descent `gd`, plus a vector runner.

      gd(x0, y0, eta): minimize f(x,y) = (x-1)² + (y-2)² by gradient descent,
      ∇f = (2(x-1), 2(y-2)); return the final objective f(x_K, y_K).

  Untrusted candidate, validated bit-for-bit against the C++ `double` oracle.
  The fixed 200-step loop is `Float.iterate` over the state `(x, y)`. Inputs and
  the result travel as IEEE bit patterns; NaN → `NAN`, -0.0 → `0`.
-/
import LeanLift.Float

open LeanLift

namespace Candidate

def gd (x0 y0 eta : Float) : Float :=
  let step := fun (p : Float × Float) =>
    let x := p.1
    let y := p.2
    let gx := 2.0 * (x - 1.0)
    let gy := 2.0 * (y - 2.0)
    (x - eta * gx, y - eta * gy)
  let r := Float.iterate 200 step (x0, y0)
  (r.1 - 1.0) * (r.1 - 1.0) + (r.2 - 2.0) * (r.2 - 2.0)

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
    | [a, b, c] =>
        let r := Candidate.gd (Float.ofBits a.toUInt64) (Float.ofBits b.toUInt64)
                   (Float.ofBits c.toUInt64)
        IO.println s!"{a} {b} {c} => {fmtF r}"
    | _ => pure ()
