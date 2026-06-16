/-
  Candidate Lean model of the float32 smoke kernel `fadd32`, plus a runner.

      fadd32(a, b) = a + b   over f32  (Lean `Float32`, binary32)

  The float32 counterpart of Fadd.lean: validated bit-for-bit against the C++
  `float` oracle. Inputs/outputs travel as 32-bit IEEE patterns; NaN → `NAN`,
  -0.0 → `0` (canonical, matching the oracle).
-/
import LeanLift.Float

open LeanLift

namespace Candidate

/-- The model: native binary32 addition. -/
def fadd32 (a b : Float32) : Float32 := a + b

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
    | [a, b] =>
        let r := Candidate.fadd32 (Float32.ofBits a.toUInt32) (Float32.ofBits b.toUInt32)
        IO.println s!"{a} {b} => {fmtF r}"
    | _ => pure ()
