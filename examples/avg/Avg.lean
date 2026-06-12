/-
  Candidate Lean model of the integer average `avg`, plus a vector runner.

      avg(a, b) = (a + b) / 2

  The checked `add` reports OVERFLOW where `a + b ≥ 2^32`; C++ wraps. The shared
  runner contract is identical to the streamed example: read `$LEANLIFT_VECTORS`
  (one tuple per line) and print `args => RESULT`.
-/
import LeanLift.Checked

open LeanLift

namespace Candidate

/-- The model, in the checked-`Res` monad over `U32`. -/
def avg (a b : U32) : Res U32 := do
  let s ← UInt.add a b      -- a + b   ← may overflow u32
  UInt.div s (UInt.lit 2)   -- floor division by 2 (2 ≠ 0)

end Candidate

def fmt : Res U32 → String
  | .ok v => toString v.val
  | .fail => "OVERFLOW"

def main : IO Unit := do
  let path := (← IO.getEnv "LEANLIFT_VECTORS").getD "vectors.txt"
  for line in (← IO.FS.lines path) do
    let nums := (line.splitOn " ").filterMap (·.toNat?)
    match nums with
    | [a, b] =>
        let r := Candidate.avg (UInt.lit a) (UInt.lit b)
        IO.println s!"{a} {b} => {fmt r}"
    | _ => pure ()
