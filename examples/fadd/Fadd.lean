/-
  Candidate Lean model of the float smoke kernel `fadd`, plus a vector runner.

      fadd(a, b) = a + b   over f64

  Like the integer examples this file is the *candidate* — untrusted; the engine
  validates it against the C++ `double` source by bit-exact differential
  execution. Inputs/outputs travel as IEEE-754 bit patterns (decimal `Nat`s);
  the result prints as its bit pattern, with NaN → `NAN` and -0.0 → `0` so the
  comparison is canonical (the C++ oracle canonicalizes identically).
-/
import LeanLift.Float

open LeanLift

namespace Candidate

/-- The model: native binary64 addition. -/
def fadd (a b : Float) : Float := a + b

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
    | [a, b] =>
        let r := Candidate.fadd (Float.ofBits a.toUInt64) (Float.ofBits b.toUInt64)
        IO.println s!"{a} {b} => {fmtF r}"
    | _ => pure ()
