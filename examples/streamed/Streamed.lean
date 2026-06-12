/-
  Candidate Lean model of the vesting kernel `streamed`, plus a vector runner.

  In the leanlift trust model this file is the *candidate* — what an LLM (for
  C++/Go/Solidity) or Aeneas (for Rust) would emit. Here it is hand-written to
  exercise the oracle. It is **untrusted**: the engine validates it against the
  C++ source by bit-exact differential execution. The job of this file is only
  to (a) define the model and (b) print `args => RESULT` lines for each vector,
  where RESULT is the numeric value or the token `OVERFLOW`.

      streamed(deposit, start, stop, t) =
          0                                    if t ≤ start
          deposit                              if t ≥ stop
          deposit * (t - start) / (stop - start)  otherwise

  The middle case multiplies two unknowns — `deposit * (t - start)` — which is
  where a u64 product can exceed 2^64. The checked model reports that as
  OVERFLOW; C++ wraps. That divergence is the whole demonstration.
-/
import LeanLift.Checked

open LeanLift

namespace Candidate

/-- The model, in the checked-`Res` monad over `U64`. -/
def streamed (deposit start stop t : U64) : Res U64 := do
  if UInt.le t start then UInt.ofNat 64 0
  else if UInt.ge t stop then pure deposit
  else
    let span ← UInt.sub t start        -- t - start   (t > start here)
    let prod ← UInt.mul deposit span   -- deposit * (t - start)  ← may overflow
    let win  ← UInt.sub stop start     -- stop - start
    UInt.div prod win                  -- floor division

end Candidate

/-- Format one result: the value, or the divergence-class token `OVERFLOW`. -/
def fmt : Res U64 → String
  | .ok v => toString v.val
  | .fail => "OVERFLOW"

/-- Read the vector file named by `$LEANLIFT_VECTORS` (one `d s e t` per line)
    and emit `d s e t => RESULT`. Inputs are decimal `Nat`s < 2^64. -/
def main : IO Unit := do
  let path := (← IO.getEnv "LEANLIFT_VECTORS").getD "vectors.txt"
  for line in (← IO.FS.lines path) do
    let nums := (line.splitOn " ").filterMap (·.toNat?)  -- empty tokens drop out
    match nums with
    | [d, s, e, t] =>
        -- inputs are < 2^64 by construction; `lit` is the unchecked injector
        let r := Candidate.streamed (UInt.lit d) (UInt.lit s) (UInt.lit e) (UInt.lit t)
        IO.println s!"{d} {s} {e} {t} => {fmt r}"
    | _ => pure ()
