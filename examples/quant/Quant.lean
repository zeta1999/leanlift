/-
  Candidate Lean model of the parametric float-cast rounding `quantize_rne`,
  plus a vector runner. Round `n` to `prec` mantissa bits, round-to-nearest-even.
  `prec` selects the format: 2=fp8-E5M2, 3=fp8-E4M3, 7=bf16, 10=fp16, 23=f32,
  52=f64. The model is over `Nat` (exact), matching the C++ source bit-for-bit on
  the integer-significand domain. See docs/float-formats.md.
-/
import LeanLift.Checked

open LeanLift

namespace Candidate

/-- Round `n` to `prec` mantissa bits below the leading bit, ties to even. -/
def qrne (prec n : Nat) : Nat :=
  if n = 0 then 0
  else
    let e := Nat.log2 n                 -- floor(log2 n)
    if e ≤ prec then n                  -- already representable
    else
      let shift := e - prec
      let step := 1 <<< shift           -- 2^shift  = ulp in this binade
      let low := (n >>> shift) <<< shift -- round toward zero
      let rem := n - low
      let half := step >>> 1
      if rem > half then low + step
      else if rem < half then low
      else if ((low >>> shift) &&& 1) = 0 then low else low + step  -- tie → even

def quantize_rne (prec : U8) (n : U64) : Res U64 :=
  .ok (UInt.lit (qrne prec.val n.val))

end Candidate

def fmt : Res U64 → String
  | .ok v => toString v.val
  | .fail => "OVERFLOW"

def main : IO Unit := do
  let path := (← IO.getEnv "LEANLIFT_VECTORS").getD "vectors.txt"
  for line in (← IO.FS.lines path) do
    let nums := (line.splitOn " ").filterMap (·.toNat?)
    match nums with
    | [prec, n] =>
        IO.println s!"{prec} {n} => {fmt (Candidate.quantize_rne (UInt.lit prec) (UInt.lit n))}"
    | _ => pure ()
