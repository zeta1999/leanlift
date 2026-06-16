/-
  Candidate Lean model of Hooke–Jeeves pattern search `hooke_jeeves`, plus a
  vector runner.

      hooke_jeeves(x0, y0, step): minimize f(x,y) = (x-1)² + (y-2)² with NO
      gradient — probe ±step per coordinate, accept improving moves, halve the
      step on a fruitless sweep; return the best objective.

  Untrusted candidate, validated bit-for-bit against the C++ `double` oracle.
  The bounded 100-sweep loop is `Float.iterate` over the state `(x, y, h, fbest)`.
  Inputs/result travel as IEEE bit patterns; NaN → `NAN`, -0.0 → `0`.
-/
import LeanLift.Float

open LeanLift

namespace Candidate

def hooke_jeeves (x0 y0 step : Float) : Float :=
  let f := fun (x y : Float) => (x - 1.0) * (x - 1.0) + (y - 2.0) * (y - 2.0)
  let sweep := fun (p : Float × Float × Float × Float) =>
    let x := p.1
    let y := p.2.1
    let h := p.2.2.1
    let fbest := p.2.2.2
    -- explore along x
    let fxp := f (x + h) y
    let (nx, fb1) :=
      if fxp < fbest then (x + h, fxp)
      else
        let fxm := f (x - h) y
        if fxm < fbest then (x - h, fxm) else (x, fbest)
    -- explore along y, from the possibly-updated nx
    let fyp := f nx (y + h)
    let (ny, fb2) :=
      if fyp < fb1 then (y + h, fyp)
      else
        let fym := f nx (y - h)
        if fym < fb1 then (y - h, fym) else (y, fb1)
    if (nx == x) && (ny == y) then (x, y, h * 0.5, fb2)
    else (nx, ny, h, fb2)
  let r := Float.iterate 100 sweep (x0, y0, step, f x0 y0)
  r.2.2.2

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
        let r := Candidate.hooke_jeeves (Float.ofBits a.toUInt64) (Float.ofBits b.toUInt64)
                   (Float.ofBits c.toUInt64)
        IO.println s!"{a} {b} {c} => {fmtF r}"
    | _ => pure ()
