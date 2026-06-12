/-
  LeanLift — audited support library: checked machine-integer arithmetic.

  This is the *fixed, audited* Lean library that LLM/Aeneas candidates target
  (SPEC §13). It models a fixed-width unsigned machine integer whose arithmetic
  is **checked**: any operation whose mathematical result leaves the range
  `[0, 2^W)` (overflow, underflow, division by zero) yields `Res.fail` rather
  than wrapping. This reproduces the semantics of Rust's debug-mode checked
  arithmetic and Aeneas's `Result` monad — and is exactly what diverges from
  C/C++'s silent two's-complement wrap.

  No Aeneas, no Mathlib: plain Lean 4 core, runnable with `lean --run`.
-/

namespace LeanLift

/-- A computation that may fail (overflow / underflow / division-by-zero).
    The single `fail` constructor mirrors Aeneas's `Result.fail _`: the
    differential oracle only needs the *ok value vs. failure* distinction. -/
inductive Res (α : Type) where
  | ok   : α → Res α
  | fail : Res α
deriving Repr, BEq

namespace Res
@[inline] def bind (x : Res α) (f : α → Res β) : Res β :=
  match x with
  | ok v => f v
  | fail => fail
instance : Monad Res where
  pure := Res.ok
  bind := Res.bind
end Res

/-- A checked unsigned integer of `width` bits, carrying its value as a `Nat`.
    The invariant `val < 2^width` is *maintained by the checked operations*:
    every constructor below either preserves it or returns `fail`. -/
structure UInt (width : Nat) where
  val : Nat
deriving Repr, BEq

namespace UInt

/-- `2^width` — the exclusive upper bound of the representable range. -/
@[inline] def modulus (width : Nat) : Nat := Nat.pow 2 width

/-- Inject a `Nat` known to be in range. Out-of-range input is a `fail`
    (so the runner can never silently smuggle a wrapped value in). -/
@[inline] def ofNat (width : Nat) (n : Nat) : Res (UInt width) :=
  if n < modulus width then .ok ⟨n⟩ else .fail

/-- Inject without the range check — only for literals provably in range. -/
@[inline] def lit (n : Nat) : UInt width := ⟨n⟩

@[inline] def le (a b : UInt width) : Bool := a.val ≤ b.val
@[inline] def ge (a b : UInt width) : Bool := a.val ≥ b.val

/-- Checked subtraction: underflow (`a < b`) fails rather than wrapping. -/
@[inline] def sub (a b : UInt width) : Res (UInt width) :=
  if a.val ≥ b.val then .ok ⟨a.val - b.val⟩ else .fail

/-- Checked addition: a sum `≥ 2^width` fails rather than wrapping. -/
@[inline] def add (a b : UInt width) : Res (UInt width) :=
  ofNat width (a.val + b.val)

/-- Checked multiplication: a product `≥ 2^width` fails rather than wrapping. -/
@[inline] def mul (a b : UInt width) : Res (UInt width) :=
  ofNat width (a.val * b.val)

/-- Checked division: division by zero fails. The quotient is always in range. -/
@[inline] def div (a b : UInt width) : Res (UInt width) :=
  if b.val = 0 then .fail else .ok ⟨a.val / b.val⟩

end UInt

/-- The 32-bit checked integer (used by the `avg` example). -/
abbrev U32 := UInt 32

/-- The 64-bit checked integer (used by the `streamed` example). -/
abbrev U64 := UInt 64

end LeanLift
