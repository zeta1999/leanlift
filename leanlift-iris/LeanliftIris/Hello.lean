/-
Phase 0.2 — MoSeL "hello world".

Proves that the upstream Iris proof mode (`iintro`, `isplitl`, `iexact`,
`iapply`, ...) is usable from this package over an arbitrary bunched-implication
logic `PROP`. These are generic separation-logic tautologies — no model, no
resources yet — just enough to confirm the proof mode, the `∗`/`-∗` connectives,
and the `⊢` entailment all work end to end. Sorry-free.
-/
import Iris.BI
import Iris.ProofMode

namespace LeanliftIris
-- `open Iris` so the bare class name `BI` resolves to `Iris.BI`; `open Iris.BI`
-- brings the `∗` / `-∗` / `⊢` notation and proof-mode names into scope.
open Iris Iris.BI

/-- Entailment is reflexive. -/
theorem ent_refl {PROP : Type _} [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  iexact HP

/-- Separating conjunction commutes. -/
theorem sep_comm {PROP : Type _} [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP

/-- Modus ponens through the magic wand. -/
theorem wand_elim {PROP : Type _} [BI PROP] (P Q : PROP) : P ∗ (P -∗ Q) ⊢ Q := by
  iintro ⟨HP, HPQ⟩
  iapply HPQ
  iexact HP

end LeanliftIris
