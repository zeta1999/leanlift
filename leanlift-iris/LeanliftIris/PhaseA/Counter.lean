/-
Phase A4 — a fetch-and-add atomic counter, the third worked operation.

Where Treiber `push`/`pop` exercise the linking `CAS`, the counter exercises the
*arithmetic* read-modify-write `FAA` — the contention point of the Vyukov MPSC
studied abstractly in Phase B. The annotation is a one-cell representation
`isCounter γ s k` (`s ↦ int k`); the property is that `incr` (a single `FAA(s, 1)`)
returns the old value and advances the count. Sorry-free.
-/
import LeanliftIris.PhaseA.WpLifting

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-- `isCounter γ s k`: the cell `s` holds the integer count `k`. -/
def isCounter (γ : GName) [HasHeap γ GF F] (s : Nat) (k : Int) : IProp GF :=
  s ↦[γ] (.int k)

/-- `incr s` increments the counter at `s` and returns the old value: a single
fetch-and-add of `1`. -/
def incrBody (s : Nat) : Expr := .faa (.val (.loc s)) (.val (.int 1))

/-- **`incr` advances the count and returns the old value.** On a counter holding
`k`, running `incr` returns `int k` and leaves a counter holding `k + 1` — the
linearizable specification of an atomic increment, discharged by `wp_faa`. -/
theorem incr_spec (γ : GName) [HasHeap γ GF F] (s : Nat) (k : Int) :
    isCounter γ s k ⊢
      wp (F := F) γ (incrBody s) (fun r => iprop(⌜r = .int k⌝ ∗ isCounter γ s (k + 1))) := by
  simp only [incrBody, isCounter]
  iintro Hc
  iapply (wp_faa γ s k 1)
  isplitl [Hc]
  · iexact Hc
  · iintro Hc'
    iintro !>
    isplitl []
    · ipure_intro; rfl
    · iexact Hc'

end LeanliftIris.PhaseA
