/-
Phase A2 — worked examples: the program logic composing end to end.

Demonstrates that the `wp` rules (`wp_bind` + the per-operation rules) actually
compose to verify real `λ-conc` heap programs, and — via adequacy — that the
verified spec constrains the *real* operational machine. Sorry-free.
-/
import LeanliftIris.PhaseA.WpLifting
import LeanliftIris.PhaseA.Adequacy

namespace LeanliftIris.PhaseA
open Iris Iris.BI COFE

variable {F} [UFraction F] {GF} [ElemG GF (FHeap (F := F))]

/-- **`load (alloc v)` returns `v`.** Composes `wp_bind` (evaluate the `alloc`
in the `load`'s argument position), `wp_alloc` (fresh `l ↦ v`), and `wp_load`
(read it back) — the program logic verifying a real two-operation heap program. -/
theorem ex_alloc_load (γ : GName) [HasHeap γ GF F] (v : Val) :
    ⊢ wp (F := F) γ (.load (.alloc (.val v))) (fun w => iprop(⌜w = v⌝)) := by
  -- focus the `alloc` inside the `load` context `[loadF]`
  show ⊢ wp (F := F) γ (fill [Frame.loadF] (.alloc (.val v))) (fun w => iprop(⌜w = v⌝))
  iapply (wp_bind γ [Frame.loadF] (.alloc (.val v)) (fun w => iprop(⌜w = v⌝)))
  -- verify `alloc v`: get a fresh `l ↦ v`, continue with `load (loc l)`
  iapply (wp_alloc γ v)
  iintro %l Hpt
  iintro !>
  -- the continuation is `load (loc l)` (reduce the context plug)
  simp only [fill, List.foldr_cons, List.foldr_nil, fill1]
  -- verify `load (loc l)`: read back `v`, return the points-to to the continuation
  iapply (wp_load γ l v (fun w => iprop(⌜w = v⌝)))
  isplitl [Hpt]
  · iexact Hpt
  · iintro Hpt2
    iintro !>
    ipure_intro
    rfl

/-! ## The full pipeline, closed: spec ⇒ operational fact

`ex_alloc_load` (the worked `wp` proof) + `heap_init` + `wp_adequacy_closed`: from
nothing — ghost heap allocated, `wp` proved — the abstract spec constrains the real
machine's result. -/

/-- **The closed input to adequacy for `load (alloc v)`.** Allocate the empty heap
(`heap_init`) and frame in the worked `wp` proof — no iProp hypotheses remain. -/
theorem ex_alloc_load_closed_input (γ : GName) [HasHeap γ GF F] (v : Val) :
    (iprop(True) : IProp GF) ⊢
      iprop(|==> ∃ γ' : GName, stateInterp γ' emptyHeap ∗
        wp (F := F) γ' (.load (.alloc (.val v))) (fun w => iprop(⌜w = v⌝))) := by
  have hte : (iprop(True) : IProp GF) ⊢ (emp : IProp GF) :=
    biaffine_iff_true_emp.1 inferInstance
  refine hte.trans ((heap_init (F := F) (GF := GF) emptyHeap).trans (BIUpdate.mono ?_))
  iintro ⟨%γ', HSI⟩
  iexists γ'
  isplitl [HSI]
  · iexact HSI
  · iapply (ex_alloc_load (F := F) γ' v)

/-- **The pipeline, closed.** Any fork-free run of `load (alloc v)` from the empty
heap that reaches a value `r` has `r = v`: the `wp` spec pins the real machine's
result, with the ghost heap allocated from nothing. The hypothesis is exactly
`ex_alloc_load_closed_input` (the closed adequacy input); the run is the operational
side. (`γ` only carries the ambient heap-logic setup, as in `wp_adequacy_val`; the
state-interp/`wp` ghost name is allocated fresh inside.) -/
theorem ex_alloc_load_adequate (γ : GName) [HasHeap γ GF F] (v r : Val) (σ' : Heap)
    (hrun : primSteps (.load (.alloc (.val v))) emptyHeap (.val r) σ')
    (hin : (iprop(True) : IProp GF) ⊢
      iprop(|==> ∃ γ' : GName, stateInterp γ' emptyHeap ∗
        wp (F := F) γ' (.load (.alloc (.val v))) (fun w => iprop(⌜w = v⌝)))) : r = v :=
  wp_adequacy_closed (φ := fun w => w = v) hrun hin

end LeanliftIris.PhaseA
