/-
Phase A2 — worked examples: the program logic composing end to end.

Demonstrates that the `wp` rules (`wp_bind` + the per-operation rules) actually
compose to verify real `λ-conc` heap programs. Sorry-free.
-/
import LeanliftIris.PhaseA.WpLifting

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

end LeanliftIris.PhaseA
