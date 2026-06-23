/-
Phase A2 (fancy-update, infra) — the identity functor and the recursive
invariant-authority functor.

To store a proposition `▷ (IProp GF)` inside ghost state we need a *recursive*
resource functor whose application to `IProp GF` is
`Auth (GenMap Nat (Agree (Later (IProp GF))))`. iris-lean ships `AgreeRF`,
`GenMapOF`, `AuthRF`, and `LaterOF`, but two ingredients are missing:

* an **identity functor** `idOF` (returning the recursion variable), and
* the fact that **`Later` *introduces* contractivity** — iris-lean's only
  `OFunctorContractive (LaterOF F)` instance *requires* `F` already contractive,
  whereas `idOF` is merely non-expansive. We prove `OFunctorContractive (LaterOF idOF)`
  directly: the contractivity comes entirely from `Later`'s `Dist n = DistLater n`.

With those, `FInv` below is `RFunctorContractive` and registrable via `ElemG`.
Sorry-free.
-/
import Iris.BI
import Iris.Algebra

namespace LeanliftIris.PhaseA.Fupd
open Iris COFE OFE

/-- The identity object functor: ignores the contravariant argument and returns
the (covariant) recursion variable. `map f g := g`. -/
abbrev idOF : OFunctorPre := fun _ B _ _ => B

instance oFunctorIdOF : OFunctor idOF where
  cofe := inferInstance
  map _ g := g
  map_ne := by
    intros
    constructor
    intro _ _ _ _ _ _ hg
    exact hg
  map_id _ := .rfl
  map_comp _ _ _ _ _ := .rfl

/-- **Later introduces contractivity.** Even though `idOF` is not contractive,
`LaterOF idOF` is: `Later`'s distance at index `n` only constrains the car at
strictly smaller indices, which is exactly the `DistLater` premise. -/
instance oFunctorContractiveLaterIdOF : OFunctorContractive (LaterOF idOF) where
  map_contractive.1 := by
    intro n p q H z
    intro m hm
    exact (H m hm).2 z.car

/-- The *value* functor for stored invariant bodies: an agreed later-proposition.
Applied to `IProp GF` this is `Agree (Later (IProp GF))`. It is `RFunctorContractive`
(the body sits under `Later`), so it can be the value type of a recursive
authoritative map (`HeapViewURF FProp`, see `Fupd.Wsat`). -/
abbrev FProp : OFunctorPre := AgreeRF (LaterOF idOF)

-- Smoke-check that the value functor is registrable (recursive + contractive).
example : RFunctorContractive FProp := inferInstance

end LeanliftIris.PhaseA.Fupd
