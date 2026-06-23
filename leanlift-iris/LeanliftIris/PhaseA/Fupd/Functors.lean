/-
Phase A2 (fancy-update, infra) — identity functor + a universe-preserving `later`.

To store a proposition inside ghost state (saved propositions / invariants) we need a
*recursive* resource functor whose value, applied to `IProp GF`, is
`Agree (later (IProp GF))`. Two ingredients are missing from iris-lean:

* an **identity functor** `idOF` (returning the recursion variable), and
* a **universe-preserving** later that *introduces* contractivity.

The second point is subtle and decisive. iris-lean's `Later A : Type (u+1)` *bumps*
the universe, while `iOwn`/`IProp`/`IResUR` are monomorphic at universe 0
(`@iOwn` demands `BundledGFunctors.{0,0,0}`). Since every registered functor must be
`RFunctorContractive` and `Later` is the only contractivity source for storing the
recursion variable, `Agree (Later (IProp GF)) : Type 1` can never be a resource — so
*propositions cannot be stored in ghost state at all* using the upstream `Later`.

We sidestep this by defining `LaterS A`, a single-field structure that stays at
`Type u` (the upstream `: Type (u+1)` annotation is the only thing forcing the bump).
`LaterS` carries the same `DistLater` OFE, so `LaterSOF` *introduces* contractivity
exactly like `Later`, but `Agree (LaterS (IProp GF)) : Type 0` — usable in `iOwn`.

With `idOF` + `LaterSOF`, `FProp = AgreeRF (LaterSOF idOF)` is `RFunctorContractive`
and proposition storage works (`Fupd.InvRes`). Sorry-free.
-/
import Iris.BI
import Iris.Algebra
import Iris.Instances.IProp

namespace LeanliftIris.PhaseA.Fupd
open Iris COFE OFE

/-! ## The identity object functor -/

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

/-! ## A universe-preserving `later` -/

/-- A universe-preserving later: unlike iris-lean's `Later A : Type (u+1)`, the
single-field structure stays at `Type u`, so `Agree (LaterS (IProp GF))` lands at
the resource universe and can be stored via `iOwn`. -/
structure LaterS (A : Type u) : Type u where
  next :: car : A

instance isOFE_laterS [OFE A] : OFE (LaterS A) where
  Equiv x y := x.car ≡ y.car
  Dist n x y := DistLater n x.car y.car
  dist_eqv := ⟨fun _ => .rfl, .symm, .trans⟩
  equiv_dist := by
    simp only [equiv_dist, DistLater]
    exact ⟨by simp +contextual, fun H n => H (Nat.succ n) n (by simp)⟩
  dist_lt Hxy Hmn _ Hkm := Hxy _ (Nat.lt_trans Hkm Hmn)

/-- Functorial action of `LaterS`. -/
def laterSMap [OFE A] [OFE B] (f : A -n> B) : LaterS A -n> LaterS B := by
  refine ⟨fun x => LaterS.next (f x.car), ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H <;> simp_all only [Dist, DistLater]
  intros m Hlt; exact f.ne.ne (H m Hlt)

/-- The later object functor. -/
abbrev LaterSOF (F : OFunctorPre) : OFunctorPre := fun A B _ _ => LaterS (F A B)

instance laterSOF_ofunctor [OFunctor F] : OFunctor (LaterSOF F) where
  cofe := _
  map f g := laterSMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := (OFunctor.map_ne.ne Hx Hy _).lt
  map_id _ := OFunctor.map_id _
  map_comp _ _ _ _ _ := OFunctor.map_comp ..

/-- **Later introduces contractivity.** The contractivity comes entirely from
`LaterS`'s `Dist n = DistLater n` (only constrains the car at strictly smaller
indices), so `LaterSOF F` is contractive for *any* `OFunctor F` — in particular the
non-contractive `idOF`. -/
instance laterSOF_contractive [OFunctor F] : OFunctorContractive (LaterSOF F) where
  map_contractive.1 := by
    intro n p q H z m hm
    exact OFunctor.map_ne.ne (H m hm).1 (H m hm).2 z.car

/-! ## The value functor for stored invariant bodies -/

/-- The *value* functor for stored invariant bodies: an agreed later-proposition.
Applied to `IProp GF` this is `Agree (LaterS (IProp GF))`, which sits at the resource
universe and is `RFunctorContractive`, so it is the value type of the recursive
authoritative invariant map (`HeapViewURF FProp`, see `Fupd.InvRes`). -/
abbrev FProp : OFunctorPre := AgreeRF (LaterSOF idOF)

-- Smoke-check that the value functor is registrable (recursive + contractive).
example : RFunctorContractive FProp := inferInstance

end LeanliftIris.PhaseA.Fupd
