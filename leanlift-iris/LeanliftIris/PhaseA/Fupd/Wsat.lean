/-
Phase A2 (fancy-update, piece 3) — world satisfaction (`wsat`).

`wsat` is the invariant of invariants: it owns the authoritative invariant map and,
for each allocated name `i` guarding `Q`, the per-name *slot*

  `(▷ Q ∗ ownD {i})  ∨  ownE {i}`

— either the body is stored and the disabled token is held (the invariant is closed),
or the enabled token sits in the world (the invariant is open / available). The
enabled and disabled tokens use the one `FTok` mask algebra (`Fupd.Masks`) under two
ghost names `γE`, `γD`; `ownD γD := ownE γD`.

`WsatG` bundles the three fixed ghost names (`γI` invariants, `γE` enabled,
`γD` disabled) and the two `ElemG` registrations, so the `fupd` modality
(`Fupd.Fupd`) — whose signature `Set Nat → Set Nat → IProp → IProp` has no room for
ghost names — can be a genuine typeclass instance. Sorry-free.
-/
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.Algebra
import Iris.Std.HeapInstances
import LeanliftIris.PhaseA.Fupd.Masks
import LeanliftIris.PhaseA.Fupd.InvRes

namespace LeanliftIris.PhaseA.Fupd
open Iris Iris.BI COFE HeapView One DFrac Agree

variable {F} [UFraction F] {GF} [ElemG GF (FInv F)] [ElemG GF FTok]

/-- The singleton mask `{i}`. -/
def eqset (i : Nat) : Iris.Set Nat := fun j => j = i

/-- Disabled tokens reuse the enabled-token algebra under a separate ghost name. -/
noncomputable abbrev ownD (γ : GName) (D : Iris.Set Nat) : IProp GF := ownE (GF := GF) γ D

/-- The authoritative invariant map built from a name/proposition list. -/
noncomputable def toMap : List (Nat × IProp GF) → (Nat → Option (Agree (LaterS (IProp GF))))
  | [] => fun _ => none
  | (i, Q) :: L => fun j => if j = i then some (toAgree (LaterS.next Q)) else toMap L j

/-- The per-invariant slot: body stored & disabled, or enabled token present. -/
noncomputable def invSlot (γE γD : GName) (i : Nat) (Q : IProp GF) : IProp GF :=
  iprop( (▷ Q ∗ ownD (GF := GF) γD (eqset i)) ∨ ownE γE (eqset i) )

/-- **World satisfaction.** -/
noncomputable def wsat (γI γE γD : GName) : IProp GF :=
  iprop( ∃ L, invAuth (F := F) γI (toMap L) ∗
              [∗] (L.map (fun p => iprop(ownI (F := F) γI p.1 p.2 ∗ invSlot γE γD p.1 p.2))) )

/-- The fixed ghost names and registrations the `fupd`/`inv` layer is parametric in.
`F` is an `outParam` (determined by the chosen `WsatG` instance) so the `fupd` /
`BIFUpdate` instances on `IProp GF` resolve without mentioning `F`. -/
class WsatG (GF : BundledGFunctors) (F : outParam (Type _)) [UFraction F] where
  γI : GName
  γE : GName
  γD : GName
  [hInv : ElemG GF (FInv F)]
  [hTok : ElemG GF FTok]

attribute [instance] WsatG.hInv WsatG.hTok

end LeanliftIris.PhaseA.Fupd
