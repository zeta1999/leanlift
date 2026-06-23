# PLAN — fancy-update (`fupd`), invariants, and true logical atomicity

Goal: give `IProp GF` a **fancy-update modality** `|={E1,E2}=> P` and **invariants**
`inv N P`, so that the upstream `BIFUpdate (IProp GF) Nat` typeclass is *instantiated*
and Iris-style logically-atomic triples `<<< P >>> e <<< Q >>>` become **expressible**
over our `λ-conc` program logic.

This mirrors upstream Iris `base_logic/lib/{wsat,fancy_updates,invariants}.v`, adapted to
what iris-lean actually ships.

## What iris-lean already gives us (verified against `.lake/packages/iris`)

- `BIFUpdate PROP MASK` / `FUpd PROP MASK` classes **already declared** with the 5 laws
  (`subset`, `except0`, `trans`, `mask_frame_r'`, `frame_r`) and `ne`
  (`Iris/BI/Updates.lean`). **No `IProp` instance exists** — that is our target.
  Masks are `Set MASK := MASK → Prop`, with `Set.univ`, `Subset`, `Disjoint`, `union`.
- `iOwn`, `iOwn_alloc(_dep)`, `iOwn_op`, `iOwn_mono`, `iOwn_cmraValid`,
  `iOwn_update` (`a ~~> a' ⟹ iOwn γ a ⊢ |==> iOwn γ a'`), `iOwn_updateP`, `iOwn_unit`.
- bupd `|==>` with `BIUpdate (IProp GF)`; `◇`, `▷`, `□`, `∗`, `-∗`, `⌜⌝`.
- Algebras: `Excl`, `Agree`/`toAgree`/`toAgree_op_valid_iff_equiv`, `GenMap`
  (`singleton_map_op`, `valid_exists_fresh`), `Auth`/`View` (`both_validN`, `frag_op`,
  `auth_update`, `auth_update_alloc`).
- Functor combinators: `constOF`, `AgreeRF`, `GenMapOF Nat`, `AuthRF`, `LaterOF`,
  `Later.next` (contractive). Contractivity preserved through `AgreeRF`/`GenMapOF`/`AuthRF`.

## Gaps we must build first (iris-lean does NOT ship these)

1. **No identity functor** and `LaterOF` only *preserves* contractivity (its only
   `OFunctorContractive` instance requires the argument already contractive). To store
   `▷ (IProp GF)` we need `idOF` + a direct `OFunctorContractive (LaterOF idOF)`
   ("later introduces contractivity"). → `Fupd/Functors.lean`.
2. **No internal-equality connective** `≡` in the BI. Saved-prop/invariant agreement
   needs `▷ (P ≡ Q)` and an `internal_eq_rewrite`. We define a minimal `iEq` for IProp
   directly at the `UPred` model level. → `Fupd/IEq.lean`.
3. **No big-sep over maps/sets** — only `bigOp`/`bigSep` over `List PROP`. We model the
   invariant world as an association list and build the `insert`/`delete`/`lookup`
   separation lemmas we need. → `Fupd/BigSep.lean`.
4. **Mask difference** `E ∖ E'` is undefined — add it plus the set-algebra lemmas.

## Hard design constraint — the `⊤` mask

`GenMap Nat β` validity requires **infinitely many free keys** (`Infinite (IsFree car)`),
so a `GenMap Nat (Excl Unit)` token set **cannot represent `⊤`** (or any cofinite mask):
`ownE ⊤ ⊢ False`. Consequence: the `BIFUpdate` instance is **sound** (the 5 laws are
relative and hold; bad-mask cases are vacuous), and invariant access works for **finite
masks** (`E`, `E ∖ ↑N` finite). Wiring `fupd` into `wp`/adequacy (which forces `ownE ⊤`)
is **out of scope** here; logically-atomic triples carry an explicit mask `E`, so goal #5
(expressibility of `<<<P>>> e @ E <<<Q>>>`) is unaffected. This is documented at each
affected definition.

## The five pieces (each its own sorry-free commit; strict CI gate, no `sorry`/`admit`)

Files live under `leanlift-iris/LeanliftIris/PhaseA/Fupd/`, wired into `LeanliftIris.lean`.

- **0. Infra** (`Functors.lean`, `IEq.lean`, `BigSep.lean`): `idOF` + later-contractivity;
  `iEq`/`internal_eq_rewrite`/`later_equivI`; `bigSepL` insert/delete/lookup lemmas.
- **1. Mask tokens** (`Masks.lean`): `FEnabled = FDisabled = constOF (GenMap Nat (Excl Unit))`,
  registered via `ElemG`. `ownE E`, `ownD D` (classical token maps). Lemmas: `ownE_empty`,
  `ownE_op` (disjoint split), `ownE_disjoint` (Excl exclusivity ⟹ `Disjoint`), singletons;
  same for `ownD`. Reuses existing algebra — most self-contained.
- **2. Invariant authority** (`Wsat.lean`, part A): `FInv =
  AuthRF (GenMapOF Nat (AgreeRF (LaterOF idOF)))`, registered. `invAuth I`,
  `ownI i P := iOwn γI (◯ singleton i (toAgree (next P)))`. Persistence of `ownI`;
  agreement `ownI i P ∗ ownI i Q ⊢ ▷ (P ≡ Q)` (via `iEq` + `toAgree_op_valid_iff_equiv`).
- **3. wsat** (`Wsat.lean`, part B): `wsat := ∃ I, invAuth I ∗
  [∗ list] (i,Q) ∈ I, (▷ Q ∗ ownD {i}) ∨ ownE {i}`, with the open/close element lemmas
  (`wsat_open i`, `wsat_close i`) built on the `BigSep` delete/insert lemmas.
- **4. fupd + BIFUpdate** (`Fupd.lean`): `fupd E1 E2 P := wsat ∗ ownE E1 -∗
  |==> ◇ (wsat ∗ ownE E2 ∗ P)`; prove `ne` + the 5 laws; register
  `instance : BIFUpdate (IProp GF) Nat`. The intricate core.
- **5. inv + LAT** (`Inv.lean`): `inv N P := □ ∀ E, ⌜↑N ⊆ E⌝ →
  |={E, E∖↑N}=> ▷ P ∗ (▷ P ={E∖↑N, E}=∗ emp)`; `inv_alloc`, `inv_acc`. Then the
  logically-atomic triple `<<< P >>> e @ E <<< Q >>>` (Texan-style notation) is definable
  and `inv`-clients typecheck. Namespaces `N` modelled as finite `Set Nat` (`↑N` finite).

## STATUS (live) — all five pieces landed, sorry-free

- **Infra:** `Functors.lean` (`idOF`, `LaterS`, `FProp`); `IEq.lean` (internal equality
  `iEq` + `iEq_elim`/`agree_iEq`/`iEq_laterS_fwd`).
- **Piece 1** `Masks.lean` — `ownE`/`ownD`, splitting/exclusivity, `mdiff`,
  `ownE_subset_split`, `ownE_disjoint_keep`.
- **Piece 2** `InvRes.lean` — `invAuth`, `ownI` (persistent), `invAuth_lookup`.
- **Piece 3** `Wsat.lean` — `wsat` + `WsatG` (fixed ghost names, `F` outParam).
- **Piece 4** `Fupd.lean` — `fupd` + all five laws (`frame_r`, `except0`, `trans`,
  `subset`, `mask_frame_r'`) + `ne`; **`instance : BIFUpdate (IProp GF) Nat`**.
- **Piece 5** `Inv.lean` — `inv` (persistent), `bigSep_map_extract` (slot surgery),
  `ownI_open` / `ownI_close` (wsat open/close), **`inv_acc`** (the full invariant-access
  law, finite masks), **`atomic_acc`** (logically-atomic accessor → `<<<…>>>` triples
  now expressible). Agreement/transport: `ownI_agree`, `iEq_later_transport(’)`,
  `invAuth_lookup_keep`, `toMap_mem`.

**Two iris-lean blockers found & fixed in-repo:** (1) `Auth.lean` not built → used the
built `HeapView.HeapViewURF`; (2) `Later : Type (u+1)` bumps the universe while `iOwn`
is universe-0-monomorphic → `LaterS` (`Type u`, same `DistLater` OFE).

**Remaining (one lemma):** `inv_alloc` (invariant *creation*). Needs a fresh
disabled-token allocation: a GenMap frame-preserving `updateP` minting `ownD {i}` for an
`i` fresh in both the `γD` frame and `dom (toMap L)`. That rests on a list pigeonhole
(`injective enum → ∃ k, enum k ∉ X`) which is **not in Lean core and there is no Mathlib
dependency**, so it must be proven from primitives (`GenMap.Enum` + a `Nodup`/length
counting lemma) — a self-contained sub-development. Everything else (incl. the harder
`inv_acc` open/close) is done sorry-free.

## Order of work / commits

infra (`Functors` → `IEq` → `BigSep`) → `Masks` (piece 1) → `Wsat` auth (piece 2) →
`wsat` (piece 3) → `Fupd`+instance (piece 4) → `Inv`+LAT (piece 5). Build with
`cd leanlift-iris && lake build`; gate with `lake env lean CiAxioms.lean` (no `sorryAx`).
Commit each compiling, sorry-free file directly to `main`.
