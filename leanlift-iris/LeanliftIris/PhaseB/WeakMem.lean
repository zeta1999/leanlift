/-
Phase B (step 1) — a view-based release/acquire weak-memory model for `λ-conc`.

Phase A's semantics is sequentially consistent; the corpus' interesting members
(SPSC ring #1, seqlock #3, SPMC #5, Chase–Lev #8) are *weak-memory* and cannot be
expressed there. This file starts the weak-memory layer with the standard
view-based operational model (à la iRC11 / ORC11):

  * every location carries a **modification order** — a history of write messages,
    each with a timestamp and a *released view*;
  * every thread has a **view** — the latest timestamp it has observed per
    location;
  * a **release** store attaches the writer's view to its message; an **acquire**
    load absorbs the message's view; **relaxed** accesses only move the
    single-location timestamp.

We validate the model on the **message-passing (MP)** litmus — the publish-then-
read edge that the corpus' SPSC ring (`spsc_ring.hpp`) relies on: *"the payload
write is published before the counter advance (release), observed by the other
side (acquire)."* The theorem `message_passing` shows that after that
release/acquire handshake, the consumer is *forced* to observe the published
payload (it cannot read the stale initial value).

Core Lean only (no Iris): this is the operational substrate a weak-memory program
logic (B2) will later be built over. Sorry-free.
-/
namespace LeanliftIris.PhaseB

/-- C11 memory orderings (the subset the corpus uses). -/
inductive MemOrd | rlx | rel | acq | sc
deriving DecidableEq, Repr

abbrev Time := Nat
abbrev Loc := Nat

/-- A thread/message **view**: the latest timestamp observed per location. -/
abbrev View := Loc → Time

namespace View
/-- The initial view — nothing observed. -/
def bot : View := fun _ => 0
/-- Pointwise max (the join of the observation lattice). -/
def join (V W : View) : View := fun l => max (V l) (W l)
/-- The view that has observed exactly timestamp `t` at `l`. -/
def singleton (l : Loc) (t : Time) : View := fun l' => if l' = l then t else 0
end View

/-- A write **message** in a location's modification order. -/
structure Msg where
  val   : Int
  ts    : Time
  /-- the view this write releases (carried to acquire-readers). -/
  rview : View

/-- **Memory**: each location's modification order (newest first). -/
abbrev Mem := Loc → List Msg

/-- The empty/initial memory: every location holds a single value-`0` write at
timestamp `0` with the bottom view. -/
def initMem : Mem := fun _ => [⟨0, 0, View.bot⟩]

/-- The greatest timestamp currently written at `l`. -/
def maxTs (M : Mem) (l : Loc) : Time := (M l).foldl (fun acc m => max acc m.ts) 0

/-- Append a message to `l`'s history. -/
def push (M : Mem) (l : Loc) (m : Msg) : Mem :=
  fun l' => if l' = l then m :: M l' else M l'

/-- **Store** of `v` at `l` with ordering `o` by a thread with view `V`. Picks a
fresh timestamp after every existing write; a release/seq-cst store attaches the
writer's full view, a relaxed store only its own new timestamp. Returns the new
memory and the writer's advanced view. -/
def store (M : Mem) (V : View) (l : Loc) (v : Int) (o : MemOrd) : Mem × View :=
  let t := maxTs M l + 1
  let base : View := if o = .rel ∨ o = .sc then V else View.bot
  let rv := View.join base (View.singleton l t)
  (push M l ⟨v, t, rv⟩, View.join V (View.singleton l t))

/-- A thread with view `V` may **load** message `m` from `l` iff `m` is in the
history and is not older than what the thread has already observed there. -/
def canLoad (M : Mem) (V : View) (l : Loc) (m : Msg) : Prop :=
  m ∈ M l ∧ V l ≤ m.ts

/-- The view a thread holds after loading `m` from `l` with ordering `o`: an
acquire/seq-cst load absorbs `m`'s released view, a relaxed load only the
single-location timestamp. -/
def loadView (V : View) (l : Loc) (m : Msg) (o : MemOrd) : View :=
  View.join V (if o = .acq ∨ o = .sc then m.rview else View.singleton l m.ts)

/-- The message a `store` creates (exposed for synchronization reasoning). -/
def storeMsg (M : Mem) (V : View) (l : Loc) (v : Int) (o : MemOrd) : Msg :=
  let t := maxTs M l + 1
  ⟨v, t, View.join (if o = .rel ∨ o = .sc then V else View.bot) (View.singleton l t)⟩

/-! ## Coherence: per-location writes are totally ordered by timestamp -/

private theorem foldl_acc_ge :
    ∀ (xs : List Msg) (acc : Time), acc ≤ xs.foldl (fun a m => max a m.ts) acc := by
  intro xs
  induction xs with
  | nil => intro acc; exact Nat.le_refl _
  | cons x xs ih => intro acc; exact Nat.le_trans (Nat.le_max_left acc x.ts) (ih (max acc x.ts))

private theorem foldl_max_ts_ge {m : Msg} :
    ∀ (xs : List Msg) (acc : Time), m ∈ xs → m.ts ≤ xs.foldl (fun a m => max a m.ts) acc := by
  intro xs
  induction xs with
  | nil => intro acc h; cases h
  | cons x xs ih =>
    intro acc h
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact Nat.le_trans (Nat.le_max_right acc x.ts) (foldl_acc_ge xs (max acc x.ts))
    · exact ih (max acc x.ts) h

/-- Every write in `l`'s history has a timestamp `≤` the location's maximum. -/
theorem mem_ts_le_maxTs (M : Mem) (l : Loc) (m : Msg) (h : m ∈ M l) : m.ts ≤ maxTs M l :=
  foldl_max_ts_ge (M l) 0 h

/-- **Coherence.** A new store gets a fresh timestamp, strictly greater than every
existing write to that location — so each location's modification order is a total
order, and the store is its new latest write. -/
theorem store_ts_fresh (M : Mem) (V : View) (l : Loc) (v : Int) (o : MemOrd)
    (m : Msg) (h : m ∈ M l) : m.ts < (storeMsg M V l v o).ts := by
  have hle := mem_ts_le_maxTs M l m h
  have hts : (storeMsg M V l v o).ts = maxTs M l + 1 := rfl
  rw [hts]; exact Nat.lt_succ_of_le hle

/-! ## Foundational view lemmas

A store/load only ever *advances* a thread's view (observations are monotone),
and a release/acquire handshake transfers the releaser's whole view to the
acquirer — the happens-before edge weak-memory correctness rests on. -/

/-- A store only advances the writer's view. -/
theorem store_view_mono (M : Mem) (V : View) (l : Loc) (v : Int) (o : MemOrd) (l' : Loc) :
    V l' ≤ (store M V l v o).2 l' := by
  simp only [store, View.join]; exact Nat.le_max_left _ _

/-- A load only advances the reader's view. -/
theorem loadView_mono (V : View) (l : Loc) (m : Msg) (o : MemOrd) (l' : Loc) :
    V l' ≤ loadView V l m o l' := by
  simp only [loadView, View.join]; exact Nat.le_max_left _ _

/-- **Release/acquire happens-before.** After acquire-loading a release-store, the
acquirer's view dominates everything the releaser had observed: `Vprod ≤
loadView Vcons f (release-msg) acq`. This is the general synchronization theorem
— message passing is the special case where what the releaser observed includes a
prior data write. -/
theorem release_acquire_hb (M : Mem) (Vprod Vcons : View) (f : Loc) (v : Int) (l : Loc) :
    Vprod l ≤ loadView Vcons f (storeMsg M Vprod f v .rel) .acq l := by
  have h1 : (storeMsg M Vprod f v .rel).rview
      = View.join Vprod (View.singleton f (maxTs M f + 1)) := by simp [storeMsg]
  have h2 : loadView Vcons f (storeMsg M Vprod f v .rel) .acq
      = View.join Vcons ((storeMsg M Vprod f v .rel).rview) := by simp [loadView]
  rw [h2, h1]
  simp only [View.join]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-! ## Message passing (the SPSC publish-then-read edge)

Locations `d` (data/payload) and `f` (flag/counter). Producer: write `d := 42`
relaxed, then `f := 1` **release**. Consumer: **acquire**-load `f`, then load
`d`. Claim: once the consumer has acquire-read the producer's release write, any
`d`-message it can still read carries the published value `42` — never the stale
initial `0`. -/

section MP
variable (d f : Loc)

/-- Memory after the producer's two writes (`d := 42` relaxed, `f := 1` release).
-/
def mpMem : Mem :=
  let (M1, V1) := store initMem View.bot d 42 .rlx
  (store M1 V1 f 1 .rel).1

/-- The producer's view after both writes. -/
def mpProdView : View :=
  let (_, V1) := store initMem View.bot d 42 .rlx
  (store (store initMem View.bot d 42 .rlx).1 V1 f 1 .rel).2

/-- The release message the producer published at the flag `f`. -/
def mpFlagMsg : Msg :=
  let (M1, V1) := store initMem View.bot d 42 .rlx
  ⟨1, maxTs M1 f + 1, View.join V1 (View.singleton f (maxTs M1 f + 1))⟩

/-- **Message passing.** After the consumer (starting from the bottom view)
acquire-loads the producer's release write on `f`, every `d`-message it can then
load carries the published value `42`. The release/acquire handshake forces the
payload to be visible — exactly the SPSC ring's correctness argument. -/
theorem message_passing (hdf : d ≠ f) :
    ∀ m : Msg,
      canLoad (mpMem d f) (loadView View.bot f (mpFlagMsg d f) .acq) d m → m.val = 42 := by
  intro m hm
  obtain ⟨hmem, hts⟩ := hm
  -- the consumer's observed timestamp at `d` is 1 (gained via the acquire load)
  have hview : loadView View.bot f (mpFlagMsg d f) .acq d = 1 := by
    simp [loadView, mpFlagMsg, store, View.join, View.bot, View.singleton, maxTs,
      initMem, push, hdf, Ne.symm hdf]
  rw [hview] at hts
  -- `d`'s history is [⟨42,1,_⟩, ⟨0,0,bot⟩]; only the ts-1 (published) write has 1 ≤ ts
  simp [mpMem, store, push, maxTs, initMem, hdf, Ne.symm hdf] at hmem
  rcases hmem with h | h <;> subst h
  · rfl
  · simp at hts

/-- **Acquire is necessary.** If the consumer loads the flag `f` only *relaxed*
(not acquire), it gains nothing at `d`, so it may still read the **stale** initial
`0` — the message-passing guarantee fails. This is the genuine weakness the model
must (and does) exhibit: `rlx ≠ acq`. -/
theorem mp_relaxed_admits_stale (hdf : d ≠ f) :
    ∃ m : Msg,
      canLoad (mpMem d f) (loadView View.bot f (mpFlagMsg d f) .rlx) d m ∧ m.val = 0 := by
  refine ⟨⟨0, 0, View.bot⟩, ⟨?_, ?_⟩, rfl⟩
  · -- the stale initial write is still in `d`'s history
    simp [mpMem, store, push, maxTs, initMem, hdf, Ne.symm hdf]
  · -- a relaxed load of `f` leaves the consumer's view at `d` equal to 0
    simp [loadView, mpFlagMsg, store, View.join, View.bot, View.singleton, maxTs,
      initMem, push, hdf, Ne.symm hdf]

/-- **Release is necessary.** If the producer stores the flag `f` only *relaxed*
(not release), its write carries no view, so even an *acquire*-load of `f` gives
the consumer nothing at `d` — it may still read the stale initial `0`. Symmetric
to `mp_relaxed_admits_stale`: message passing needs **both** a release store and
an acquire load. -/
theorem mp_release_necessary (hdf : d ≠ f) :
    ∃ m : Msg,
      canLoad
          ((store (store initMem View.bot d 42 .rlx).1
              (store initMem View.bot d 42 .rlx).2 f 1 .rlx).1)
          (loadView View.bot f
            (storeMsg (store initMem View.bot d 42 .rlx).1
              (store initMem View.bot d 42 .rlx).2 f 1 .rlx) .acq) d m ∧ m.val = 0 := by
  refine ⟨⟨0, 0, View.bot⟩, ⟨?_, ?_⟩, rfl⟩
  · -- the stale initial write is still in `d`'s history
    simp [store, push, maxTs, initMem, hdf, Ne.symm hdf]
  · -- a relaxed flag store carries no view, so the acquire load gains nothing at `d`
    simp [loadView, storeMsg, store, View.join, View.bot, View.singleton, maxTs,
      initMem, push, hdf, Ne.symm hdf]

end MP

end LeanliftIris.PhaseB
