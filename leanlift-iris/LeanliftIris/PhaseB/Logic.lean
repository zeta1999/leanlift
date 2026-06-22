/-
Phase B (step 3) — the assertion layer of a weak-memory program logic.

The operational model (`WeakMem.lean`) and machine (`Machine.lean`) give the
semantics; a *program logic* reasons with assertions instead of raw views. The
cornerstone of any release/acquire logic (iRC11, GPS, FSL) is:

  **synchronizes-with** — whatever *monotone* knowledge a thread had when it did a
  release store transfers to any thread that acquire-reads that store.

Here we make that a clean, reusable rule (`ra_transfer`) over **monotone
view-assertions** (`View → Prop` closed under view growth — the "subjective"
propositions of iRC11), built on `release_acquire_hb`. We instantiate it with the
`seen` assertion ("this thread has observed location `l` up to timestamp `t`") and
re-derive message passing *in the logic* (`mp_via_logic`): after the acquire, the
consumer's assertion shows it has observed the published payload.

Core Lean only, sorry-free. This is the interface a full separation-logic
points-to (`l ↦` rel/acq) would be defined in terms of.
-/
import LeanliftIris.PhaseB.WeakMem

namespace LeanliftIris.PhaseB

/-- A subjective weak-memory assertion: a predicate on the observing thread's
view that is closed under observing *more* (monotone in the view order). -/
def Monotone (Q : View → Prop) : Prop :=
  ∀ V W : View, (∀ l, V l ≤ W l) → Q V → Q W

/-- **Release/acquire transfer (synchronizes-with).** Any monotone assertion the
releaser established at a release store is acquired by a thread that
acquire-loads that store. The program-logic form of `release_acquire_hb`. -/
theorem ra_transfer (Q : View → Prop) (hmono : Monotone Q) (M : Mem)
    (Vprod Vcons : View) (f : Loc) (v : Int) (hQ : Q Vprod) :
    Q (loadView Vcons f (storeMsg M Vprod f v .rel) .acq) :=
  hmono Vprod _ (fun l => release_acquire_hb M Vprod Vcons f v l) hQ

/-! ## The `seen` assertion -/

/-- `seen l t`: the thread has observed location `l` up to (at least) timestamp
`t`. The basic positive knowledge a reader gains. -/
def seen (l : Loc) (t : Time) : View → Prop := fun V => t ≤ V l

/-- `seen` is monotone, so it is transferable by `ra_transfer`. -/
theorem seen_mono (l : Loc) (t : Time) : Monotone (seen l t) :=
  fun _V _W hVW hV => Nat.le_trans hV (hVW l)

/-- A relaxed store makes the writer `seen` its own write. -/
theorem seen_after_store (M : Mem) (V : View) (l : Loc) (v : Int) (o : MemOrd) :
    seen l (maxTs M l + 1) (store M V l v o).2 := by
  simp only [seen, store, View.join, View.singleton, if_pos rfl]
  exact Nat.le_max_right _ _

/-! ## Message passing, derived in the logic

The producer writes `d` (gaining `seen d 1`), then release-stores `f`. By
`ra_transfer`, a consumer that acquire-loads `f` *also* has `seen d 1` — it has
observed the payload write, so its subsequent read of `d` cannot be stale. -/
theorem mp_via_logic (d f : Loc) (Vcons : View) :
    seen d 1
      (loadView Vcons f
        (storeMsg (store initMem View.bot d 42 .rlx).1
          (store initMem View.bot d 42 .rlx).2 f 1 .rel) .acq) := by
  apply ra_transfer (seen d 1) (seen_mono d 1)
  -- the producer's own view sees its `d := 42` write (timestamp 1)
  have h := seen_after_store initMem View.bot d 42 .rlx
  simpa [seen, maxTs, initMem] using h

/-! ## Read determinism: a synchronized consumer reads the published value

`readsAs M V l v` says the thread (view `V`) can only read value `v` at `l` — no
torn or stale read is possible. The key rule: if the thread has `seen l t` and
*every* write at `l` from timestamp `t` on has value `v` (the single-writer
published value), then it reads `v`. -/

/-- The thread (view `V`) is determined to read value `v` at `l`. -/
def readsAs (M : Mem) (V : View) (l : Loc) (v : Int) : Prop :=
  ∀ m, canLoad M V l m → m.val = v

/-- **Read-determinism.** Synchronization (`seen l t`) plus a single published
value from timestamp `t` on forces the read. -/
theorem reads_determined (M : Mem) (V : View) (l : Loc) (t : Time) (v : Int)
    (hseen : seen l t V) (hwrites : ∀ m, m ∈ M l → t ≤ m.ts → m.val = v) :
    readsAs M V l v := by
  intro m hm
  obtain ⟨hmem, hts⟩ := hm
  exact hwrites m hmem (Nat.le_trans hseen hts)

/-- **Full SPSC ring guarantee, in the logic.** After the producer publishes
`d := 42` (rlx) ; `f := 1` (rel), a consumer that acquire-loads `f` is
*determined* to read the payload `42` at `d` — it cannot read the stale initial
value. This composes `ra_transfer` (synchronizes-with) and `reads_determined`,
proving the corpus' SPSC ring (`spsc_ring.hpp`) handoff entirely in the
weak-memory program logic. -/
theorem spsc_consumer_reads_payload (d f : Loc) (hdf : d ≠ f) (Vcons : View) :
    readsAs
      ((store (store initMem View.bot d 42 .rlx).1
          (store initMem View.bot d 42 .rlx).2 f 1 .rel).1)
      (loadView Vcons f
        (storeMsg (store initMem View.bot d 42 .rlx).1
          (store initMem View.bot d 42 .rlx).2 f 1 .rel) .acq) d 42 := by
  refine reads_determined _ _ _ 1 _ (mp_via_logic d f Vcons) ?_
  intro m hmem hts
  simp [store, push, maxTs, initMem, hdf, Ne.symm hdf] at hmem
  rcases hmem with h | h <;> subst h
  · rfl
  · simp at hts

end LeanliftIris.PhaseB
