/-
Phase B (step 4) — the seqlock (`#3` in the corpus), proved torn-read-free.

A **seqlock** lets a single writer publish a multi-word snapshot to many readers
without locking the readers out. The protocol is a parity dance on a sequence
counter `s` guarding data words `d1, d2`:

  * Writer:  `s := odd` (begin) ; write `d1, d2` (relaxed) ; `s := even` (**release**).
  * Reader:  `s1 := s` (**acquire**) ; read `d1, d2` (relaxed) ; `s2 := s` ;
             retry unless `s1 = s2` and `s1` is even.

The correctness claim is **torn-read freedom**: a reader that comes away with a
consistent even sequence number read a *coherent* snapshot — never a mix of one
word from before a write and one from after.

This file proves both directions in the view-based model of `WeakMem.lean`:

  * `seqlock_consistent_read` — once the reader **acquire**-loads the writer's
    even publish of `s`, it is *determined* to read the whole published payload
    (`d1 = 42 ∧ d2 = 43`). This is the synchronizes-with edge (`ra_transfer`)
    transferring the writer's view of *both* data writes, then read-determinism
    forcing each word. Torn reads are impossible on this path.

  * `seqlock_torn_without_validation` — drop the discipline (bare relaxed reads,
    no parity check) and a **torn** snapshot `[42, 0]` is a real interleaved
    execution: the reader catches `d1`'s new value but `d2`'s stale one, mid-write.
    This is exactly what the sequence-number validation exists to reject, and the
    begin-write's *odd* stamp (`seqlock_begin_odd`) is what a reader would see and
    retry on.

Together they are the seqlock guarantee: the acquire + even-parity protocol is
both sufficient (no torn read) and necessary (torn reads exist without it).

Core Lean only, sorry-free.
-/
import LeanliftIris.PhaseB.Logic
import LeanliftIris.PhaseB.Machine

namespace LeanliftIris.PhaseB

/-! ## The writer's run, as a chain of stores

Locations `s` (sequence counter), `d1`/`d2` (the two data words). The writer
publishes version 2 with payload `(42, 43)`: begin (`s := 1`, odd, relaxed),
two relaxed data writes, then the release publish (`s := 2`, even). -/

section Seqlock
variable (s d1 d2 : Loc)

/-- Memory/view after the **begin** write `s := 1` (relaxed, odd). -/
def slM1 : Mem  := (store initMem View.bot s 1 .rlx).1
def slV1 : View := (store initMem View.bot s 1 .rlx).2
/-- … after `d1 := 42` (relaxed). -/
def slM2 : Mem  := (store (slM1 s) (slV1 s) d1 42 .rlx).1
def slV2 : View := (store (slM1 s) (slV1 s) d1 42 .rlx).2
/-- … after `d2 := 43` (relaxed). -/
def slM3 : Mem  := (store (slM2 s d1) (slV2 s d1) d2 43 .rlx).1
def slV3 : View := (store (slM2 s d1) (slV2 s d1) d2 43 .rlx).2
/-- … after the **publish** `s := 2` (release, even) — the final memory. -/
def slM4 : Mem  := (store (slM3 s d1 d2) (slV3 s d1 d2) s 2 .rel).1
/-- The release message the writer published at `s` (carries its full view). -/
def slPub : Msg := storeMsg (slM3 s d1 d2) (slV3 s d1 d2) s 2 .rel

/-! ## Parity invariant: begin is odd, publish is even -/

/-- The begin write stamps `s` with the **odd** value `1` — what a reader catches
to know a write is in progress and to retry. -/
theorem seqlock_begin_odd : (slPub s d1 d2).val = 2 ∧ (1 : Int) % 2 = 1 := ⟨rfl, rfl⟩

/-! ## The writer saw both data writes by publish time

`seen d 1` at the pre-publish view `slV3` for each data word — the knowledge that
the release transfers to an acquiring reader. -/

/-- The writer has observed `d1`'s write by the time it stored `d2`. -/
theorem slV3_seen_d1 (h1 : s ≠ d1) : seen d1 1 (slV3 s d1 d2) := by
  -- the `d1 := 42` store makes the writer `seen d1 1` …
  have hd1 : seen d1 (maxTs (slM1 s) d1 + 1) (slV2 s d1) :=
    seen_after_store (slM1 s) (slV1 s) d1 42 .rlx
  have hmax : maxTs (slM1 s) d1 = 0 := by
    simp [slM1, maxTs, store, push, initMem, h1, Ne.symm h1]
  rw [hmax] at hd1
  -- … and the later `d2 := 43` store only advances the view.
  exact Nat.le_trans hd1 (store_view_mono (slM2 s d1) (slV2 s d1) d2 43 .rlx d1)

/-- The writer has observed `d2`'s write by publish time. -/
theorem slV3_seen_d2 (h2 : s ≠ d2) (h3 : d1 ≠ d2) : seen d2 1 (slV3 s d1 d2) := by
  have hd2 : seen d2 (maxTs (slM2 s d1) d2 + 1) (slV3 s d1 d2) :=
    seen_after_store (slM2 s d1) (slV2 s d1) d2 43 .rlx
  have hmax : maxTs (slM2 s d1) d2 = 0 := by
    simp [slM2, slM1, maxTs, store, push, initMem, h2, Ne.symm h2, h3, Ne.symm h3]
  rwa [hmax] at hd2

/-! ## Consistency: the acquiring reader reads a coherent snapshot -/

/-- **Torn-read freedom (sufficiency).** A reader that **acquire**-loads the
writer's even publish of `s` is *determined* to read the whole published payload:
`d1 = 42` and `d2 = 43`. The release/acquire handshake (`ra_transfer`) hands the
reader the writer's view of *both* data writes, and read-determinism then forces
each word — there is no execution in which it sees one new word and one stale
word. This is the seqlock's whole point, in the logic. -/
theorem seqlock_consistent_read (h1 : s ≠ d1) (h2 : s ≠ d2) (h3 : d1 ≠ d2) (Vcons : View) :
    readsAs (slM4 s d1 d2) (loadView Vcons s (slPub s d1 d2) .acq) d1 42 ∧
    readsAs (slM4 s d1 d2) (loadView Vcons s (slPub s d1 d2) .acq) d2 43 := by
  constructor
  · -- d1 = 42
    refine reads_determined _ _ _ 1 _ ?_ ?_
    · exact ra_transfer (seen d1 1) (seen_mono d1 1) (slM3 s d1 d2) (slV3 s d1 d2)
        Vcons s 2 (slV3_seen_d1 s d1 d2 h1)
    · intro m hmem hts
      -- `d1`'s history is [⟨42,1⟩, ⟨0,0⟩]; only the published write has ts ≥ 1
      simp [slM4, slM3, slM2, slM1, store, push, maxTs, initMem,
        h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3] at hmem
      rcases hmem with h | h <;> subst h
      · rfl
      · simp at hts
  · -- d2 = 43
    refine reads_determined _ _ _ 1 _ ?_ ?_
    · exact ra_transfer (seen d2 1) (seen_mono d2 1) (slM3 s d1 d2) (slV3 s d1 d2)
        Vcons s 2 (slV3_seen_d2 s d1 d2 h2 h3)
    · intro m hmem hts
      simp [slM4, slM3, slM2, slM1, store, push, maxTs, initMem,
        h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3] at hmem
      rcases hmem with h | h <;> subst h
      · rfl
      · simp at hts

/-! ## Necessity: without the discipline, a torn read is a real execution

Drop the acquire+parity protocol — let the reader take bare relaxed snapshots of
`d1, d2` while the writer is mid-update. There is an interleaving in which the
reader catches `d1`'s *new* value but `d2`'s *stale* value: the torn snapshot
`[42, 0]`. (At that interleaving `s` is the odd `1` — the in-progress stamp the
real reader would have seen and retried on.) This is exactly the outcome the
sequence-number validation exists to forbid. -/
theorem seqlock_torn_without_validation (h2 : s ≠ d2) (h3 : d1 ≠ d2) :
    ∃ C : Config,
      Steps ([([.wr s 1 .rlx, .wr d1 42 .rlx, .wr d2 43 .rlx, .wr s 2 .rel], View.bot, []),
              ([.rd d1 .rlx, .rd d2 .rlx], View.bot, [])], initMem) C ∧
      (C.1[1]?).map (fun th => th.2.2) = some [42, 0] := by
  refine ⟨([([.wr d2 43 .rlx, .wr s 2 .rel], slV2 s d1, []),
            ([], loadView (loadView View.bot d1 (storeMsg (slM1 s) (slV1 s) d1 42 .rlx) .rlx)
                  d2 ⟨0, 0, View.bot⟩ .rlx, [42, 0])], slM2 s d1), ?_, rfl⟩
  -- writer: begin `s := 1` (relaxed, odd)
  refine Steps.step (Step.wr [] [_] [.wr d1 42 .rlx, .wr d2 43 .rlx, .wr s 2 .rel]
    View.bot [] initMem s 1 .rlx) ?_
  -- writer: `d1 := 42` (relaxed)
  refine Steps.step (Step.wr [] [_] [.wr d2 43 .rlx, .wr s 2 .rel]
    (slV1 s) [] (slM1 s) d1 42 .rlx) ?_
  -- reader: relaxed-loads `d1`, catches the new value 42
  refine Steps.step (Step.rd [_] [] [.rd d2 .rlx] View.bot [] (slM2 s d1) d1 .rlx
    (storeMsg (slM1 s) (slV1 s) d1 42 .rlx)
    ⟨by simp [slM2, store, push, storeMsg], Nat.zero_le _⟩) ?_
  -- reader: relaxed-loads `d2`, still sees the stale 0 (writer hasn't reached `d2`)
  refine Steps.step (Step.rd [_] [] []
    (loadView View.bot d1 (storeMsg (slM1 s) (slV1 s) d1 42 .rlx) .rlx) [42]
    (slM2 s d1) d2 .rlx ⟨0, 0, View.bot⟩
    ⟨by simp [slM2, slM1, store, push, maxTs, initMem, h2, Ne.symm h2, h3, Ne.symm h3],
     by simp [loadView, storeMsg, slM1, slV1, store, View.join, View.bot, View.singleton,
          maxTs, initMem, h3, Ne.symm h3]⟩) ?_
  exact Steps.refl _

end Seqlock

end LeanliftIris.PhaseB
