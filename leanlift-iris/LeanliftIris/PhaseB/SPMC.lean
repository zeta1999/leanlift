/-
Phase B (step 7) — the SPMC broadcast ring (`#5`): a per-slot stamp seqlock where
the slot is **reused** (lapped) by the single producer.

The SPSC ring (`Logic.lean`) and the seqlock (`Seqlock.lean`) publish *once*. A
broadcast ring's distinguishing feature is **overrun**: the single producer keeps
writing, so a slot is overwritten round after round, and a slow consumer must be
able to tell that the data under a stale stamp has been lapped. Each slot carries
a monotone **sequence stamp**; the producer writes payload (relaxed) then bumps
the stamp (release); a consumer for round `r` acquire-reads the stamp and accepts
the payload only when the stamp matches `r`'s.

This file models one slot across two rounds (`d` payload, `s` stamp; round 0
publishes `100`@stamp 1, round 1 laps with `200`@stamp 2) and proves the three
facts that make the ring correct:

  * `spmc_consumer_reads_round0` — **pre-lap consistency**: before the lap, a
    consumer that acquire-reads stamp `1` is *determined* to read round-0's
    payload `100` (the message-passing handshake, as in SPSC/seqlock).
  * `spmc_reads_latest` — **freshest-wins**: after the lap, a consumer that
    acquire-reads the new stamp is *determined* to read the newest payload `200`.
  * `spmc_stamp_advances` — **overrun is observable**: every republish takes a
    strictly greater stamp (`store_ts_fresh`), so a consumer that re-reads the
    stamp sees it change and knows its slot was lapped — it never silently accepts
    stale data.

Scope note: this captures the stamp/overrun mechanism honestly; it does *not*
claim the double-stamp check alone defends a *relaxed* payload read against a lap
in flight (that needs the data read ordered by the acquire, a separate argument).
Core Lean only, sorry-free.
-/
import LeanliftIris.PhaseB.Logic

namespace LeanliftIris.PhaseB

section SPMC
variable (d s : Loc)

/-! ## The producer's two rounds over one slot -/

/-- Round 0: payload `d := 100` (relaxed). -/
def r0M1 : Mem  := (store initMem View.bot d 100 .rlx).1
def r0V1 : View := (store initMem View.bot d 100 .rlx).2
/-- Round 0 publish: stamp `s := 1` (release). -/
def r0M2 : Mem  := (store (r0M1 d) (r0V1 d) s 1 .rel).1
def r0V2 : View := (store (r0M1 d) (r0V1 d) s 1 .rel).2
/-- The round-0 stamp message published at `s`. -/
def r0Pub : Msg := storeMsg (r0M1 d) (r0V1 d) s 1 .rel
/-- Round 1 (lap): payload `d := 200` (relaxed), reusing the slot. -/
def r1M1 : Mem  := (store (r0M2 d s) (r0V2 d s) d 200 .rlx).1
def r1V1 : View := (store (r0M2 d s) (r0V2 d s) d 200 .rlx).2
/-- Round 1 publish: stamp `s := 2` (release) — the final memory. -/
def r1M2 : Mem  := (store (r1M1 d s) (r1V1 d s) s 2 .rel).1
/-- The round-1 stamp message. -/
def r1Pub : Msg := storeMsg (r1M1 d s) (r1V1 d s) s 2 .rel

/-! ## Pre-lap consistency -/

/-- The producer has observed its round-0 payload by round-0 publish time. -/
theorem r0V1_seen_d : seen d 1 (r0V1 d) := by
  have h : seen d (maxTs initMem d + 1) (r0V1 d) := seen_after_store initMem View.bot d 100 .rlx
  have hmax : maxTs initMem d = 0 := by simp [maxTs, initMem]
  rwa [hmax] at h

/-- **Pre-lap consistency.** Before the lap, a consumer that acquire-loads the
round-0 stamp publish is *determined* to read round-0's payload `100` — the
ordinary release/acquire handshake. -/
theorem spmc_consumer_reads_round0 (hds : d ≠ s) (Vc : View) :
    readsAs (r0M2 d s) (loadView Vc s (r0Pub d s) .acq) d 100 := by
  refine reads_determined _ _ _ 1 _ ?_ ?_
  · exact ra_transfer (seen d 1) (seen_mono d 1) (r0M1 d) (r0V1 d) Vc s 1 (r0V1_seen_d d)
  · intro m hmem hts
    simp [r0M2, r0M1, store, push, maxTs, initMem, hds, Ne.symm hds] at hmem
    rcases hmem with h | h <;> subst h
    · rfl
    · simp at hts

/-! ## Freshest-wins after a lap -/

/-- The producer has observed its round-1 (lapped) payload by round-1 publish. -/
theorem r1V1_seen_d (hds : d ≠ s) : seen d 2 (r1V1 d s) := by
  have h : seen d (maxTs (r0M2 d s) d + 1) (r1V1 d s) :=
    seen_after_store (r0M2 d s) (r0V2 d s) d 200 .rlx
  have hmax : maxTs (r0M2 d s) d = 1 := by
    simp [r0M2, r0M1, maxTs, store, push, initMem, hds, Ne.symm hds]
  rwa [hmax] at h

/-- **Freshest-wins.** After the lap, a consumer that acquire-loads the round-1
stamp publish is *determined* to read the newest payload `200` — the slot's reuse
does not produce a torn read on the synchronized path. -/
theorem spmc_reads_latest (hds : d ≠ s) (Vc : View) :
    readsAs (r1M2 d s) (loadView Vc s (r1Pub d s) .acq) d 200 := by
  refine reads_determined _ _ _ 2 _ ?_ ?_
  · exact ra_transfer (seen d 2) (seen_mono d 2) (r1M1 d s) (r1V1 d s) Vc s 2 (r1V1_seen_d d s hds)
  · intro m hmem hts
    simp [r1M2, r1M1, r0M2, r0M1, store, push, maxTs, initMem, hds, Ne.symm hds] at hmem
    rcases hmem with h | h | h <;> subst h
    · rfl
    · simp at hts
    · simp at hts

/-! ## Overrun is observable -/

/-- **Overrun is observable.** Each republish of the slot takes a strictly greater
stamp timestamp than the previous round's. So a consumer that re-reads the stamp
after the producer has lapped *sees it change* — the per-slot stamp lets a slow
consumer detect that its data was overwritten, instead of silently accepting
stale bytes. (Coherence, via `store_ts_fresh`.) -/
theorem spmc_stamp_advances (hds : d ≠ s) : (r0Pub d s).ts < (r1Pub d s).ts := by
  apply store_ts_fresh (r1M1 d s) (r1V1 d s) s 2 .rel
  simp [r1M1, r0M2, r0M1, r0Pub, storeMsg, store, push, maxTs, initMem, hds, Ne.symm hds]

end SPMC

end LeanliftIris.PhaseB
