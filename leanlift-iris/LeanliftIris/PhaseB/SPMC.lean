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

And it closes the ordering question the SPSC handshake left implicit — **the
payload read must be ordered after the stamp acquire**:

  * `spmc_acq_ordered_reads_fresh` — the *positive* direction restated: a payload
    read taken from the post-acquire view (`loadView … s … .acq`) is determined to
    read the freshest payload `200`, even across the lap (this is `spmc_reads_latest`).
  * `spmc_relaxed_lap_in_flight` — the *necessity*: a payload read **not** ordered
    after the acquire (an unsynchronized relaxed load, view `⊥`) still admits the
    lapped/stale value `100` after the producer has moved on to round 1. So the
    stamp check alone is not enough — the data read genuinely must be ordered by
    the acquire (acquire-load / consume-dependency / acquire fence).

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

/-! ## The payload read must be ordered after the stamp acquire

`spmc_reads_latest` already shows the *positive* direction — a payload read taken
from the **post-acquire view** reads the freshest value across the lap. We restate
it under a name that makes the ordering explicit, then prove its converse: drop
the ordering and the lap-in-flight hazard is real. -/

/-- **Acquire-ordered ⇒ fresh.** A consumer whose payload read starts from the
view it gained by acquire-loading the round-1 stamp is determined to read the
newest payload `200` — the ordering after the acquire is exactly what defeats the
lap. (Same statement as `spmc_reads_latest`, named for the ordering it relies on.) -/
theorem spmc_acq_ordered_reads_fresh (hds : d ≠ s) (Vc : View) :
    readsAs (r1M2 d s) (loadView Vc s (r1Pub d s) .acq) d 200 :=
  spmc_reads_latest d s hds Vc

/-- **The ordering is necessary — lap in flight.** If the payload read is *not*
ordered after the stamp acquire (modeled as an unsynchronized relaxed load from
the bottom view), then even after the producer has lapped to round 1 the consumer
can still load the round-0 payload `100`. So a consumer that validates against the
round-1 stamp but reads the payload with an unordered relaxed load may pair the
new stamp with stale bytes: the stamp check alone does **not** defend the payload —
the data read must be ordered by the acquire. (Cf. `mp_relaxed_admits_stale`.) -/
theorem spmc_relaxed_lap_in_flight (hds : d ≠ s) :
    ∃ m : Msg, canLoad (r1M2 d s) View.bot d m ∧ m.val = 100 := by
  refine ⟨storeMsg initMem View.bot d 100 .rlx, ⟨?_, ?_⟩, rfl⟩
  · -- the round-0 payload write is still in `d`'s history after the lap
    simp [r1M2, r1M1, r0M2, r0M1, storeMsg, store, push, maxTs, initMem, hds, Ne.symm hds]
  · -- the bottom view imposes no lower bound at `d`
    exact Nat.zero_le _

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
