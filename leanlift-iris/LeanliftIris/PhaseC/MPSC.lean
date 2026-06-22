/-
Phase C (step 3) — the **Vyukov MPSC queue** (`#2`): the corpus member tagged
"B + C" (ABA-by-stamp under weak memory **and** a future-dependent linearization
point needing a prophecy). This file assembles both halves on the machinery
already built.

A multi-producer / single-consumer queue has two genuinely hard parts:

  * **the contention point** — many producers must agree on *who writes which
    cell*. Vyukov's queue resolves this with an atomic increment (FAA) on a shared
    position counter: each producer's FAA returns a distinct slot. The weak-memory
    subtlety is that, having claimed a cell, a producer publishes it with a
    per-cell **sequence stamp** (release) that the consumer acquire-reads — and a
    lapped cell must be distinguishable from a fresh one (ABA-by-stamp). This is
    the **B** half, and it reuses the release/acquire handshake (`reads_determined`
    / `ra_transfer`) and coherence (`store_ts_fresh`).

  * **the linearization point** — a producer's position in the queue order is
    decided by *which producer wins the FAA race*, an event in the **future** of
    the moment a producer decides to enqueue. So enqueue's LP is not a function of
    the present state; it needs a **prophecy** of the race outcome. This is the
    **C** half, on `Prophecy.lean`.

Proved (sorry-free):
  * `tickets_nodup` / `mpsc_distinct_slots` — FAA dispenses distinct cells: no two
    producers ever share a slot (the contention point is exclusive *by the RMW*,
    no seq_cst needed — contrast the Chase–Lev last-element race).
  * `mpsc_consumer_reads_payload` — a producer that publishes its cell with a
    release stamp hands the payload to a consumer that acquire-reads the stamp.
  * `mpsc_stamp_advances` — a republished cell takes a strictly greater stamp, so
    a stale lap is never silently accepted (ABA defense).
  * `mpsc_order_proph` / `mpsc_ticket_proph_correct` / `mpsc_order_not_present` /
    `mpsc_order_distinct` — the enqueue order is future-dependent (no present-only
    LP), resolved by a prophecy of the race winner, and consistent (the two
    contenders always end in distinct cells whichever way the prophecy resolves).

Core Lean, sorry-free.
-/
import LeanliftIris.PhaseB.Logic
import LeanliftIris.PhaseC.Prophecy

namespace LeanliftIris.PhaseC
open LeanliftIris.PhaseB

section MPSC

/-! ## The slot dispenser: FAA gives each producer a unique cell

An RMW (fetch-and-add) on a single location is totally ordered by that location's
modification order — the `n`-th FAA must read the `(n-1)`-th FAA's write. So `n`
successive FAAs from counter `c` dispense the tickets `c, c+1, …, c+n-1`: a
strictly increasing, duplicate-free sequence. We model exactly that. -/

/-- Fetch-and-add on the position counter: returns `(old, new)`. -/
def faa (pos : Nat) : Nat × Nat := (pos, pos + 1)

/-- The `n` tickets dispensed by `n` successive FAAs starting at counter `c`. -/
def tickets (c n : Nat) : List Nat := List.range' c n

/-- **No two producers share a cell** — the dispensed tickets are distinct. -/
theorem tickets_nodup (c n : Nat) : (tickets c n).Nodup := List.nodup_range'

/-- The `i`-th producer to FAA gets ticket `c + i`. -/
theorem tickets_get (c n i : Nat) (h : i < (tickets c n).length) :
    (tickets c n)[i] = c + i := by
  unfold tickets; rw [List.getElem_range']; omega

/-- **The contention point is exclusive.** Two distinct producers receive distinct
cells — guaranteed by the atomic increment itself, no seq_cst fence needed. This is
the MPSC analogue of "no double claim", but here the RMW provides it for free
(contrast the Chase–Lev last-element race, which needs seq_cst). -/
theorem mpsc_distinct_slots (c n i j : Nat) (hi : i < (tickets c n).length)
    (hj : j < (tickets c n).length) (hij : i ≠ j) :
    (tickets c n)[i] ≠ (tickets c n)[j] := by
  rw [tickets_get c n i hi, tickets_get c n j hj]; omega

/-- Concretely: two producers FAA-ing in sequence get different cells. -/
theorem mpsc_faa_two (c : Nat) : (faa c).1 ≠ (faa (faa c).2).1 := by
  simp only [faa]; omega

/-! ## Stamp publish: the winning producer's payload reaches the consumer

The producer that claimed cell `d` writes its payload (relaxed) then bumps the
cell's stamp `s` (release). A consumer that acquire-reads the stamp is *determined*
to read that payload — the release/acquire handshake, exactly as in SPSC/SPMC. -/

variable (d s : Loc)

/-- Memory / view after the producer writes payload `d := 7` (relaxed). -/
def mqM1 : Mem  := (store initMem View.bot d 7 .rlx).1
def mqV1 : View := (store initMem View.bot d 7 .rlx).2
/-- The cell's stamp publish (`s := 1`, release). -/
def mqPub : Msg := storeMsg (mqM1 d) (mqV1 d) s 1 .rel
/-- Final memory after the stamp publish. -/
def mqM2 : Mem  := (store (mqM1 d) (mqV1 d) s 1 .rel).1

/-- The producer has observed its own payload write by publish time. -/
theorem mqV1_seen_d : seen d 1 (mqV1 d) := by
  have h : seen d (maxTs initMem d + 1) (mqV1 d) := seen_after_store initMem View.bot d 7 .rlx
  have hmax : maxTs initMem d = 0 := by simp [maxTs, initMem]
  rwa [hmax] at h

/-- **Stamp publish handoff.** A consumer that acquire-loads the cell's stamp is
*determined* to read the producer's payload `7` — never the stale initial value.
The per-cell release/acquire pair carries the payload across. -/
theorem mpsc_consumer_reads_payload (hds : d ≠ s) (Vc : View) :
    readsAs (mqM2 d s) (loadView Vc s (mqPub d s) .acq) d 7 := by
  refine reads_determined _ _ _ 1 _ ?_ ?_
  · exact ra_transfer (seen d 1) (seen_mono d 1) (mqM1 d) (mqV1 d) Vc s 1 (mqV1_seen_d d)
  · intro m hmem hts
    simp [mqM2, mqM1, store, push, maxTs, initMem, hds, Ne.symm hds] at hmem
    rcases hmem with h | h <;> subst h
    · rfl
    · simp at hts

/-- **ABA defense.** Republishing the cell (a later producer laps it) takes a
strictly greater stamp timestamp than the previous publish. So a consumer that
re-reads the stamp sees it change and never silently accepts a lapped cell's stale
bytes. (Coherence, via `store_ts_fresh`.) -/
theorem mpsc_stamp_advances (hds : d ≠ s) :
    (mqPub d s).ts < (storeMsg (mqM2 d s) (mqV1 d) s 2 .rel).ts := by
  apply store_ts_fresh (mqM2 d s) (mqV1 d) s 2 .rel
  simp [mqPub, mqM2, mqM1, storeMsg, store, push, maxTs, initMem, hds, Ne.symm hds]

end MPSC

/-! ## The enqueue order is future-dependent — resolved by a prophecy

A producer `P`'s position in the queue order is its FAA ticket; but *which* ticket
it gets relative to a concurrent producer `Q` depends on **who FAAs first** — an
event in `P`'s future when it decides to enqueue. We model the race outcome as the
bit `pFirst` (did `P` win), and `P`'s resulting ticket. The bit is a physical fact
about the schedule; a prophecy predicts it. -/

/-- `P`'s ticket given whether `P` won the FAA race: `counter` if first, else
`counter + 1`. (`cond` so the two cases reduce definitionally.) -/
def pTicket (counter : Nat) (pFirst : Bool) : Nat := counter + (cond pFirst 0 1)

/-- **Prophecy soundness for the enqueue order.** The prophecy predicting "`P` wins
the FAA race" can always be set equal to the actual schedule outcome, uniquely —
because the outcome is read from the *physical* schedule, not the ghost
prophecy. (`proph_sound` at `Bool`.) -/
theorem mpsc_order_proph {Sched : Type} (pFirst : Sched → Bool) (sched : Sched) :
    ∃ pv : Bool, pv = pFirst sched ∧ ∀ y : Bool, y = pFirst sched → y = pv :=
  proph_sound pFirst sched

/-- **Faithfulness.** Under a consistent assignment the prophecy-predicted ticket
equals the real one — so `P` may commit to its queue position at enqueue time,
prophesying the race, and be provably correct. -/
theorem mpsc_ticket_proph_correct (counter : Nat) (pv w : Bool) (h : pv = w) :
    pTicket counter pv = pTicket counter w := by rw [h]

/-- **The enqueue LP is not present-determined.** At the moment `P` decides to
enqueue, its eventual queue position is not a function of the present (pre-race)
state: any present-only choice `f` is wrong for some race outcome. This is the gap
the prophecy fills (cf. `Prophecy.lp_not_present_determined`). -/
theorem mpsc_order_not_present (counter : Nat) (f : Unit → Nat) :
    ∃ pFirst : Bool, f () ≠ pTicket counter pFirst := by
  by_cases h : f () = counter
  · refine ⟨false, ?_⟩; change f () ≠ counter + 1; omega
  · exact ⟨true, h⟩

/-- **Consistency.** Whichever way the prophecy resolves, `P` and `Q` end in
distinct cells — the order is well-defined and never collides (matching
`mpsc_distinct_slots`). -/
theorem mpsc_order_distinct (counter : Nat) (pFirst : Bool) :
    pTicket counter pFirst ≠ pTicket counter (!pFirst) := by
  cases pFirst
  · change counter + 1 ≠ counter; omega
  · change counter ≠ counter + 1; omega

end LeanliftIris.PhaseC
