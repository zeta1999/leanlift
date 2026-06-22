/-
CI sorry-free gate for the [IRIS] weak-memory / linearizability lane.

Not part of the `LeanliftIris` library target (it is never imported by
`LeanliftIris.lean`); `ci.sh` runs it standalone with `lake env lean CiAxioms.lean`
and fails if the output mentions `sorryAx`. `#print axioms` walks the full
dependency tree of each marquee theorem, so a `sorry` anywhere beneath them — even
transitively — surfaces here as a kernel-level `sorryAx` dependency. This is the
"the proofs are actually proofs" teeth for the lane (cf. the FPGA lane's
`M3 PROVED sorry-free` greps).
-/
import LeanliftIris

open LeanliftIris.PhaseB
open LeanliftIris.PhaseC

-- Phase B — weak-memory marquee results across the corpus.
#print axioms message_passing                 -- B1 message passing
#print axioms spsc_consumer_reads_payload     -- B3 SPSC handoff
#print axioms seqlock_consistent_read         -- B4 seqlock torn-read freedom
#print axioms spmc_reads_latest               -- B4 SPMC freshest-wins
#print axioms spmc_relaxed_lap_in_flight      -- B4 SPMC lap-in-flight necessity
#print axioms sb_sc_no_both_zero              -- B5 seq_cst forbids store buffering
#print axioms chase_lev_sc_no_double_claim    -- B5 Chase–Lev (marquee)
#print axioms hp_sc_no_use_after_free         -- B6 hazard-pointer safety
#print axioms HazardGC.bounded_garbage        -- B6 bounded garbage
#print axioms Deque.elem_grow                 -- B5 growable deque contents preserved

-- Phase C — linearizability / prophecy.
#print axioms proph_sound                     -- C2 prophecy soundness
#print axioms owner_claim_lp                  -- C2 Chase–Lev LP, via SC safety
#print axioms LAT.atomic_commit               -- C1 logically-atomic commit
#print axioms take_linearizes                 -- C1 take linearizes
#print axioms mpsc_distinct_slots             -- #2 MPSC exclusive cells
#print axioms mpsc_consumer_reads_payload     -- #2 MPSC stamp handoff
#print axioms mpsc_order_proph                -- #2 MPSC enqueue-order prophecy
