# The combined concurrency certificate — what is proved, per structure, and by whom

Status: **2026-10-01.** This is PLAN-concurrency Phase D2: the honest statement of
what the two halves of leanlift's concurrency story each prove, structure by
structure, with the trust boundary each half owns. Read the README section
"What leanlift does not verify: memory-order correctness" first; this document is
its per-structure form.

## The claim shape

For a lock-free structure the strongest claim leanlift can make is the
conjunction of two independent results:

1. **leanlift SC-model half** (the `lift` subcommands, `lean/LeanLift/`,
   `leanproofs/`, the behavioural-model families): a proof about a *model* of the
   code under **sequential consistency** — one shared state, every read sees the
   last write in one global order. Design safety, equivalence of model and
   reference, timing/queueing numbers where a family provides them.
2. **`[IRIS]` lane half** (`leanlift-iris/`, hand-written): memory-order
   correctness and/or linearizability, proved in iris-lean, kernel-checked,
   sorry-free (`ci.sh` runs `#print axioms` on every theorem named in
   `leanlift-iris/CiAxioms.lean`).

A structure carries the **combined certificate** only when both halves exist for
*that structure*. Today that is true for **none** of the corpus: the `[IRIS]` lane
has results for most of it, and the SC-model half has not been run on any of
these structures (there is no `examples/` entry for a ring, a seqlock, a stack, a
queue or a deque). So every row below is at most one half.

## Trust boundaries that apply to every row

- **Model, not source.** Neither half reads the C++ in the `lockfree-algorithms`
  corpus. The SC-model half proves what it is given as a model; the `[IRIS]` lane
  proves hand-written models — either programs in the lane's own language
  `λ-conc` (Phase A/C) or executions of its view-based weak-memory machine
  (Phase B). No extraction, no refinement from source, so "the code is correct"
  is not a claim either half makes. This is the gap PLAN-concurrency names in its
  first paragraph and it is unchanged.
- **Memory model, per theorem.** `[IRIS]` results are of three kinds and the
  table says which: *weak-memory aware* (Phase B, view-based release/acquire/
  relaxed/seq_cst model — the only memory-order content in the repository);
  *SC by construction* (Phase A program logic and Phase C over `λ-conc`, which
  has one shared heap and atomic read-modify-writes); *pure functional* (Phase A3,
  no concurrency at all).
- **Partial correctness.** Adequacy and safety results constrain runs that reach
  a value; nothing claims termination. Progress means "no thread is stuck", not
  "every thread finishes".
- **Axioms.** Every `[IRIS]` theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound` (iris-lean's model needs classical
  reasoning); no custom axiom, no `sorry`. The SC-model half's Lean output is
  checked the same way by `ci.sh`.
- **Hand-proved only.** Nothing in the `[IRIS]` lane is generated. A structure not
  in the table has no memory-order result, whatever the SC-model half says.

## Per structure

| # | Structure | `[IRIS]` lane result | Kind | SC-model half | Combined? |
|---|---|---|---|---|---|
| 1 | SPSC ring (cached index) | `spsc_consumer_reads_payload` (B3, `PhaseB/Logic.lean`): the consumer that acquire-loads the flag is determined to read the payload, never the stale value; `message_passing` (B1): the release/acquire handoff that underlies it, with `mp_relaxed_admits_stale` and `mp_release_necessary` showing both orderings are needed | weak-memory aware | not run | no |
| 3 | Seqlock snapshot | `seqlock_consistent_read` (B4, `PhaseB/Seqlock.lean`): acquire + even parity ⇒ no torn snapshot; `seqlock_torn_without_validation`: bare relaxed reads admit a torn `[42, 0]` run (the proof has teeth) | weak-memory aware | not run | no |
| 5 | SPMC broadcast ring | `spmc_reads_latest`, `spmc_consumer_reads_round0`, `spmc_stamp_advances`, `spmc_relaxed_lap_in_flight` / `spmc_acq_ordered_reads_fresh` (B4, `PhaseB/SPMC.lean`): freshest publish read consistently after a lap, overrun observable as a strictly advancing stamp, and the data read must be ordered by the acquire or a lapped value is admitted | weak-memory aware | not run | no |
| 7 | Treiber stack | SC linearizability skeleton: `push_body_spec`, `pop_body_spec` (Phase A, `PhaseA/Treiber.lean`), realized against the abstract triple (`push_realizes_commit`, `pop_realizes_commit`, `PhaseC/WpAtomic.lean`); `two_pushes_linearize` (`PhaseC/Linearize.lean`) at the abstract state | SC by construction | not run | no |
| 7 | + hazard pointers | `hp_sc_no_use_after_free` (B6, `PhaseB/HazardPtr.lean`): seq_cst forbids the reader dereferencing a node the reclaimer frees, and `hp_use_after_free_relacq`: release/acquire alone admits it; `HazardGC.bounded_garbage`, `reclaim_progress` (`PhaseB/HazardGC.lean`): at most `N·K` unreclaimed, a scan frees the rest | weak-memory aware (safety); pure (accounting) | not run | no |
| 2 | MPSC queue (Vyukov stamps) | `tickets_nodup`, `mpsc_distinct_slots` (the FAA contention point hands out distinct cells, no seq_cst needed); `mpsc_consumer_reads_payload`, `mpsc_stamp_advances` (per-cell release/acquire stamp handoff with ABA defense); `mpsc_order_proph`, `mpsc_order_not_present`, `mpsc_order_distinct` (enqueue order is future-dependent and resolved by a prophecy of the FAA race winner) — `PhaseC/MPSC.lean` | weak-memory aware (handoff); prophecy at the abstract level | not run | no |
| 8 | Chase–Lev work-stealing deque | `sb_sc_no_both_zero` (B5, `PhaseB/SeqCst.lean`): seq_cst forbids store buffering; `chase_lev_double_claim_relacq` / `chase_lev_sc_no_double_claim` (`PhaseB/ChaseLev.lean`): release/acquire lets owner and thief claim the same element, seq_cst forbids it in every interleaving — the Lê et al. argument; `owner_claim_lp` (`PhaseC/Prophecy.lean`): the prophecy-resolved LP for `take` under seq_cst; `takeLAT` / `take_linearizes` (`PhaseC/LogAtom.lean`); sequential structure and growable buffer (`PhaseB/ChaseLevDeque.lean`: `popBottom_pushBottom_val`, `elem_grow`, `cap_grow`) | weak-memory aware (race); prophecy at the abstract level; pure (buffer) | not run | no |
| 6 | spin / futex / semaphore | nothing | — | not run | no |
| 9 | L2 order book | `maxOcc_some_iff`, `maxOcc_fallback`, `minOcc_some_iff`, `minOcc_fallback`, `microprice_bracket` (A3, `PhaseA/OrderBook.lean`): best = max occupied level, fall-back on cancel, microprice bracketed | pure functional | not run | no |
| 10 | effective-best (sweep VWAP) | exact `filled = min Q total`, completion ⇔ `Q ≤ total`, over-ask, drained-level skip, `best_ask·filled ≤ notional ≤ touch·filled` in exact `Nat` (A3, `PhaseA/Sweep.lean`) | pure functional | not run | no |
| 4 | false sharing | nothing to prove (performance only) | — | — | — |

Structure-independent `[IRIS]` results, all **SC by construction** over
`λ-conc` and listed so nobody reads them as memory-order content: the program
logic and its rules (`PhaseA/Wp.lean`, `WpLifting.lean`), sequential and
thread-pool adequacy (`wp_adequacy_closed`, `wp_adequacy_pool_closed`), safety
(`wp_adequacy_safe`), the closed unconditional facts (`PhaseA/Concrete.lean`),
linearizability at the abstract state (`linearizable_abstract`), the erasure
from real pool runs (`real_run_linearizes`, `two_incrs_steps`), and the CAS race
as a run-indexed family (`two_cas_steps`, `two_cas_linearizes`).

## Bounded evidence: `[LOOM]` (not part of either half)

Since 2026-10-02, `leanlift-loom/` model-checks small Rust reimplementations of
six rows above under loom's C11 model: #1 SPSC, #3 seqlock, #2 MPSC, #5 SPMC,
#7 Treiber (no reclamation), #8 Chase–Lev (no growth). Every clean model
passes and every core's injected ordering bug is caught; bounds and execution
counts are in `leanlift-loom/LOOM.md`. This is **evidence, not a certificate
half**: bounded, a tiny test per core, reimplementations rather than the corpus
C++, and loom does not explore load-buffering executions. It does not upgrade
any row, and it is independent of the `[IRIS]` proofs — agreement between them
is not checked anywhere.

## What would make a row "combined"

For a structure `S` in the table: a leanlift behavioural model of `S` (or a
translated kernel of its sequential core) carried to M3/L3 by the automated
lanes, **and** the `[IRIS]` row above, **and** a written statement of what the two
models share — which operations, which state, which invariant — since nothing
checks that the SC model and the `λ-conc`/view model describe the same
algorithm. That third item is the honest cost of a "combined" certificate and
is not automated anywhere in this repository.

## Reading a claim

- "verified by leanlift" with no `[IRIS]` row ⇒ verified under sequential
  consistency, in a model, nothing about memory order.
- an `[IRIS]` row marked *SC by construction* ⇒ a concurrency result (adequacy,
  linearizability, a race outcome) with no memory-order content.
- an `[IRIS]` row marked *weak-memory aware* ⇒ a memory-order result about the
  lane's view-based model of that algorithm, for that algorithm only.
- "combined" ⇒ both halves plus the shared-model statement; currently nothing.
