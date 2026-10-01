# `[LOOM]` — bounded weak-memory model checking of the concurrency corpus

Status: **2026-10-02**, PLAN-concurrency Phase E2. Off-CI: `ci.sh` does not run
this; run `./run.sh` by hand.

## What this is, and what it is not

**This is bounded model checking, not a proof.** [loom](https://github.com/tokio-rs/loom)
runs a small concurrent test under its model of the C11 memory model and
explores the thread interleavings and the values each load may return. A clean
run means: *for this test, at this size, within this bound, and within what
loom models, no execution violated an assertion or raced on a cell.* It does not
mean the algorithm is correct.

It is, however, the first thing in this repository's automated output that is
**not** sequentially consistent: loom explores weak-memory executions that
leanlift's SC models cannot express. That is why it exists.

Loom's own documented limits (loom 0.7.2, `README.md`, "Unsupported features"),
which bound everything below:

- **Load buffering is not explored.** Some executions the C11 model allows are
  never tried, so a bug can exist when loom reports none. *Loom is not sound.*
- **`SeqCst` loads, stores and read-modify-writes are treated as `AcqRel`.**
  Weaker than C11, so loom can raise false alarms. *Loom is not complete.*
  `fence(SeqCst)` is modelled fully; the cores below rely on `SeqCst` only
  through fences.

## The cores

Six small Rust reimplementations of corpus algorithms, written against loom's
atomics (`src/`). They are **not translations** of the corpus C++ (which is not
in this repository); they follow the algorithms the `[IRIS]` Phase B models
describe. Each has exactly one deliberate ordering mutation behind a cargo
feature, so the teeth check needs no source edits.

| # | Core | Test (spawned threads) | Mutation (`--features mutant-<core>`) | How loom catches it |
|---|---|---|---|---|
| 1 | SPSC ring, capacity 2 | producer pushes 1, 2; consumer pops twice | consumer's `tail` load `Acquire` → `Relaxed` | data race: read `spsc.rs:59` vs write `spsc.rs:47` |
| 3 | Seqlock, two-word payload | writer writes 1 then 2; reader one attempt | reader's `fence(Acquire)` removed | assertion: torn snapshot accepted, `a = 0, b = 1` |
| 2 | MPSC stamp queue, capacity 2 | two producers push 1 and 2; consumer pops twice | consumer's stamp load `Acquire` → `Relaxed` | data race on the cell value |
| 5 | SPMC broadcast ring, 1 slot | writer publishes 1 then 2 (a lap); two readers, one attempt each | **writer's** `fence(Release)` after marking the slot odd removed | assertion: torn slot accepted, `0` vs `1` |
| 7 | Treiber stack | two pushers (1, 2); one popper pops twice | popper's head load `Acquire` → `Relaxed` | data race on the node's link/value |
| 8 | Chase–Lev deque, capacity 4, no growth | deque holds 1, 2; owner takes once ∥ thief steals twice | owner's `fence(SeqCst)` in `take` removed (the Lê et al. fence) | assertion: element claimed twice, result `[1, 2, 2]` |

The clean model of every core passes; the mutated model of every core fails.
`run.sh` checks both and exits non-zero if any clean model fails **or any mutant
passes**.

### Seqlock witness, read from the values

The reader accepted `(a, b) = (0, 1)`. Acceptance means both sequence reads were
equal and even, and the only even sequence value before the second write
completes that is compatible with `a = 0` is `0`. So: first sequence read `0`;
`a` read before the writer's first store; `b` read after it; and the second
sequence read was satisfied with the stale `0`. The removed `Acquire` fence is
what forbids that last step — with it, reading the writer's `b` makes the odd
sequence visible.

## Bounds and run times

All on akilles (Linux x86_64), release build, one test at a time. "Executions"
is the number of complete executions loom explored for the test.

| Core | Bound 3: executions | Bound 3: time | No bound: executions | No bound: time |
|---|---|---|---|---|
| SPSC | 153 | 3 ms | 594 | 10 ms |
| Seqlock | 5,105 | 93 ms | 142,416 | 2.4 s |
| MPSC | 3,325 | 80 ms | 18,612 | 0.43 s |
| SPMC | 2,359,134 | 52 s | **did not finish** | stopped at 30 min |
| Treiber | 7,179 | 160 ms | 191,442 | 5.0 s |
| Chase–Lev | 113 | 2 ms | 387 | 9 ms |

"No bound" means loom's preemption bound was off: the search is exhaustive
**for that test**, within loom's model (so still subject to the load-buffering
gap above). **SPMC is the exception:** with no bound it did not finish within a
30-minute cap, so SPMC's only completed search is bound 3 — a truncated search,
stated as such. Every mutant was caught at bound 3 already.

## The harness shape matters — a finding

The first version of these tests ran one role on loom's main thread. For SPSC
that explored **one** execution, with or without a bound, and the mutant passed.
Probing showed the cause: with loom 0.7.2, when the spawned thread performs
independent loads before its conflicting store, loom did not explore running it
first (1 execution); the same accesses with every role in a spawned thread and
main only joining explored 45. All tests here use that shape, and the clean
execution counts above are the evidence the search is no longer degenerate.
Anyone adding a core should check its execution count is not suspiciously small
and that its mutant is caught.

## What is not covered

- **Test size.** Two or three threads, two operations each, capacities of 1 to
  4. Bugs that need more threads, more operations, a full ring, or growth are
  out of reach. (Chase–Lev buffer growth and the MPSC lap-wait path are not
  exercised.)
- **Reclamation.** The Treiber test has a single popper that frees what it pops;
  ABA and use-after-free under concurrent pops — the hazard-pointer half of #7 —
  are not checked here.
- **Source fidelity.** These are reimplementations; nothing checks they match the
  corpus C++.
- **Soundness.** Load buffering, as above.

For what the hand-proved `[IRIS]` lane proves about the same structures, see
`../docs/CERTIFICATE-concurrency.md`.
