# PLAN — lock-free / weak-memory verification (Iris-in-Lean lane)

> Give leanlift a **heavyweight, code-level lane** that verifies the part of
> lock-free C++/Rust its existing families *cannot*: the **C++11 weak-memory
> ordering** (relaxed/acquire/release/seq_cst, fences), ABA-by-bits, safe
> reclamation under weak memory, and **linearizability** of fine-grained
> concurrent structures — by building on the **Lean 4 port of Iris** rather than
> the sequentially-consistent interleaving models leanlift already has.
>
> **This lane is deliberately different from every other leanlift family.** It is
> *interactive theorem proving*, not a mechanical generator→checker. It preserves
> the **no-LLM** invariant (humans + Lean kernel, sorry-free) but **drops the
> push-button invariant**: proofs are hand-written and kernel-checked. It is the
> tool you reach for to certify *one finished structure to the bit*, not to sweep
> a design space. leanlift's automated families remain the first line; this is the
> court of last resort for the genuinely hard obligations.

## Why this lane exists (the gap it closes)

leanlift's concurrency story today (FSM/Petri/qnet/GSPN + equivalence) is
**sequentially-consistent interleaving over a hand-written model**. That gives
TLA+/Spin-grade design assurance plus quantitative envelopes — but it provably
**cannot** certify:

- the `std::memory_order` annotations that make lock-free code correct *and* fast
  (every algorithm in the validation corpus below turns on exactly this);
- ABA defused by real pointer/tag bits;
- safe memory reclamation (hazard pointers / EBR) under weak memory;
- linearizability of the *actual code* (leanlift proves bisimulation of a
  *model*, with no extraction from the source — a trust gap).

Iris is the established tool class for all of this, and as of 2026 it has a real,
actively-maintained Lean 4 port. This plan adopts it.

## What already exists in Lean 4 (DO NOT rebuild — survey)

Researched 2026-06-21. The ecosystem is further along than expected; the strategy
is **reuse `iris-lean` + `Eileen` foundations**, and spend our effort on the two
things nobody has built in Lean: a **concrete program logic for a real(istic)
object language** and a **weak-memory (iRC11-style) layer**.

| Component | Lean 4 status | Source | Use it for |
|---|---|---|---|
| **iris-lean** — MoSeL proof mode, UPred base logic, iProp model, invariants, later credits | **Active.** v4.30.0 (May 2026), 355 commits, leanprover-community. Optional Mathlib via `IrisMath`. | [github.com/leanprover-community/iris-lean](https://github.com/leanprover-community/iris-lean) | The base logic + proof mode. Our foundation. |
| **Eileen** — OFE/COFE/RA→CMRA algebra + base-logic foundations, **typeclass-based (Mathlib style)**, `Excl`/`Frac`/`Auth` milestones | **Plan/in-progress.** Explicitly flags **generalized (setoid) rewriting** as the key Lean gap. Complements iris-lean (which did the proof mode). | [markusde.ca/pages/eileen.html](https://www.markusde.ca/pages/eileen.html) | The camera hierarchy + ghost state. Track and adopt. |
| **splean (SLean)** — sequential heap separation logic, CFML-style `xsimp`/`xstep`/`xapp` tactics | Sequential only; no concurrency, no weak memory; SSA, no recursion. | [github.com/verse-lab/splean](https://github.com/verse-lab/splean) | Tactic-ergonomics reference for symbolic execution. |
| **Mathlib** — algebraic hierarchy, order theory, category theory | Mature. | mathlib4 | Host for OFE/CMRA bundled hierarchy; the COFE domain construction. |
| **Aeneas** — Rust → Lean *functional* translation | Mature; leanlift already uses it for the Rust codegen path. | [github.com/AeneasVerif](https://github.com/AeneasVerif) | A *Rust* reimpl of the corpus could reach Lean via Aeneas — but Aeneas is **functional/sequential**, so it is **not** a shortcut for the weak-memory core. Note only. |
| **Weak-memory program logic** (iRC11 / RSL / GPS / FSL — C11 release-acquire+relaxed) | **Does not exist in Lean.** All are Coq. This is the **long pole**. | RSL/FSL (Vafeiadis et al., Coq) | Must be built. Phase B. |

Net: the **base logic and proof mode are done** (iris-lean); the **algebra is
being done** (Eileen); the **sequential tactic story is demonstrated** (splean);
the **weak-memory object language is the unbuilt critical path**.

**iris-lean capability boundary (verified 2026-06-21 against the v4.28.0 source).**
iris-lean ships the base logic + proof mode **and a substantial resource-algebra
layer** — `Iris/Algebra/`: `CMRA`/`OFE`/`COFE` (+ `COFESolver` domain
construction), `Auth`, `View`, **`Heap`/`HeapView`** (authoritative heap with
`DFrac` fractions and singleton fragments — the algebra *behind* a `l ↦{dq} v`),
`GenMap`, `Frac`/`DFrac`/`Excl`/`Agree`, frame-preserving `Updates`, and a BI
`Lib/Fixpoint`. What it does **not** ship: any **program-logic layer** — no
`own`/ghost-state plumbing (`gFunctors`), no **weakest precondition**, no
**adequacy**. So **Phase A2 is a from-scratch build of the Iris program logic
over `λ-conc`** (embed `HeapView` into `iProp` via `own`, define the `wp`
fixpoint with `Lib/Fixpoint`, prove the per-`Head` lifting lemmas, then
adequacy). This is heavier than the "cheap win" framing suggests; treat A2 like a
gated focused effort with its own go/no-go (the algebra exists, but the wp +
adequacy mechanization is the bulk). A1 + A3 (done) stand on their own without it.

## The No-LLM invariant (carried over) + the honesty it forces

Every proof in this lane is **human-authored Lean checked by the Lean kernel,
sorry-free** — no LLM proposes proofs, consistent with leanlift's standing rule.
But unlike the other families this lane is **not automated**: a single non-trivial
structure is days-to-weeks of expert proof. Every milestone below states its
*manual cost* honestly. We never claim a structure is "verified" until its Lean
proof is sorry-free **and** a brutal-honesty review confirms the spec actually
captures linearizability/safety (a vacuous spec is the failure mode here).

## Validation corpus (the bit that makes this concrete)

A self-contained set of ten standard lock-free / weak-memory C++ structures (a
local `lockfree-algorithms/` corpus, vendored into this repo) is the test set.
Each is tagged with the **minimum lane layer** needed to verify it — this drives
phase ordering (do the SC-provable ones first, gate the weak-memory ones).

| # | Algorithm | Min layer needed | Notes |
|---|---|---|---|
| 1 | SPSC ring (cached index) | **B** (acq/rel) | smallest real weak-memory proof; first iRC11 target |
| 3 | Seqlock snapshot | **B** (acq/rel + fences) | torn-read freedom under release/acquire fences |
| 7 | Treiber stack + hazard pointers | **A→B** | SC linearizability first; reclamation needs the StoreLoad/`seq_cst` argument (B) |
| 2 | MPSC queue (Vyukov stamps) | **B + C** | ABA-by-stamp; future-dependent LP → **prophecy** (C) |
| 5 | SPMC broadcast ring | **B** | seqlock-across-a-ring; overrun semantics |
| 8 | Chase–Lev work-stealing deque | **B** (the `seq_cst` fence is the whole point) | the canonical store-load fence proof (Lê et al.) |
| 6 | spin/futex/semaphore | **A** (protocol) + out-of-scope (kernel) | lost-wakeup as a safety property; futex syscall is trusted |
| 9 | L2 order book | **A** (functional) | data-structure invariant; single-writer; SC suffices |
| 10 | effective-best (sweep VWAP) | **A** (functional) + B for the seqlock read | mostly a pure-function correctness + 128-bit no-overflow proof |
| 4 | false sharing | **n/a** | pure performance; nothing to prove |

First provable win is **#1 SPSC** (Phase B) and the **functional cores of #9/#10**
(Phase A). The marquee is **#8 Chase–Lev**: the one place a `seq_cst` fence is
genuinely required and acquire/release is provably insufficient — the headline
demonstration that this lane sees what leanlift's SC model cannot.

---

## Phase 0 — adopt the foundation (no new logic)

- [x] **0.1 Stand up `iris-lean`** as a Lake dependency in a sandbox package
  (`../leanlift-iris/`), toolchain pinned to **v4.28.0** (matches the repo's
  installed Lean), `lake build` green. **Started Mathlib-OFF** (core `Iris` only,
  Qq dep) for a fast first build — `IrisMath` deferred to Phase A, where the
  algebra is first needed. Drift fix recorded: Qq pinned to its `v4.28.0` tag to
  override iris's moving `git#stable` require (old commit GC'd upstream).
- [x] **0.2 Reproduce a MoSeL proof** end-to-end. `LeanliftIris/Hello.lean`:
  `ent_refl`, `sep_comm`, `wand_elim` via `iintro`/`isplitl`/`iexact`/`iapply`.
  Sorry-free — `#print axioms` reports **no axiom dependence at all**. The proof
  mode, `∗`/`-∗`/`⊢` connectives, and the `Iris.BI` class are usable from a
  foreign namespace (`open Iris Iris.BI`). **Done.**
- [ ] **0.3 Track Eileen.** Pull its OFE/COFE/CMRA hierarchy as it lands; do
  **not** fork a competing camera hierarchy. File the **generalized-rewriting**
  gap as a known risk (see Risks) and adopt whatever interim `≡`-rewriting tactics
  exist. *(Pending — revisit when Phase A needs the algebra; `IrisMath` is the
  on-ramp.)*

Exit 0: we can state and prove separation-logic entailments in Lean, sorry-free,
on top of the upstream port. **Pure integration; zero new metatheory.** ✅ reached
for 0.1/0.2; 0.3 tracked.

## Phase A — a concrete program logic over a small SC language

iris-lean ships the *logic* but (per survey) no off-the-shelf weakest-precondition
program logic for a realistic language. Build the smallest one that can host the
corpus' control flow.

- **A1 — object language `λ-conc`.** A tiny imperative core with a heap,
  `CAS`/`FAA`/load/store, `fork`, and (initially) **sequentially-consistent**
  semantics. Operational small-step in Lean. Keep it minimal — enough for
  Treiber/SPSC/order-book, no more.
- **A2 — weakest precondition + adequacy.** ✅ *Sequential adequacy done.* `wp e
  {Φ}` is defined over `λ-conc` in iris-lean's logic, and the **adequacy theorem**
  is proved for fork-free runs: `wp_adequacy_seq` — a `wp` proof of a pure `φ`
  plus a run reaching a value ⟹ the meta-level fact `φ v`. Built from multi-step
  preservation (`wp_primSteps_pres`) over the step-update tower `sfupdN`, whose
  collapse over a pure proposition (`sfupdN_pure_soundness`) is proved at the
  `UPred` model level. This is the trust anchor that closes leanlift's model-code
  gap *for this lane* — every sequential `wp` result (Treiber `push`/`pop`, the
  C1 bridge) now entails a real operational guarantee. The pipeline is also
  **closed end-to-end**: `heap_init` allocates the authoritative heap from nothing
  (`iOwn_alloc` + `auth_one_valid`), `wp_adequacy_closed` consumes
  `True ⊢ |==> ∃ γ, stateInterp γ σ ∗ wp γ e ⌜φ⌝` (no iProp hypotheses), and
  `ex_alloc_load_closed_input` discharges that input for `load (alloc v)` from
  `True` — so a worked program's spec provably constrains the real machine with no
  ghost-state assumptions. Adequacy now runs over the **real thread-pool `steps`**
  (`PhaseA/ForkFree.lean`): for a fork-free program, `wp_adequacy_steps` takes a
  genuine `steps` run and yields the meta-level fact. The bridge is
  `steps_singleton_forkFree` (a fork-free singleton pool stays a singleton and its
  `steps` run *is* a `primSteps` run), resting on `prim_step_preserves_forkFree`
  (reduction preserves fork-freedom given a fork-free heap — with fork-freedom
  preserved under substitution, `forkFreeE_substE`, and contexts, `forkFreeE_fill`).
  So the spec constrains the actual operational semantics. *Still to do:* the
  *forking* thread-pool adequacy (programs that spawn threads) — needs the `wpF`
  fork/progress extension.
- **A3 — first functional proofs (SC).** Verify the **#9 order-book** invariant
  (`best = max occupied level`, fall-back correctness) and the **#10 sweep**
  (exact 128-bit notional, `Q==0`/over-ask/drained-level cases, `best_ask ≤ VWAP
  ≤ touch`). These are essentially pure-function proofs — cheap, high-confidence,
  and they exercise the toolchain before the hard concurrency.
- **A4 — first concurrent proof (SC).** Verify **#7 Treiber stack** linearizable
  under SC using a **logically-atomic triple** (the linearizability skeleton),
  reclamation deferred. Establishes the logical-atomicity pattern we reuse.

Exit A: code-level, kernel-checked proofs of two functional cores + one
concurrent structure, under SC. **Already strictly beyond leanlift's model lane**
(real code, real adequacy, linearizability spec). Manual cost: A3 ~days, A4 ~1–2
weeks.

## Phase B — the weak-memory layer (the long pole, gated)

This is the research frontier and the reason the lane exists. No Lean prior art;
we port the **iRC11 / RSL** approach (C11 release-acquire + relaxed, fences) onto
iris-lean.

- **B1 — C11 op-sem for `λ-conc`.** Replace SC with a release-acquire + relaxed
  memory model (per-location modification orders, release sequences, fences).
  Decide operational (à la `iRC11`'s view-based model) vs axiomatic; **prefer the
  operational view-based model** — it composes with iris-lean's `wp`/adequacy.
- **B2 — the weak-memory assertions.** Release/acquire points-to, the "objective
  vs subjective" proposition split, fence reasoning, the **StoreLoad** edge that
  only `seq_cst` provides. This is the bulk of the build.
- **B3 — `#1 SPSC` under acq/rel.** ✅ *Done* (`PhaseB/Logic.lean`,
  `spsc_consumer_reads_payload`). The smallest honest weak-memory proof:
  payload-before-publish release/acquire pairing, relaxed self-counter loads.
- **B4 — `#3 seqlock` + `#5 SPMC`.** ✅ *Done.* Seqlock (`PhaseB/Seqlock.lean`):
  torn-read freedom both ways — `seqlock_consistent_read` (acquire + even parity ⇒
  no torn snapshot) and `seqlock_torn_without_validation` (bare relaxed reads admit
  a torn `[42,0]` machine run). SPMC (`PhaseB/SPMC.lean`): the per-slot stamp
  seqlock with slot reuse — `spmc_consumer_reads_round0` (pre-lap consistency),
  `spmc_reads_latest` (freshest publish read consistently after a lap),
  `spmc_stamp_advances` (overrun is observable as a strictly-advancing stamp), and
  `spmc_relaxed_lap_in_flight` — a payload read *not* ordered after the stamp
  acquire admits a lapped/stale value, so the data read genuinely must be ordered
  by the acquire (`spmc_acq_ordered_reads_fresh` is the positive side). This closes
  the earlier scope caveat.
- **B5 — `seq_cst` + `#8 Chase–Lev`, the marquee.** ✅ *Last-element race done.*
  `PhaseB/SeqCst.lean` adds a global SC view (`scStore`/`canLoadSC`) whose
  StoreLoad lower-bound **forbids store-buffering** — `sb_sc_no_both_zero` proves
  *no* SC interleaving of SB yields the weak `r1=r2=0`, the exact outcome
  `sb_admits_reorder` shows release/acquire admits. `PhaseB/ChaseLev.lean` then
  recognizes the Chase–Lev take/steal last-element race *as* store buffering and
  proves both halves: `chase_lev_double_claim_relacq` (rel/acq lets owner **and**
  thief claim the same element — the Lê et al. bug) and
  `chase_lev_sc_no_double_claim` (seq_cst forbids the double-claim for every
  interleaving). The sequential structure (`PhaseB/ChaseLevDeque.lean`) is also
  done: a fixed-capacity circular buffer with owner LIFO (`popBottom_pushBottom_val`),
  single-element steal, size/`top≤bot` invariants, and a concrete `cap=2`
  wrap-around run where a vacated slot is reused and the thief still reads every
  element back in FIFO order. The **growable (doubling) buffer** is also done
  (`grow`, compacting variant): `elem_grow` (contents preserved across a grow),
  `size_grow`, `cap_grow` (capacity doubles), and a concrete wrapped→grown run
  (`grow_steal0/1`) where a wrapped buffer is re-laid contiguously, contents intact.
- **B6 — reclamation under weak memory.** ✅ *Done.* Safety (`PhaseB/HazardPtr.lean`):
  `#7` hazard-pointer safety as two-sided store buffering: the reader's
  publish-then-revalidate ∥ the reclaimer's retire-then-scan. `hp_use_after_free_relacq`
  (rel/acq admits use-after-free — reader derefs a node the reclaimer frees) and
  `hp_sc_no_use_after_free` (seq_cst forbids it for every interleaving).
  **Bounded-garbage accounting** (`PhaseB/HazardGC.lean`): `allSlots_length_le` (at
  most `N·K` nodes hazardous), `bounded_garbage`/`bounded_garbage_NK` (a scan leaves
  ≤ `N·K` unreclaimed, by pigeonhole), and `reclaim_progress` (a scan of `R` retired
  nodes frees ≥ `R − N·K`, so the retire list cannot grow unboundedly). EBR optional.

Exit B: the weak-memory obligations leanlift cannot express are kernel-checked for
SPSC, seqlock, SPMC, Chase–Lev, and HP-reclamation. **Gate:** B1–B2 are a major
build (months, expert); start only after Phase A proves the toolchain and after a
go/no-go review. If B stalls, Phase A alone is already a shippable capability.

## Phase C — linearizability & future-dependent linearization points

- **C1 — logical atomicity, generalized.** 🚧 *Foundation done* (`PhaseC/LogAtom.lean`).
  A reusable logically-atomic-triple library `LAT P Q` over an abstract state:
  framing-prefix `pre` + single linearization point `commit` (`P → Q`) +
  framing-suffix `post`, with the payoff `LAT.atomic_commit` (running the whole
  operation from a `P`-state lands in `Q`) and the structural rules `LAT.refl`
  (no-op) and `LAT.frameL` (frame). Instantiated for Chase–Lev `take`: `takeLAT`
  (one-element `take` linearizes by removing the element, index read/write as
  framing steps) and `take_linearizes`. The abstract triple is now also **bridged
  to the real `wp`** (`PhaseC/WpAtomic.lean`): a wp Hoare triple `HoareTriple` with
  structural rules (`hoare_value`/`hoare_mono`/`hoare_conseq`) lifted from Phase A,
  the Treiber-`push` linearization point as a Hoare triple (`hoare_push_cas`, from
  `push_cas_step`), and the bridge `push_realizes_commit` — the verified `wp` proof
  of `push` establishes exactly the abstract `LAT`'s commit (`pushAbstract`, `v::·`)
  on the heap-level `isStack` predicate. So the abstract LP and the concrete
  iris-lean proof name the same atomic effect. The bridge is now **operation-agnostic**:
  a `Realizes repr f e` predicate ("`e` takes a heap representing `s` to one
  representing `f s`") with a consequence rule (`realizes_mono`), and the general
  `lat_realized` — for *any* `LAT P Q` and any program realizing its commit, the real
  `wp` establishes the abstract postcondition `Q` at the representation level
  (`{repr s} e {∃ s', ⌜Q s'⌝ ∗ repr s'}`). `push` is re-derived through it
  (`push_realizes` + `push_establishes_post`, end-to-end). **Three operations** now
  go through the bridge, covering distinct effects and both total/partial shapes:
  (1) Treiber `pop` (`PhaseA.pop_body_spec` — a verified
  read-modify-return lock-free op using the new `wp_fst`/`wp_snd` projection rules;
  returns the head and re-establishes `isStack` for the tail), bridged via
  `popAbstract` (commit `List.tail`) + `pop_realizes_commit`. `pop` is *partial*
  (non-empty stacks only), so it uses the per-state `LAT`+`HoareTriple` interface
  rather than the total `∀`-`Realizes` wrapper — showing the bridge handles
  state-shrinking ops too. (2) An **FAA atomic counter** (`PhaseA.Counter` —
  `incr = FAA(s,1)` via the new `wp_faa` arithmetic-RMW rule; returns the old count,
  advances by one), bridged via `incrAbstract` (commit `(· + 1)`) +
  `incr_realizes`/`incr_establishes_post`. `incr` is *total*, so it uses the
  `∀`-`Realizes` wrapper like `push` — the same interface absorbs CAS-linking,
  head-removal, and arithmetic RMW, total and partial alike. Verified operations
  also **compose into larger programs**: `twoIncr_spec` chains `incr_spec` with
  itself under `wp_let` (`let _ = incr s in incr s` advances the count by two),
  showing the per-operation specs sequence via the program logic. *Still to do:* the full
  mask/atomic-update encoding (open the invariant at the LP, true `<<<P>>> e <<<Q>>>`
  against a concurrent context).
- **C2 — prophecy variables.** 🚧 *Foundation done* (`PhaseC/Prophecy.lean`). The
  prophecy mechanism in the small + the Chase–Lev last-element LP: the obstruction
  `lp_not_present_determined` (the LP is genuinely future-dependent — no present-only
  effect is correct), soundness `proph_sound` (the prophesied value may always be
  chosen equal to its physical resolution, uniquely) and faithfulness
  `takeLP_proph_correct`, and the payoff `owner_claim_lp` — under seq_cst, a
  `take` that physically claims linearizes (by the prophecy-resolved LP) as
  "owner took it" with the thief excluded, discharged via
  `chase_lev_sc_no_double_claim`. **#2 MPSC** (Vyukov stamp queue) is also done
  (`PhaseC/MPSC.lean`): the FAA contention point is exclusive (`tickets_nodup`,
  `mpsc_distinct_slots` — distinct cells *by the RMW*, no seq_cst), the per-cell
  release/acquire stamp hands off the payload (`mpsc_consumer_reads_payload`) with
  ABA defense (`mpsc_stamp_advances`), and the enqueue order is future-dependent —
  resolved by a prophecy of the FAA race winner (`mpsc_order_proph`,
  `mpsc_order_not_present`, `mpsc_order_distinct`). The prophecy-resolution
  *operational* step is also done (`PhaseC/ProphMachine.lean`): `NewProph`/`Resolve`
  as real `PStep` transitions (resolve guarded to fire at most once), with
  `resolved_stable` (a resolution is permanent) and `proph_predicts_future` (the
  prophesied value read from the final state equals the value resolved
  mid-execution — soundness over the transition system, not an assumed resolution
  function). *Still to do for full C:* lift these onto the Phase-A `wp`/adequacy so
  the LP/resolution attach to the real `λ-conc` execution (C1 currently runs an
  abstract micro-step list; resolution lives on its own small machine).

## Phase D — integration with leanlift (the seam)

- **D1 — lane boundary, explicit.** This lane is **not** a `lift` subcommand that
  runs in CI by default. It is a separate package producing sorry-free `.lean`
  proofs, checked off-CI (the proofs are heavy). `ci.sh` gains only a *cheap*
  check: that the proof package **builds and is sorry-free**, not that it re-elabs
  the world. Tag everything `[IRIS]` (cf. the `[M24]`/`[GPU]` tag scheme).
- **D2 — the combined certificate.** For a structure proved in this lane, the
  story becomes: *leanlift SC-model (design safety + equivalence + timing/qnet)
  ∧ Iris-lane (weak-memory correctness + linearizability)* ⇒ the structure is
  correct under its real memory model. Document which axes each side owns so the
  certificate is honest about its trust boundaries.
- **D3 — no overclaiming.** The README/docs must state plainly: leanlift's
  automated families do **not** prove memory-order correctness; only the `[IRIS]`
  lane does, and only for structures someone has hand-proved. Silence here would
  read as "leanlift verifies lock-free code," which is false.

---

## Phase E — Rust variant (AFTER the C++ corpus is done)

Do **not** start this until Phases 0–A (and ideally B) on the C++ corpus are
landed. It is a deliberate follow-on: once the Iris lane works for C++, Rust is
the *easier* second target and lets leanlift assemble a stronger concurrency
story with **less original mechanization** — because the foundations and the
practical tooling already exist for Rust specifically.

**Why Rust is better-positioned than C++ here:**

- **The Iris foundation is already Rust-specific.** RustBelt — and **RustBelt
  Relaxed** over the iRC11 weak-memory model — proves safety of `unsafe`
  concurrent libraries (`Arc`, `Mutex`, `RwLock`, …) in Iris/Coq. An Iris-in-Lean
  development aimed at Rust can reuse that decade of design rather than inventing
  it (the C++ side has no equivalent).
- **A richer practical toolchain exists**, and it maps onto leanlift's tiers.

**Aeneas's actual role (important — it does NOT cover the lock-free part):**
Aeneas translates **safe, sequential** Rust to a *pure functional* model; that
works precisely because ownership forbids the aliasing lock-free code is built on.
Atomics / `UnsafeCell` / raw pointers / shared mutable state are outside its model
by construction — the **same boundary** as the C++ side. leanlift already uses
Aeneas in its sweet spot (sequential Rust kernels). So for the corpus, Aeneas
contributes the **sequential slice only**.

**Tool mapping (Rust):**

| Tool | Kind | Weak memory? | `unsafe`/atomics? | leanlift tier |
|---|---|---|---|---|
| **Aeneas → Lean** | functional translation | n/a | ❌ safe/seq only | existing sequential Rust path |
| **Loom** | exhaustive model-checker | ✅ models C11 orderings | ✅ | automated first line (the Rust GenMC/CDSChecker) |
| **Shuttle** | randomized conc. testing | partial | ✅ | cheap screening |
| **Kani** | bounded MC (CBMC) | limited | ✅ | already in leanlift's stack (`[M24]`) |
| **Verus** | SMT deductive (Z3) | permission-based, ~SC (not full C11) | ✅ ghost permissions | semi-automated deductive middle |
| **RustBelt-Relaxed / Iris** | interactive proof | ✅ full iRC11 | ✅ | heavyweight foundational lane |

**Phase E plan (mirrors the C++ phases, mostly by reuse):**

- **E1 — sequential slice via Aeneas.** Reimplement the SC-only structures (order
  book, sweep-VWAP, bitmap) in safe Rust; Aeneas → Lean gives bit-exact functional
  proofs nearly for free. This is leanlift's *existing* Rust path — no new lane.
- **E2 — automated weak-memory screening.** Wire **Loom** (and optionally Kani /
  Shuttle) over the concurrency cores (SPSC, MPSC, seqlock, SPMC, Treiber,
  Chase–Lev). Bounded, not a proof, but it *sees* weak-memory bugs leanlift's SC
  model cannot. Tag `[LOOM]`, off-CI.
- **E3 — deductive lane, pick one:**
  - **Verus** for the pragmatic route (SMT-discharged, handles atomics via the
    ghost-permission / tokenized-state-machine discipline; memory model closer to
    SC than full C11 — state this limit honestly), or
  - a **RustBelt-style Iris-in-Lean** development for full iRC11 weak-memory proof
    (reuses Phase B; maximal assurance, maximal manual cost).
- **E4 — certificate seam.** Same as D2 but for Rust: Aeneas (sequential) ∧
  Loom (weak-memory screening) ∧ Verus-or-Iris (deductive) — document which axis
  each tool owns and its trust boundary.

Net: for Rust, Aeneas covers the sequential kernels it already handles, Loom/Kani
cover automated weak-memory checking, and the deductive lane builds on RustBelt —
so Rust reaches further than C++ for less new code. **But it is strictly a
post-C++ task; the C++ corpus is the proving ground for the lane.**

---

## Risks & honest unknowns

- **Generalized/setoid rewriting in Lean (highest risk).** Iris proofs lean
  heavily on rewriting under OFE `≡`, and both Eileen and the community flag
  Lean's generalized rewriting as weaker than Coq's. If this stays immature, proof
  ergonomics suffer badly. Mitigation: lean on iris-lean's existing interim
  tactics; prefer propositional `=` via quotients where possible; track upstream
  Lean generalized-rewriting work.
- **The weak-memory layer is genuinely unbuilt (Phase B).** Everything in Lean
  today is SC or sequential. B1–B2 is original mechanization, not a port of
  existing Lean. Scope it as a research project with a go/no-go after Phase A.
- **iris-lean completeness drift.** It's active but may lack a resource/lemma we
  need; budget upstreaming contributions, don't fork.
- **Manual cost is the headline cost.** This never becomes push-button. If the
  goal is breadth (many structures, fast), this lane is the wrong tool — use the
  SC families and accept their limits. This lane is for depth on a chosen few.
- **Spec vacuity.** A linearizability spec that's accidentally trivial "passes"
  vacuously. Every Phase A/B/C structure needs an adversarial spec review + a
  discrimination test (a deliberately-wrong variant must fail to verify), mirroring
  the FPGA lane's "teeth" tests.

## Recommendation (decision pending)

Proceed with **Phase 0 + Phase A only**, as a time-boxed spike: adopt iris-lean,
prove the two functional cores (#9, #10) and one SC-linearizable structure (#7
Treiber). That is low-risk, reuses upstream, and already delivers code-level
proofs beyond leanlift's SC model. Treat **Phase B (weak memory)** as a separate,
explicitly-funded research effort with its own go/no-go — it is the real prize and
the real cost, and it should not be started until the toolchain is proven on A.

## Sources

- iris-lean (Lean 4 Iris port): https://github.com/leanprover-community/iris-lean
- Eileen (Iris-in-Lean foundations plan): https://www.markusde.ca/pages/eileen.html
- splean (sequential SL in Lean): https://github.com/verse-lab/splean
- "Formalizing higher-order separation logic in Lean" (ETH thesis proposal):
  https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjectProposals/iris-in-lean.pdf
- iRC11 / RSL (C11 weak-memory separation logic, Coq prior art):
  https://people.mpi-sws.org/~viktor/papers/oopsla2013-rsl.pdf
- Aeneas (Rust→Lean): https://github.com/AeneasVerif
- Loom (Rust C11 model checker): https://github.com/tokio-rs/loom
- Shuttle (randomized Rust concurrency testing): https://github.com/awslabs/shuttle
- Kani (Rust bounded model checker): https://github.com/model-checking/kani
- Verus (SMT-deductive Rust verifier): https://github.com/verus-lang/verus
- RustBelt / RustBelt Relaxed (Iris, weak-memory Rust): https://plv.mpi-sws.org/rustbelt/
