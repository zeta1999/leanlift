# TODO — concurrency / Iris-in-Lean lane

Actionable checklist for [`PLAN-concurrency.md`](./PLAN-concurrency.md). Sandbox:
[`../leanlift-iris/`](../leanlift-iris/). Order matters: do the C++ corpus first
(Phases 0→A→B→C→D), then the Rust variant (Phase E).

## Phase 0 — adopt the foundation
- [x] 0.1 iris-lean as a Lake dep, pinned v4.28.0 (core `Iris`, no Mathlib), `lake build` green
- [x] 0.2 MoSeL "hello world" — `ent_refl`/`sep_comm`/`wand_elim`, sorry-free (no axiom dependence)
- [ ] 0.3 track Eileen; pull OFE/COFE/CMRA algebra (via `IrisMath`) when Phase A needs it; do NOT fork the camera hierarchy

## Phase A — concrete SC program logic (the cheap, high-confidence wins)
- [x] A1 define `λ-conc`: tiny imperative core + heap + CAS/FAA/load/store/fork, SC small-step semantics in Lean
      — `leanlift-iris/LeanliftIris/PhaseA/Lang.lean`: Val/Expr (HeapLang-style: closures, pairs, ints/bools), substitution, `Head` reduction (pure + heap + atomic CAS/FAA + fork), evaluation contexts (`Frame`/`fill`), `prim_step`, thread-pool `step` + `steps` (RTC). Metatheory for A2/A4: values aren't redexes (`head_not_val`, `val_no_prim_step` = normal forms), context composition `fill_app` (wp-bind basis), `fill_val_nil`; worked alloc/load/CAS-atomic/fork examples. Sorry-free (audit in `PhaseA/Axioms.lean`).
- [ ] A2 define `wp e {Φ}` over `λ-conc`; prove the adequacy theorem (closes the model-code gap for this lane)
      — **scope sharpened (iris-lean v4.28.0 audited 2026-06-21):** iris-lean has the resource *algebra* + ghost-state primitive `iOwn` and a worked wp/points-to template (`Iris/Examples/IProp.lean`), but no ready program logic. A2 = adapt that template to `λ-conc`. In progress:
      - [x] A2.1 heap resource + points-to: `LeanliftIris/PhaseA/HeapRes.lean` — `FHeap` functor (`HeapView F Nat (Agree (LeibnizO Val)) AssocList`), `l ↦[γ] v := iOwn γ (Frag l (own one) (toAgree v))`, **agreement** lemma `l ↦ v ∗ l ↦ w ⊢ ⌜v = w⌝`. Sorry-free (Iris-model axioms only).
      - [x] A2.2 `wp` fixpoint over `λ-conc`: `LeanliftIris/PhaseA/Wp.lean` — `stateInterp` (authoritative heap via the function-map `HeapView`, `toAgreeHeap`), `wpF` (relational `prim_step`), `Contractive` instance, `wp := fixpoint wpF`, `wp_unfold`, and a `wp_value` smoke test. Sorry-free. Caveats (additive, don't change the fixpoint): primary-thread only (no `[∗list] efs` fork obligation yet — needs a big-op `ne` lemma) and no `reducible`/progress conjunct (as in the upstream template).
      - [~] A2.3 lifting lemmas — `LeanliftIris/PhaseA/WpLifting.lean`. Done: `prim_step` inversion infra (`head_toVal_none`, `fill_toVal_none`, `ctx_nil_of_load`, `prim_step_load_inv`), generic `wp_lift_step`, auth-frag heap agreement (`stateInterp_pointsTo_agree`: `stateInterp ∗ l↦v ⊢ ⌜σ l = some v⌝`), and the first full heap rule **`wp_load`** (end-to-end: agreement + step inversion + points-to returned to continuation). Sorry-free. **`wp_store`** also done (first *mutating* rule: `l↦v_old ∗ (l↦v_new -∗ |==> Φ ()) ⊢ wp γ (store (loc l) v_new) Φ`, via frame-preserving ghost update `iOwn_update ∘ HeapView.update_replace`, `insert_toAgreeHeap : insert (toAgreeHeap σ) l (toAgree v) = toAgreeHeap (σ.set l v)`; key trick: give the `iOwn_op`/`iOwn_update` steps explicit types so the functor/`ElemG` instances resolve). So the `wp` handles heap reads **and** writes. **Pure rules** also done: `wp_pure_det` (generic deterministic heap-preserving step ⇒ `▷ wp etgt Φ ⊢ wp e Φ`) + `prim_step_ite_true_inv` + `wp_if_true`. Remaining: alloc/CAS/FAA + more pure rules (replicate `*_inv`), bind via `fill_app`; then fork (`efs`) + progress conjuncts to `wpF`; then adequacy.
      - [ ] A2.4 adequacy: `⊢ wp e {Φ}` ⇒ operational safety + postcondition over `steps` (uses `val_no_prim_step`).
- [x] A3 functional proofs (SC): order book #9 invariant (`best = max occupied`, fall-back) + sweep-VWAP #10 (exact 128-bit notional, Q==0 / over-ask / drained-level, `best_ask ≤ VWAP ≤ touch`)
      — done as standalone pure-Lean proofs (no Iris/program-logic dependency, as the plan intends for the "essentially pure-function" warm-up). Files: `leanlift-iris/LeanliftIris/PhaseA/{Sweep,OrderBook}.lean`; sorry-free (audit: `PhaseA/Axioms.lean`, only `propext`/`Quot.sound`).
      - [x] #10 sweep: exact `filled = min Q total`, completion ⇔ `Q ≤ total`, over-ask, drained-level skip, lower+upper VWAP bracket (`best_ask·filled ≤ notional ≤ touch·filled`, exact `Nat` = no overflow)
      - [x] #9 order book: `maxOcc`/`minOcc` = greatest/least occupied (the `clz`/`ctz` spec), bid+ask fall-back on cancel, microprice bracket `[best_bid, best_ask]`
      - [ ] A3-refine (follow-on, not required by A3): hierarchical-bitmap `clz`/`ctz` refinement of `maxOcc`/`minOcc` (bit-vector proof); optional two-engine equivalence `sweep_linear == prefix.query`
- [ ] A4 first concurrent proof (SC): Treiber stack #7 linearizable via a logically-atomic triple (reclamation deferred) — needs A1/A2 first

## Phase B — weak-memory layer (long pole; GATE after Phase A go/no-go)
- [ ] B1 C11 release-acquire+relaxed op-sem for `λ-conc` (prefer operational view-based, à la iRC11)
- [ ] B2 weak-memory assertions: rel/acq points-to, objective/subjective split, fences, the StoreLoad/`seq_cst` edge
- [ ] B3 SPSC ring #1 under acq/rel (smallest honest weak-memory proof)
- [ ] B4 seqlock #3 + SPMC broadcast #5 (torn-read freedom under the fence discipline)
- [ ] B5 Chase–Lev #8 (marquee): correct WITH `seq_cst` fence, and exhibit acquire/release is insufficient
- [ ] B6 hazard-pointer reclamation #7 under weak memory (publish-then-revalidate; bounded garbage)

## Phase C — linearizability & prophecy
- [ ] C1 reusable logically-atomic triple library (generalize A4)
- [ ] C2 prophecy variables for future-dependent LPs: MPSC #2 stamp publish, Chase–Lev #8 last-element race

## Phase D — integration with leanlift
- [ ] D1 lane boundary: separate `[IRIS]` package, off-CI; `ci.sh` only checks it builds + is sorry-free
- [ ] D2 combined certificate: leanlift SC-model ∧ Iris-lane weak-memory/linearizability; document trust boundaries
- [ ] D3 docs disclaimer: leanlift's automated families do NOT prove memory-order correctness — only `[IRIS]` does

## Phase E — Rust variant (AFTER the C++ corpus)
- [ ] E1 sequential slice via Aeneas → Lean (order book, sweep, bitmap in safe Rust) — reuses leanlift's existing Rust path
- [ ] E2 automated weak-memory screening: Loom (+ optionally Kani/Shuttle) over the concurrency cores; tag `[LOOM]`, off-CI
- [ ] E3 deductive lane — pick: Verus (SMT, ~SC permission model) OR RustBelt-style Iris-in-Lean (full iRC11, reuses Phase B)
- [ ] E4 certificate seam: Aeneas ∧ Loom ∧ (Verus|Iris); document which axis each tool owns
- [ ] note: Aeneas itself covers ONLY the sequential slice — atomics/`unsafe` are outside its model (same boundary as C++)

## Cross-cutting (every phase)
- [ ] keep proofs sorry-free; verify with `#print axioms`
- [ ] adversarial spec review + a "teeth" discrimination test per structure (a wrong variant must fail to verify)
- [ ] watch the Lean generalized/setoid-rewriting gap (highest risk; flagged by Eileen and the community)

## Recommendation
Time-box **Phase 0 + Phase A** as a spike (low-risk, reuses upstream, already
beyond leanlift's SC model). Treat **Phase B** as a separately-funded research
effort with its own go/no-go.
