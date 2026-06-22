/-
Phase B (step 8) — hazard-pointer reclamation (`#7`): why safe reclamation needs
a StoreLoad fence.

A hazard-pointer scheme lets readers safely dereference nodes a concurrent
reclaimer may be freeing. The protocol has two sides, each a **store→load**:

  * **reader** — *publish* the node into its hazard slot (`hp := node`), then
    *revalidate* by re-reading the shared pointer; dereference only if the node is
    still installed (the reclaimer had not retired it from the reader's view);
  * **reclaimer** — *retire* the node (unlink / mark it removed), then *scan* the
    hazard slots; free it only if no slot protects it (no reader had published it
    from the reclaimer's view).

Use-after-free happens exactly when **both** sides win the race: the reader
revalidates successfully (sees the node still live) *and* the reclaimer frees it
(sees no hazard). For that, each side's *load* must miss the other side's *store*
— i.e. both read the stale pre-store value. That is the **store-buffering** shape
again, now two-sided: publish-then-revalidate ∥ retire-then-scan. It is precisely
why the hazard-pointer algorithm specifies a StoreLoad barrier (a `seq_cst` fence)
on both sides.

So, as with the Chase–Lev deque, the two halves are corollaries of the
store-buffering results. Modeling `hp` (hazard slot) and `ret` (retired marker)
both starting unprotected (`0`):

  * `hp_use_after_free_relacq` — under release/acquire the reader dereferences a
    node the reclaimer concurrently frees (UAF), from `sb_admits_reorder`:
    **acquire/release is insufficient** for safe reclamation.
  * `hp_sc_no_use_after_free` — under seq_cst no interleaving lets both win, from
    `sb_sc_no_both_zero`: the StoreLoad fence is exactly what makes reclamation
    safe.

Core Lean, sorry-free.
-/
import LeanliftIris.PhaseB.Machine
import LeanliftIris.PhaseB.SeqCst

namespace LeanliftIris.PhaseB

section HazardPtr
variable (hp ret : Loc)

/-- The reclamation race as a two-thread program. Reader: publish the node into
its hazard slot (`hp := 1`, release) then acquire-read the retired marker `ret` to
revalidate. Reclaimer: retire the node (`ret := 1`, release) then acquire-read the
hazard slot `hp` to scan. Both markers start `0` (unprotected / not retired). -/
def hpProtocol : List Thread :=
  [([.wr hp 1 .rel, .rd ret .acq], View.bot, []),
   ([.wr ret 1 .rel, .rd hp .acq], View.bot, [])]

/-- The reader dereferences the node iff its revalidation read of `ret` still saw
the node *not* retired (`0`) — from the reader's view the reclaimer had not yet
unlinked it. -/
def readerDerefs (C : Config) : Prop := (C.1[0]?).map (fun th => th.2.2) = some [0]

/-- The reclaimer frees the node iff its scan of `hp` saw *no* hazard (`0`) — from
the reclaimer's view no reader had published it. -/
def reclaimerFrees (C : Config) : Prop := (C.1[1]?).map (fun th => th.2.2) = some [0]

/-- **Release/acquire is insufficient — use-after-free.** There is an execution in
which the reader dereferences the node *and* the reclaimer frees the same node:
the reader publishes its hazard but its revalidation misses the retire, while the
reclaimer's scan misses the hazard — each acquire-load reads the stale `0`. This
is two-sided store buffering (`sb_admits_reorder`): without a StoreLoad fence the
hazard-pointer scheme is unsound. -/
theorem hp_use_after_free_relacq (hhr : hp ≠ ret) :
    ∃ C : Config, Steps (hpProtocol hp ret, initMem) C ∧ readerDerefs C ∧ reclaimerFrees C := by
  simpa only [hpProtocol, readerDerefs, reclaimerFrees] using sb_admits_reorder hp ret hhr

/-- **Seq-cst makes reclamation safe.** Reading `s.r1`/`s.r2` as the reader's
revalidation of `ret` and the reclaimer's scan of `hp`, no seq-cst execution lets
*both* read the stale `0` — so the reader can never dereference a node the
reclaimer frees. This is the universal store-buffering guarantee
(`sb_sc_no_both_zero`): the publish-then-revalidate / retire-then-scan StoreLoad
fences are exactly what hazard pointers require. -/
theorem hp_sc_no_use_after_free (hhr : hp ≠ ret) {s : SBState}
    (h : SBSteps hp ret SBState.init s) :
    ¬ (s.r1 = some 0 ∧ s.r2 = some 0) :=
  sb_sc_no_both_zero hp ret hhr h

end HazardPtr

end LeanliftIris.PhaseB
