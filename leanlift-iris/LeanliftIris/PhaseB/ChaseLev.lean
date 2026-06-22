/-
Phase B (step 6) — the Chase–Lev work-stealing deque (`#8`), the marquee.

The whole reason this lane exists is to *see the memory model*: to find the one
place where release/acquire is not enough and a `seq_cst` fence is mandatory, and
to prove both halves. That place is the **last-element race** in the Chase–Lev
deque (Lê et al., "Correct and Efficient Work-Stealing for Weak Memory Models").

When the deque holds a single element, the owner's `take` and a thief's `steal`
contend for it:

  * `take` (owner) claims by writing the **bottom** index, then reading **top** to
    check the thief has not already taken it;
  * `steal` (thief) claims by writing the **top** index, then reading **bottom**
    to check the element is still in range.

Each side writes *its* index and then reads *the other's* index — and proceeds to
pop the element iff that read still shows the unclaimed value. That is exactly the
**store-buffering** shape (`store x; load y ∥ store y; load x`). The infamous bug
is the SB weak outcome: both reads see the *stale* pre-claim value, so **both**
pop the same element — the deque hands one item out twice.

So the two halves of the marquee are corollaries of the store-buffering results
already proved:

  * `chase_lev_double_claim_relacq` — under release/acquire the double-claim is a
    real execution (from `sb_admits_reorder`): **acquire/release is insufficient.**
  * `chase_lev_sc_no_double_claim` — under seq_cst it is impossible for *every*
    interleaving (from `sb_sc_no_both_zero`): the `seq_cst` fence is exactly what
    makes the deque correct.

(The two halves necessarily live on different machines — the rel/acq `Machine`
and the seq-cst transition system — because that *is* the point: the same race is
admitted by one memory model and forbidden by the stronger one.)

Core Lean, sorry-free.
-/
import LeanliftIris.PhaseB.Machine
import LeanliftIris.PhaseB.SeqCst

namespace LeanliftIris.PhaseB

section ChaseLev
variable (bot top : Loc)

/-- The single-element race as a two-thread program: owner `take` writes `bot`
(release) then acquire-reads `top`; thief `steal` writes `top` (release) then
acquire-reads `bot`. Both indices start at `0` (unclaimed). -/
def takeSteal : List Thread :=
  [([.wr bot 1 .rel, .rd top .acq], View.bot, []),
   ([.wr top 1 .rel, .rd bot .acq], View.bot, [])]

/-- The owner pops the element iff its check of `top` still read the unclaimed
`0` (the thief had not yet published its claim, from the owner's view). -/
def ownerClaims (C : Config) : Prop := (C.1[0]?).map (fun th => th.2.2) = some [0]

/-- The thief steals the element iff its check of `bot` still read the unclaimed
`0` (the owner had not yet published its claim, from the thief's view). -/
def thiefClaims (C : Config) : Prop := (C.1[1]?).map (fun th => th.2.2) = some [0]

/-- **Release/acquire is insufficient — the Lê et al. bug.** There is an execution
of the last-element race in which the owner *and* the thief both claim the same
element: each writes its own index but then acquire-reads the other's *stale*
unclaimed value, so both believe the element is theirs. The deque pops one item
twice. This is store buffering (`sb_admits_reorder`) in a deque costume. -/
theorem chase_lev_double_claim_relacq (hbt : bot ≠ top) :
    ∃ C : Config, Steps (takeSteal bot top, initMem) C ∧ ownerClaims C ∧ thiefClaims C := by
  simpa only [takeSteal, ownerClaims, thiefClaims] using sb_admits_reorder bot top hbt

/-- **Seq-cst makes it correct.** Reading `s.r1`/`s.r2` as the owner's check of
`top` and the thief's check of `bot`, no seq-cst execution of the last-element
race lets *both* read the stale unclaimed `0` — so the owner and thief can never
both claim the element. This is the universal store-buffering guarantee
(`sb_sc_no_both_zero`): the `seq_cst` fence's StoreLoad ordering is precisely what
the Chase–Lev deque needs. -/
theorem chase_lev_sc_no_double_claim (hbt : bot ≠ top) {s : SBState}
    (h : SBSteps bot top SBState.init s) :
    ¬ (s.r1 = some 0 ∧ s.r2 = some 0) :=
  sb_sc_no_both_zero bot top hbt h

end ChaseLev

end LeanliftIris.PhaseB
