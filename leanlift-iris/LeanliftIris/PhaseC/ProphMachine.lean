/-
Phase C (step 4) — **operational** prophecy: `NewProph` / `Resolve` as real machine
transitions, and the soundness payoff proved over the transition system.

`Prophecy.lean` modeled prophecy soundness *abstractly*: the prophesied value may
be set equal to a resolution that is a function of the physical state
(`proph_sound`). The remaining obligation (flagged in `PLAN-concurrency.md` C2) is
to make resolution an actual **operational step** and re-prove soundness over the
machine — so the discipline ("resolution is physical, the prophesied value is
chosen from the future") is forced by the operational semantics, not assumed.

The machine is tiny: a state carries a fresh-id counter and a per-prophecy
**resolution map** (`none` = unresolved). Two transitions:

  * `newproph` — allocate a fresh prophecy id;
  * `resolve p w` — record that prophecy `p` resolved to the physical value `w`,
    **guarded** so a prophecy is resolved at most once (first resolution wins).

The two facts that make prophecy sound, now operational:

  * `resolved_stable` — a resolution is **permanent**: once `p` resolves to `w`, it
    stays `w` along every later execution. So the prophesied value, chosen as the
    *eventual* resolution, can never be contradicted later.
  * `proph_predicts_future` — the payoff: the prophesied value read from the final
    state equals the value the prophecy actually resolved to mid-execution. The
    prophecy "from the future" is correct, by construction of the operational
    semantics. (`no_double_resolve` records the at-most-once guarantee the guard
    enforces.)

Core Lean, sorry-free.
-/
import LeanliftIris.PhaseC.Prophecy

namespace LeanliftIris.PhaseC

/-! ## The prophecy machine -/

/-- State of the prophecy machine: the next fresh prophecy id, and a resolution
map (`none` = not yet resolved). -/
structure PState where
  next : Nat
  resolved : Nat → Option Int

/-- The initial state: no prophecies allocated, none resolved. -/
def PState.init : PState := ⟨0, fun _ => none⟩

/-- One operational step. `newproph` allocates a fresh id; `resolve` records a
prophecy's physical resolution, guarded so a prophecy resolves **at most once**. -/
inductive PStep : PState → PState → Prop where
  | newproph (s : PState) :
      PStep s { s with next := s.next + 1 }
  | resolve (s : PState) (pr : Nat) (v : Int) (h : s.resolved pr = none) :
      PStep s { s with resolved := fun q => if q = pr then some v else s.resolved q }

/-- Reflexive-transitive closure of `PStep`. -/
inductive PSteps : PState → PState → Prop where
  | refl (s : PState) : PSteps s s
  | step {s s' s'' : PState} : PStep s s' → PSteps s' s'' → PSteps s s''

/-! ## Resolution is permanent -/

/-- **A resolution is permanent.** Once prophecy `p` has resolved to `w`, it stays
`w` along every later execution — the resolution map only ever fills in `none`
slots (the `resolve` guard forbids overwriting). This is what makes the prophesied
value (chosen as the eventual resolution) well-defined and never contradicted. -/
theorem resolved_stable {s s' : PState} (h : PSteps s s') :
    ∀ (p : Nat) (w : Int), s.resolved p = some w → s'.resolved p = some w := by
  induction h with
  | refl => intro _ _ hr; exact hr
  | step hstep _ ih =>
      intro p w hr
      apply ih
      cases hstep with
      | newproph => exact hr
      | resolve pr v hpr =>
          by_cases hpq : p = pr
          · subst hpq; rw [hpr] at hr; simp at hr
          · simpa [hpq] using hr

/-- **At most once.** A `resolve` step never overwrites an already-resolved
prophecy: if `p` was resolved to `w` before the step, it is still `w` after. (The
guard makes a second resolution of the same prophecy impossible; here we record
that resolutions, in particular, are stable across a single step.) -/
theorem no_double_resolve {s s' : PState} (hstep : PStep s s') (p : Nat) (w : Int)
    (hr : s.resolved p = some w) : s'.resolved p = some w :=
  resolved_stable (PSteps.step hstep (PSteps.refl _)) p w hr

/-! ## Operational soundness: the prophecy predicts the future -/

/-- The prophesied-value assignment read off a state: each prophecy's value is its
resolution (a default for the not-yet-resolved). This is a function of the
**physical** state only — the operational witness for `Prophecy.proph_sound`. -/
def assign (s : PState) : Nat → Int := fun p => (s.resolved p).getD 0

/-- The assignment is consistent with every recorded resolution. -/
theorem assign_consistent (s : PState) (p : Nat) (w : Int) (h : s.resolved p = some w) :
    assign s p = w := by simp [assign, h]

/-- **Operational prophecy soundness — the prophecy predicts the future.** The
prophesied value read from the final state equals the value the prophecy actually
resolved to mid-execution. So allocating a prophecy whose value is its *eventual*
resolution is sound: by `resolved_stable` the mid-execution resolution survives to
the end, and the final assignment agrees with it. This discharges the operational
half of C2 — resolution is a genuine machine step, and the "value from the future"
is provably the value that gets resolved. -/
theorem proph_predicts_future {s0 sR sF : PState}
    (hR : PSteps sR sF) (p : Nat) (w : Int) (hr : sR.resolved p = some w) :
    assign sF p = w :=
  assign_consistent sF p w (resolved_stable hR p w hr)

/-- And `assign` is exactly a legitimate `resolve` for the abstract soundness
theorem: the prophesied value can be chosen equal to it, uniquely. -/
theorem assign_proph_sound (s : PState) (p : Nat) :
    ∃ pv : Int, pv = assign s p ∧ ∀ y : Int, y = assign s p → y = pv :=
  proph_sound (fun st => assign st p) s

end LeanliftIris.PhaseC
