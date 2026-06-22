/-
Phase B (step 5, start) — the `seq_cst` extension: a global SC view that forbids
store→load reordering.

`Machine.lean` proved (`sb_admits_reorder`) that release/acquire **admits** the
store-buffering weak outcome `r1 = r2 = 0`: each thread, having only rel/acq
edges, may read the other's stale initial value. That is the store→load reorder
the corpus' Chase–Lev deque (`#8`) needs a `seq_cst` fence to rule out — and the
existing model cannot rule it out, because its per-operation `store`/`load` treat
`.sc` exactly like rel/acq (a *local* view transfer, no global order).

`seq_cst` is genuinely stronger: all SC operations are totally ordered, and that
order is global. We capture its store→load-forbidding power operationally with the
standard device — a single **global SC view** `Vsc` threaded through the machine:

  * an **SC store** publishes its write's timestamp into `Vsc` (and the writer
    absorbs `Vsc`, so it observes everything SC-before);
  * an **SC load** may only read a message whose timestamp is `≥ Vsc[l]` — it
    cannot read behind the global SC frontier.

That single lower-bound is what kills store-buffering. The cyclic argument: for
both reads to be `0`, T1's load of `y` must precede T2's store of `y` (else `Vsc y
≥ 1` blocks the stale read), and symmetrically T2's load of `x` must precede T1's
store of `x`; with each thread's store before its own load (program order) this
closes a cycle `T1.st < T1.ld < T2.st < T2.ld < T1.st`. We prove the local
crux concretely here:

  * `sc_reads_determined` — the SC analogue of `reads_determined`: an SC load
    whose `Vsc` already reflects a store is forced to read it.
  * `sb_sc_reads_one` / `sb_sc_blocks_stale_load` — in the SB program, once both
    SC stores have run, `Vsc x = 1`, so T2's SC load of `x` is *determined* to
    read `1`; the exact stale-read step that `sb_admits_reorder` took under rel/acq
    is **not a legal SC step**.

The full "no SC execution yields both-zero" universal (an induction over the
interleaving relation) is the next increment; this file lays the model and proves
the crux that makes it go through. Core Lean, sorry-free.
-/
import LeanliftIris.PhaseB.Machine

namespace LeanliftIris.PhaseB

/-! ## The SC-augmented operations

A global SC view `Vsc` records, per location, the SC frontier: the timestamp of
the latest SC store there in the global SC order. -/

/-- **SC store** of `v` at `l` by a thread with view `V`, against global SC view
`Vsc`. Picks a fresh timestamp, publishes it into `Vsc`, makes the writer absorb
`Vsc`, and releases the writer's (SC-absorbed) view. Returns the new memory, the
writer's advanced view, and the advanced global SC view. -/
def scStore (M : Mem) (V Vsc : View) (l : Loc) (v : Int) : Mem × View × View :=
  let t    := maxTs M l + 1
  let Vsc' := View.join Vsc (View.singleton l t)
  let V'   := View.join (View.join V Vsc') (View.singleton l t)
  (push M l ⟨v, t, V'⟩, V', Vsc')

/-- An **SC load** may read `m` only if it is in the history, is not older than the
thread has already observed, **and is not older than the global SC frontier**
(`Vsc l ≤ m.ts`). That last conjunct is the seq-cst strengthening over acquire. -/
def canLoadSC (M : Mem) (V Vsc : View) (l : Loc) (m : Msg) : Prop :=
  m ∈ M l ∧ V l ≤ m.ts ∧ Vsc l ≤ m.ts

/-- The view a thread holds after an SC load: it absorbs the message's released
view *and* the global SC view. -/
def scLoadView (V Vsc : View) (m : Msg) : View := View.join (View.join V m.rview) Vsc

/-! ## SC machine: thread pool over weak memory **plus** the global SC view -/

/-- An SC machine configuration: thread pool, shared memory, and global SC view. -/
abbrev SCConfig := List Thread × Mem × View

/-- One SC interleaving step. SC stores advance `Vsc`; SC loads must respect it. -/
inductive SCStep : SCConfig → SCConfig → Prop where
  | wr (t1 t2 : List Thread) (ops : List Op) (V : View) (log : List Int)
      (M : Mem) (Vsc : View) (l : Loc) (v : Int) :
      SCStep (t1 ++ (Op.wr l v .sc :: ops, V, log) :: t2, M, Vsc)
             (t1 ++ (ops, (scStore M V Vsc l v).2.1, log) :: t2,
                (scStore M V Vsc l v).1, (scStore M V Vsc l v).2.2)
  | rd (t1 t2 : List Thread) (ops : List Op) (V : View) (log : List Int)
      (M : Mem) (Vsc : View) (l : Loc) (m : Msg) (hcl : canLoadSC M V Vsc l m) :
      SCStep (t1 ++ (Op.rd l .sc :: ops, V, log) :: t2, M, Vsc)
             (t1 ++ (ops, scLoadView V Vsc m, log ++ [m.val]) :: t2, M, Vsc)

/-- Reflexive-transitive closure of `SCStep`. -/
inductive SCSteps : SCConfig → SCConfig → Prop where
  | refl (C : SCConfig) : SCSteps C C
  | step {C C' C'' : SCConfig} : SCStep C C' → SCSteps C' C'' → SCSteps C C''

/-! ## Foundational SC-view lemmas -/

/-- An SC store only advances the global SC view (monotone — the SC frontier never
recedes). -/
theorem scStore_Vsc_mono (M : Mem) (V Vsc : View) (l : Loc) (v : Int) (l' : Loc) :
    Vsc l' ≤ (scStore M V Vsc l v).2.2 l' := by
  simp only [scStore, View.join]; exact Nat.le_max_left _ _

/-- An SC store **publishes**: afterwards the global SC frontier at `l` is at least
the store's (positive) timestamp — so any later SC load of `l` is barred from the
stale initial write. -/
theorem scStore_publishes (M : Mem) (V Vsc : View) (l : Loc) (v : Int) :
    1 ≤ (scStore M V Vsc l v).2.2 l := by
  have h : (View.singleton l (maxTs M l + 1)) l ≤ (scStore M V Vsc l v).2.2 l := by
    simp only [scStore, View.join]; exact Nat.le_max_right _ _
  have hs : (View.singleton l (maxTs M l + 1)) l = maxTs M l + 1 := by
    simp [View.singleton]
  rw [hs] at h; exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h

/-- **SC read-determinism.** A thread whose SC view already reflects the store
`l := v` (`t ≤ Vsc l`) can only SC-load value `v` at `l`, given every write at `l`
from timestamp `t` on has value `v`. The SC analogue of `reads_determined`, using
the *global* SC frontier instead of the thread-local `seen`. -/
theorem sc_reads_determined (M : Mem) (V Vsc : View) (l : Loc) (t : Time) (v : Int)
    (hsc : t ≤ Vsc l) (hwrites : ∀ m, m ∈ M l → t ≤ m.ts → m.val = v) :
    ∀ m, canLoadSC M V Vsc l m → m.val = v := by
  rintro m ⟨hmem, _, hvsc⟩
  exact hwrites m hmem (Nat.le_trans hsc hvsc)

/-! ## Store buffering is forbidden under seq_cst

The all-`sc` SB program `x:=1; r1:=y ∥ y:=1; r2:=x`. We chain the two SC stores
through the global SC view, then show T2's SC load of `x` is forced to read `1`. -/

section SB
variable (x y : Loc)

/-- Memory / global-SC-view after T1's SC store `x := 1`. -/
def scbX     : Mem  := (scStore initMem View.bot View.bot x 1).1
def scbVscX  : View := (scStore initMem View.bot View.bot x 1).2.2
/-- … after T2's SC store `y := 1` (carrying the global SC view forward). -/
def scbXY    : Mem  := (scStore (scbX x) View.bot (scbVscX x) y 1).1
def scbVscXY : View := (scStore (scbX x) View.bot (scbVscX x) y 1).2.2

/-- After both SC stores, the global SC frontier at `x` is `1`. -/
theorem scb_Vsc_x (hxy : x ≠ y) : (scbVscXY x y) x = 1 := by
  simp [scbVscXY, scbVscX, scbX, scStore, View.join, View.singleton, View.bot, maxTs,
    initMem, hxy, Ne.symm hxy]

/-- **Seq-cst forbids the store-buffering stale read.** Once both SC stores have
run, T2's SC load of `x` is *determined* to read `1` — never the stale initial
`0`. This is the StoreLoad guarantee the Chase–Lev fence rests on; contrast
`sb_admits_reorder`, where release/acquire let this very read return `0`. -/
theorem sb_sc_reads_one (hxy : x ≠ y) :
    ∀ m, canLoadSC (scbXY x y) View.bot (scbVscXY x y) x m → m.val = 1 := by
  refine sc_reads_determined _ _ _ _ 1 _ ?_ ?_
  · exact Nat.le_of_eq (scb_Vsc_x x y hxy).symm
  · intro m hmem hts
    -- `x`'s history is [⟨1,1⟩, ⟨0,0⟩]; only the SC store has ts ≥ 1
    simp [scbXY, scbX, scStore, push, maxTs, initMem, hxy, Ne.symm hxy] at hmem
    rcases hmem with h | h <;> subst h
    · rfl
    · simp at hts

/-- **The stale step `sb_admits_reorder` took is not a legal SC step.** Reading
the initial `⟨0,0,⊥⟩` write of `x` violates `canLoadSC`: its timestamp `0` lies
below the global SC frontier `Vsc x = 1`. So the release/acquire weak execution
has no seq-cst counterpart — the model exhibits `sc ≠ acq` exactly where it must. -/
theorem sb_sc_blocks_stale_load (hxy : x ≠ y) :
    ¬ canLoadSC (scbXY x y) View.bot (scbVscXY x y) x ⟨0, 0, View.bot⟩ := by
  rintro ⟨_, _, hsc⟩
  rw [scb_Vsc_x x y hxy] at hsc
  exact absurd hsc (by decide)

end SB

/-! ## The full universal: no SC execution of SB yields the weak outcome

The results above show the *one* stale step is blocked. The genuine theorem is
universal: **no** interleaving of the all-`sc` SB program ends with both reads
`0`. The generic list-pool `SCStep` is awkward to induct over, so we model SB on
an explicit two-thread transition system whose store/load transitions mirror
`scStore`/`canLoadSC` exactly, and prove impossibility by an invariant. -/

/-! Two reusable memory facts about an SC store. -/
section MemLemmas

/-- An SC store to `l` keeps every existing value-`v` write at `l` (those with
`ts ≥ 1`) and its own fresh write is also `v` — so a single-published-value
location stays single-valued. -/
theorem scStore_preserves_val (M : Mem) (V Vsc : View) (l : Loc) (v : Int)
    (hM : ∀ m, m ∈ M l → 1 ≤ m.ts → m.val = v) :
    ∀ m, m ∈ (scStore M V Vsc l v).1 l → 1 ≤ m.ts → m.val = v := by
  intro m hm hts
  simp only [scStore, push] at hm
  split at hm
  · rcases List.mem_cons.mp hm with h | h
    · rw [h]
    · exact hM m h hts
  · exact hM m hm hts

/-- An SC store to `l` leaves any *other* location's history untouched. -/
theorem scStore_other (M : Mem) (V Vsc : View) (l : Loc) (v : Int) (l' : Loc) (h : l ≠ l') :
    (scStore M V Vsc l v).1 l' = M l' := by
  simp [scStore, push, Ne.symm h]

end MemLemmas

/-- An explicit two-thread state for the SB program. `pc ∈ {0:pre-store,
1:stored, 2:done}`; `r1`/`r2` record the read results; `V1`/`V2` the thread
views; `M`/`Vsc` the shared memory and global SC frontier. -/
structure SBState where
  pc1 : Nat
  pc2 : Nat
  M   : Mem
  Vsc : View
  V1  : View
  V2  : View
  r1  : Option Int
  r2  : Option Int

namespace SBState
/-- The SB initial state: both threads at pc 0, fresh memory, no reads. -/
def init : SBState := ⟨0, 0, initMem, View.bot, View.bot, View.bot, none, none⟩
end SBState

/-- One SC step of the SB program. Stores/loads are exactly `scStore`/`canLoadSC`:
T1 does `x:=1`(sc) then `r1:=y`(sc); T2 does `y:=1`(sc) then `r2:=x`(sc). -/
inductive SBStep (x y : Loc) : SBState → SBState → Prop where
  | st1 (s : SBState) (h : s.pc1 = 0) :
      SBStep x y s
        { s with pc1 := 1,
                 M   := (scStore s.M s.V1 s.Vsc x 1).1,
                 V1  := (scStore s.M s.V1 s.Vsc x 1).2.1,
                 Vsc := (scStore s.M s.V1 s.Vsc x 1).2.2 }
  | st2 (s : SBState) (h : s.pc2 = 0) :
      SBStep x y s
        { s with pc2 := 1,
                 M   := (scStore s.M s.V2 s.Vsc y 1).1,
                 V2  := (scStore s.M s.V2 s.Vsc y 1).2.1,
                 Vsc := (scStore s.M s.V2 s.Vsc y 1).2.2 }
  | ld1 (s : SBState) (m : Msg) (h : s.pc1 = 1) (hcl : canLoadSC s.M s.V1 s.Vsc y m) :
      SBStep x y s { s with pc1 := 2, V1 := scLoadView s.V1 s.Vsc m, r1 := some m.val }
  | ld2 (s : SBState) (m : Msg) (h : s.pc2 = 1) (hcl : canLoadSC s.M s.V2 s.Vsc x m) :
      SBStep x y s { s with pc2 := 2, V2 := scLoadView s.V2 s.Vsc m, r2 := some m.val }

/-- Reflexive-transitive closure of `SBStep`. -/
inductive SBSteps (x y : Loc) : SBState → SBState → Prop where
  | refl (s : SBState) : SBSteps x y s s
  | step {s s' s'' : SBState} : SBStep x y s s' → SBSteps x y s' s'' → SBSteps x y s s''

/-- The reachability invariant. The last conjunct is the goal; the others (each
store raises its frontier; each location stays single-valued; an unfinished read
is `none`) are the supporting facts that keep it inductive. -/
def Inv (x y : Loc) (s : SBState) : Prop :=
  (1 ≤ s.pc1 → 1 ≤ s.Vsc x) ∧
  (1 ≤ s.pc2 → 1 ≤ s.Vsc y) ∧
  (∀ m, m ∈ s.M x → 1 ≤ m.ts → m.val = 1) ∧
  (∀ m, m ∈ s.M y → 1 ≤ m.ts → m.val = 1) ∧
  (s.pc1 < 2 → s.r1 = none) ∧
  (s.pc2 < 2 → s.r2 = none) ∧
  ¬ (s.r1 = some 0 ∧ s.r2 = some 0)

/-- The invariant holds initially. -/
theorem Inv_init (x y : Loc) : Inv x y SBState.init := by
  refine ⟨fun h => ?_, fun h => ?_, ?_, ?_, fun _ => rfl, fun _ => rfl, by simp [SBState.init]⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · intro m hm hts
    simp only [SBState.init, initMem, List.mem_singleton] at hm
    subst hm; exact absurd hts (by decide)
  · intro m hm hts
    simp only [SBState.init, initMem, List.mem_singleton] at hm
    subst hm; exact absurd hts (by decide)

/-- The invariant is preserved by every SC step. The two load cases are the crux:
a read whose frontier already reflects the *other* thread's store (because that
store has run) is forced off the stale `0`. -/
theorem Inv_step (x y : Loc) (hxy : x ≠ y) {s s' : SBState}
    (hI : Inv x y s) (hstep : SBStep x y s s') : Inv x y s' := by
  cases hstep with
  | st1 ht =>
      obtain ⟨ha, hb, hfx, hfy, hi1, hi2, hc⟩ := hI
      refine ⟨fun _ => scStore_publishes s.M s.V1 s.Vsc x 1,
              fun hp => Nat.le_trans (hb hp) (scStore_Vsc_mono s.M s.V1 s.Vsc x 1 y),
              scStore_preserves_val s.M s.V1 s.Vsc x 1 hfx, ?_,
              fun _ => hi1 (by omega), hi2, hc⟩
      intro m hm hts
      change m ∈ (scStore s.M s.V1 s.Vsc x 1).1 y at hm
      rw [scStore_other s.M s.V1 s.Vsc x 1 y hxy] at hm
      exact hfy m hm hts
  | st2 ht =>
      obtain ⟨ha, hb, hfx, hfy, hi1, hi2, hc⟩ := hI
      refine ⟨fun hp => Nat.le_trans (ha hp) (scStore_Vsc_mono s.M s.V2 s.Vsc y 1 x),
              fun _ => scStore_publishes s.M s.V2 s.Vsc y 1, ?_,
              scStore_preserves_val s.M s.V2 s.Vsc y 1 hfy,
              hi1, fun _ => hi2 (by omega), hc⟩
      intro m hm hts
      change m ∈ (scStore s.M s.V2 s.Vsc y 1).1 x at hm
      rw [scStore_other s.M s.V2 s.Vsc y 1 x (Ne.symm hxy)] at hm
      exact hfx m hm hts
  | ld1 m ht hcl =>
      obtain ⟨ha, hb, hfx, hfy, hi1, hi2, hc⟩ := hI
      refine ⟨fun _ => ha (by omega), hb, hfx, hfy,
              fun h => absurd h (Nat.lt_irrefl 2), hi2, ?_⟩
      rintro ⟨h1, h2⟩
      have e0 : m.val = 0 := by simpa using h1
      have hpc2 : 1 ≤ s.pc2 := by
        rcases Nat.lt_or_ge s.pc2 1 with hlt | hge
        · exfalso; have hr : s.r2 = none := hi2 (by omega); rw [hr] at h2; simp at h2
        · exact hge
      have e1 : m.val = 1 := hfy m hcl.1 (Nat.le_trans (hb hpc2) hcl.2.2)
      omega
  | ld2 m ht hcl =>
      obtain ⟨ha, hb, hfx, hfy, hi1, hi2, hc⟩ := hI
      refine ⟨ha, fun _ => hb (by omega), hfx, hfy,
              hi1, fun h => absurd h (Nat.lt_irrefl 2), ?_⟩
      rintro ⟨h1, h2⟩
      have e0 : m.val = 0 := by simpa using h2
      have hpc1 : 1 ≤ s.pc1 := by
        rcases Nat.lt_or_ge s.pc1 1 with hlt | hge
        · exfalso; have hr : s.r1 = none := hi1 (by omega); rw [hr] at h1; simp at h1
        · exact hge
      have e1 : m.val = 1 := hfx m hcl.1 (Nat.le_trans (ha hpc1) hcl.2.2)
      omega

/-- The invariant is preserved along any SC execution. -/
theorem Inv_steps (x y : Loc) (hxy : x ≠ y) {s s' : SBState}
    (h : SBSteps x y s s') : Inv x y s → Inv x y s' := by
  induction h with
  | refl _ => exact id
  | step hstep _ ih => exact fun hI => ih (Inv_step x y hxy hI hstep)

/-- **Store buffering is forbidden under seq_cst (universal).** No interleaved SC
execution of the all-`sc` SB program `x:=1; r1:=y ∥ y:=1; r2:=x` ends with both
reads `0`. Each SC store raises the global SC frontier, and a read whose frontier
already reflects the other store is forced off the stale value — closing the
`st < ld < st < ld < st` cycle the weak outcome would need. Contrast
`sb_admits_reorder`, where release/acquire admits exactly this outcome: this is
the StoreLoad guarantee the Chase–Lev deque's `seq_cst` fence buys. -/
theorem sb_sc_no_both_zero (x y : Loc) (hxy : x ≠ y) {s : SBState}
    (h : SBSteps x y SBState.init s) : ¬ (s.r1 = some 0 ∧ s.r2 = some 0) :=
  (Inv_steps x y hxy h (Inv_init x y)).2.2.2.2.2.2

end LeanliftIris.PhaseB
