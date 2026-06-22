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

end LeanliftIris.PhaseB
