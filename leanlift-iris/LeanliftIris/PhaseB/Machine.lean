/-
Phase B (step 2) — a thread-pool machine over the weak-memory model.

`WeakMem.lean` gave the per-operation `store`/`load` view machinery and proved
release/acquire faithfulness in isolation. Here we lift it into an actual
**concurrent operational semantics**: a pool of threads, each a sequence of
memory operations with its own view, interleaving over the shared weak memory.
This is the substrate a weak-memory program logic (B2) will be defined over.

We validate it by *running* the message-passing program as a real interleaved
execution (`mp_machine_run`): producer `d:=42`(rlx); `f:=1`(rel) ∥ consumer
acquire-load `f`; load `d` — there is an execution in which the consumer reads
the flag `1` and then the payload `42`. Core Lean, sorry-free.
-/
import LeanliftIris.PhaseB.WeakMem

namespace LeanliftIris.PhaseB

/-- A memory operation a thread can perform. -/
inductive Op
  | wr (l : Loc) (v : Int) (o : MemOrd)
  | rd (l : Loc) (o : MemOrd)
deriving Repr

/-- A thread: its remaining operations, its current view, and the values it has
read (its log). -/
abbrev Thread := List Op × View × List Int

/-- A machine configuration: the thread pool and the shared weak memory. -/
abbrev Config := List Thread × Mem

/-- One interleaving step: some thread executes its next operation. A write
appends a message and advances the writer's view; a read picks any message it is
allowed to load, logs the value, and advances the reader's view. -/
inductive Step : Config → Config → Prop where
  | wr (t1 t2 : List Thread) (ops : List Op) (V : View) (log : List Int)
      (M : Mem) (l : Loc) (v : Int) (o : MemOrd) :
      Step (t1 ++ (Op.wr l v o :: ops, V, log) :: t2, M)
           (t1 ++ (ops, (store M V l v o).2, log) :: t2, (store M V l v o).1)
  | rd (t1 t2 : List Thread) (ops : List Op) (V : View) (log : List Int)
      (M : Mem) (l : Loc) (o : MemOrd) (m : Msg) (hcl : canLoad M V l m) :
      Step (t1 ++ (Op.rd l o :: ops, V, log) :: t2, M)
           (t1 ++ (ops, loadView V l m o, log ++ [m.val]) :: t2, M)

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : Config → Config → Prop where
  | refl (C : Config) : Steps C C
  | step {C C' C'' : Config} : Step C C' → Steps C' C'' → Steps C C''

/-! ## Message passing as a real interleaved execution

Threads `d`, `f`; producer (thread 0) and consumer (thread 1). We exhibit the
interleaving producer;producer;consumer;consumer and read off the consumer's log:
`[1, 42]` — it sees the published flag and then the published payload. -/

/-- The producer's view after `d:=42` relaxed. -/
private def mpV1 (d : Loc) : View := (store initMem View.bot d 42 .rlx).2
/-- The memory after `d:=42` relaxed. -/
private def mpM1 (d : Loc) : Mem := (store initMem View.bot d 42 .rlx).1
/-- The memory after both producer writes. -/
private def mpM2 (d f : Loc) : Mem := (store (mpM1 d) (mpV1 d) f 1 .rel).1

/-- **Message passing runs.** There is an interleaved execution of producer
`d:=42`(rlx);`f:=1`(rel) and consumer `rd f`(acq);`rd d`(rlx) in which the
consumer's log ends `[1, 42]`: it observes the published flag and payload. -/
theorem mp_machine_run (d f : Loc) (hdf : d ≠ f) :
    ∃ C : Config,
      Steps ([([.wr d 42 .rlx, .wr f 1 .rel], View.bot, []),
              ([.rd f .acq, .rd d .rlx], View.bot, [])], initMem) C ∧
      (C.1[1]?).map (fun th => th.2.2) = some [1, 42] := by
  refine ⟨([([], (store (mpM1 d) (mpV1 d) f 1 .rel).2, []),
            ([], loadView (loadView View.bot f (storeMsg (mpM1 d) (mpV1 d) f 1 .rel) .acq) d
                  (storeMsg initMem View.bot d 42 .rlx) .rlx, [1, 42])], mpM2 d f), ?_, rfl⟩
  -- producer writes d (relaxed)
  refine Steps.step (Step.wr [] [_] [.wr f 1 .rel] View.bot [] initMem d 42 .rlx) ?_
  -- producer writes f (release)
  refine Steps.step (Step.wr [] [_] [] (mpV1 d) [] (mpM1 d) f 1 .rel) ?_
  -- consumer acquire-loads f (reads the release write, value 1)
  refine Steps.step
    (Step.rd [_] [] [.rd d .rlx] View.bot [] (mpM2 d f) f .acq
      (storeMsg (mpM1 d) (mpV1 d) f 1 .rel)
      ⟨by simp [mpM2, store, push, storeMsg], Nat.zero_le _⟩) ?_
  -- consumer relaxed-loads d (its view[d] is now 1 = the payload's ts, so reads 42)
  refine Steps.step
    (Step.rd [_] [] [] (loadView View.bot f (storeMsg (mpM1 d) (mpV1 d) f 1 .rel) .acq) [1]
      (mpM2 d f) d .rlx (storeMsg initMem View.bot d 42 .rlx)
      ⟨by simp [mpM2, mpM1, store, push, storeMsg, maxTs, initMem, hdf, Ne.symm hdf],
       by simp [loadView, storeMsg, mpV1, mpM1, store, View.join, View.bot,
            View.singleton, maxTs, initMem, hdf, Ne.symm hdf]⟩) ?_
  exact Steps.refl _

end LeanliftIris.PhaseB
