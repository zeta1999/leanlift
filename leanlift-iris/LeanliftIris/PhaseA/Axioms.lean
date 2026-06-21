/-
Phase A3 — axiom audit. Each `#print axioms` below must report
"depends on no axioms" (or only the trusted kernel axioms). leanlift's invariant
is that verification proofs are sorry-free and kernel-checked.
-/
import LeanliftIris.PhaseA.Sweep
import LeanliftIris.PhaseA.OrderBook
import LeanliftIris.PhaseA.Lang
import LeanliftIris.PhaseA.HeapRes
import LeanliftIris.PhaseA.Wp
import LeanliftIris.PhaseA.WpLifting

namespace LeanliftIris.PhaseA

-- Sweep (#10)
#print axioms sweepLinear_filled
#print axioms sweepLinear_complete
#print axioms sweep_over_ask
#print axioms sweep_Q_zero
#print axioms linearAux_drained
#print axioms sweep_lower
#print axioms sweep_upper

-- Order book (#9)
#print axioms maxOcc_some_iff
#print axioms maxOcc_fallback
#print axioms minOcc_some_iff
#print axioms minOcc_fallback
#print axioms microprice_bracket

-- λ-conc language (A1)
#print axioms head_not_val
#print axioms ex_load_after_alloc
#print axioms ex_cas_success
#print axioms ex_fork
#print axioms fill_app
#print axioms val_no_prim_step

-- Heap resource / points-to (A2 step 1). Iris-model proofs legitimately use the
-- classical axioms; the leanlift invariant is the ABSENCE of `sorryAx`.
#print axioms pointsTo_agree
#print axioms wp_unfold
#print axioms wp_value
#print axioms prim_step_load_inv
#print axioms wp_lift_step
#print axioms stateInterp_pointsTo_agree
#print axioms wp_load
#print axioms prim_step_store_inv
#print axioms wp_store
#print axioms wp_pure_det
#print axioms wp_if_true

end LeanliftIris.PhaseA
