/-
Phase A3 — axiom audit. Each `#print axioms` below must report
"depends on no axioms" (or only the trusted kernel axioms). leanlift's invariant
is that verification proofs are sorry-free and kernel-checked.
-/
import LeanliftIris.PhaseA.Sweep
import LeanliftIris.PhaseA.OrderBook

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

end LeanliftIris.PhaseA
