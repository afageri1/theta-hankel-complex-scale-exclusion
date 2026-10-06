#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3ClosureSymmetric.lean <<'LEAN'
import HodgeProofHP.Stage3CoreFormalAdjointClosure

/-!
The closure of the harmonic Schwartz core is symmetric.
The reverse inclusion, needed for self-adjointness, is not asserted.
-/

namespace HodgeProofHP

theorem hpHarmonicClosure_le_adjoint :
    HPHarmonicClosure ≤ HPHarmonicClosure.adjoint := by
  apply LinearPMap.le_of_le_graph
  change HPHarmonicCoreOperator.closure.graph ≤
    HPHarmonicClosure.adjoint.graph
  rw [← hpHarmonicCoreOperator_isClosable.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal
    HPHarmonicCoreOperator.graph
    (LinearPMap.le_graph_of_le hpHarmonicCore_le_closure_adjoint)
    (LinearPMap.adjoint_isClosed hpHarmonicClosure_domain_dense)

#print axioms hpHarmonicClosure_le_adjoint

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3ClosureSymmetric.lean
lake build HodgeProofHP.Stage3ClosureSymmetric
