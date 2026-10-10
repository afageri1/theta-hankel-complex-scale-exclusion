#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3ClosureLeAdjoint.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianClosureEigenvector
import HodgeProofHP.Stage3AdjointInclusion

/-!
The harmonic core closure is contained in the adjoint of the core
operator. Equality with the adjoint is not asserted.
-/

namespace HodgeProofHP

theorem hpHarmonicClosure_le_core_adjoint :
    HPHarmonicClosure ≤ HPHarmonicCoreOperator.adjoint := by
  apply LinearPMap.le_of_le_graph
  change HPHarmonicCoreOperator.closure.graph ≤
    HPHarmonicCoreOperator.adjoint.graph
  rw [← LinearPMap.IsClosable.graph_closure_eq_closure_graph
    hpHarmonicCoreOperator_isClosable]
  exact Submodule.topologicalClosure_minimal
    HPHarmonicCoreOperator.graph
    (LinearPMap.le_graph_of_le
      hpHarmonicCoreOperator_le_adjoint)
    (LinearPMap.adjoint_isClosed
      hpHarmonicCoreOperator_domain_dense)

#print axioms hpHarmonicClosure_le_core_adjoint

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3ClosureLeAdjoint.lean
lake build HodgeProofHP.Stage3ClosureLeAdjoint
