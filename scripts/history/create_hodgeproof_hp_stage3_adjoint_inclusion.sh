#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3AdjointInclusion.lean <<'LEAN'
import HodgeProofHP.Stage3FormalSymmetry
import HodgeProofHP.Stage3HarmonicCoreSpec

/-!
The densely defined, formally symmetric harmonic core operator is contained
in its adjoint.
-/

namespace HodgeProofHP

theorem hpHarmonicCoreOperator_le_adjoint :
    HPHarmonicCoreOperator ≤ HPHarmonicCoreOperator.adjoint := by
  exact hpHarmonicCoreOperator_isFormalAdjoint.le_adjoint
    hpHarmonicCoreOperator_domain_dense

#print axioms hpHarmonicCoreOperator_le_adjoint

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3AdjointInclusion
