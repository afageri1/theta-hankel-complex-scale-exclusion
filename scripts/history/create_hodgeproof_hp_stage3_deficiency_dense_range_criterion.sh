#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3DeficiencyDenseRangeCriterion.lean <<'LEAN'
import HodgeProofHP.Stage3DeficiencyRangeOrthogonality
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
Dense range of a conjugate-shifted harmonic core operator rules out
the corresponding eigenvectors of the adjoint. Density is an explicit
hypothesis; it is not proved in this file.
-/

namespace HodgeProofHP

theorem hpHarmonicAdjoint_eigen_eq_zero_of_dense_shifted_range
    (c : ℂ)
    (hDense : DenseRange
      (fun g : HPHarmonicCoreOperator.domain =>
        HPHarmonicCoreOperator.toFun g -
          (starRingEnd ℂ) c • (g : HPSpace)))
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      c • (f : HPSpace)) :
    (f : HPSpace) = 0 := by
  exact DenseRange.eq_zero_of_inner_left ℂ hDense
    (fun g =>
      hpHarmonicAdjoint_eigen_orthogonal_shifted_range c f hf g)

#print axioms hpHarmonicAdjoint_eigen_eq_zero_of_dense_shifted_range

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3DeficiencyDenseRangeCriterion.lean
lake build HodgeProofHP.Stage3DeficiencyDenseRangeCriterion
