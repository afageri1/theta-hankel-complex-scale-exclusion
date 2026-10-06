#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3DeficiencyRangeOrthogonality.lean <<'LEAN'
import HodgeProofHP.Stage3DeficiencyDomainBoundary

/-!
An eigenvector of the core adjoint is orthogonal to the range of
the corresponding conjugate-shifted core operator.
-/

namespace HodgeProofHP

theorem hpHarmonicAdjoint_eigen_orthogonal_shifted_range
    (c : ℂ)
    (f : HPHarmonicCoreOperator.adjoint.domain)
    (hf : HPHarmonicCoreOperator.adjoint.toFun f =
      c • (f : HPSpace))
    (g : HPHarmonicCoreOperator.domain) :
    inner ℂ (f : HPSpace)
      (HPHarmonicCoreOperator.toFun g -
        (starRingEnd ℂ) c • (g : HPSpace)) = 0 := by
  have hform :=
    (LinearPMap.adjoint_isFormalAdjoint
      hpHarmonicCoreOperator_domain_dense) f g
  change inner ℂ (HPHarmonicCoreOperator.adjoint.toFun f)
      (g : HPSpace) =
    inner ℂ (f : HPSpace)
      (HPHarmonicCoreOperator.toFun g) at hform
  rw [hf] at hform
  have hscalar :
      inner ℂ (f : HPSpace) (HPHarmonicCoreOperator.toFun g) =
        (starRingEnd ℂ) c *
          inner ℂ (f : HPSpace) (g : HPSpace) := by
    simpa only [inner_smul_left] using hform.symm
  calc
    inner ℂ (f : HPSpace)
        (HPHarmonicCoreOperator.toFun g -
          (starRingEnd ℂ) c • (g : HPSpace)) =
      inner ℂ (f : HPSpace) (HPHarmonicCoreOperator.toFun g) -
        (starRingEnd ℂ) c *
          inner ℂ (f : HPSpace) (g : HPSpace) := by
            rw [inner_sub_right, inner_smul_right]
    _ = 0 := sub_eq_zero.mpr hscalar

#print axioms hpHarmonicAdjoint_eigen_orthogonal_shifted_range

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3DeficiencyRangeOrthogonality.lean
lake build HodgeProofHP.Stage3DeficiencyRangeOrthogonality
