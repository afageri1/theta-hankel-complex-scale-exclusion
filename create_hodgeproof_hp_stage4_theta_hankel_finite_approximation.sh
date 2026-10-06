#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelCompactApiAudit

target="HodgeProofHP/Stage4ThetaHankelFiniteApproximation.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelCompactApiAudit
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Finite sums of rank-one operators associated with the chosen Hilbert basis.
No operator-norm convergence or compactness theorem is asserted here.
-/

namespace HodgeProofHP

noncomputable def hpThetaHankelBasisRankOne
    (i : hpThetaHankelBasisSet) :
    HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace :=
  InnerProductSpace.rankOne ℂ
    (hpThetaHankelOperator (hpThetaHankelHilbertBasis i))
    (hpThetaHankelHilbertBasis i)

noncomputable def hpThetaHankelFiniteApproximation
    (F : Finset hpThetaHankelBasisSet) :
    HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace :=
  ∑ i ∈ F, hpThetaHankelBasisRankOne i

noncomputable def hpThetaHankelFiniteProjection
    (F : Finset hpThetaHankelBasisSet) :
    HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace :=
  ∑ i ∈ F, InnerProductSpace.rankOne ℂ
    (hpThetaHankelHilbertBasis i)
    (hpThetaHankelHilbertBasis i)

theorem hpThetaHankelBasisRankOne_apply
    (i : hpThetaHankelBasisSet) (x : HPThetaHankelSpace) :
    hpThetaHankelBasisRankOne i x =
      inner ℂ (hpThetaHankelHilbertBasis i) x •
        hpThetaHankelOperator (hpThetaHankelHilbertBasis i) := by
  rfl

theorem hpThetaHankelBasisRankOne_norm
    (i : hpThetaHankelBasisSet) :
    ‖hpThetaHankelBasisRankOne i‖ =
      ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ := by
  unfold hpThetaHankelBasisRankOne
  rw [InnerProductSpace.norm_rankOne,
    hpThetaHankelHilbertBasis_orthonormal.norm_eq_one i,
    mul_one]

theorem hpThetaHankelFiniteApproximation_apply
    (F : Finset hpThetaHankelBasisSet) (x : HPThetaHankelSpace) :
    hpThetaHankelFiniteApproximation F x =
      ∑ i ∈ F, inner ℂ (hpThetaHankelHilbertBasis i) x •
        hpThetaHankelOperator (hpThetaHankelHilbertBasis i) := by
  classical
  simp [hpThetaHankelFiniteApproximation,
    hpThetaHankelBasisRankOne_apply]

theorem hpThetaHankelFiniteProjection_apply
    (F : Finset hpThetaHankelBasisSet) (x : HPThetaHankelSpace) :
    hpThetaHankelFiniteProjection F x =
      ∑ i ∈ F, inner ℂ (hpThetaHankelHilbertBasis i) x •
        hpThetaHankelHilbertBasis i := by
  classical
  simp [hpThetaHankelFiniteProjection,
    InnerProductSpace.rankOne_apply]

theorem hpThetaHankelFiniteApproximation_eq_comp
    (F : Finset hpThetaHankelBasisSet) :
    hpThetaHankelFiniteApproximation F =
      hpThetaHankelOperator.comp (hpThetaHankelFiniteProjection F) := by
  classical
  ext x
  simp [ContinuousLinearMap.comp_apply,
    hpThetaHankelFiniteApproximation_apply,
    hpThetaHankelFiniteProjection_apply,
    map_sum, map_smul]

theorem hpThetaHankelFiniteApproximation_empty :
    hpThetaHankelFiniteApproximation ∅ = 0 := by
  simp [hpThetaHankelFiniteApproximation]

#print axioms hpThetaHankelBasisRankOne
#print axioms hpThetaHankelBasisRankOne_norm
#print axioms hpThetaHankelFiniteApproximation_apply
#print axioms hpThetaHankelFiniteProjection_apply
#print axioms hpThetaHankelFiniteApproximation_eq_comp

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFiniteApproximation

printf '%s\n' 'PASS: Stage4ThetaHankelFiniteApproximation'
