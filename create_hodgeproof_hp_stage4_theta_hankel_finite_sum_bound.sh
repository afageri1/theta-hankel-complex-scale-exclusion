#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelRemainderApiAudit

target="HodgeProofHP/Stage4ThetaHankelFiniteSumBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelRemainderApiAudit
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Finite vector Cauchy-Schwarz bounds for the Hankel basis expansion.
These bounds prepare the estimate for the infinite remainder.
-/

namespace HodgeProofHP

theorem hpThetaHankel_finite_vector_sum_norm_sq_le
    {ι : Type*} (F : Finset ι)
    (c : ι → ℂ) (v : ι → HPThetaHankelSpace) :
    ‖∑ i ∈ F, c i • v i‖ ^ 2 ≤
      (∑ i ∈ F, ‖c i‖ ^ 2) *
        (∑ i ∈ F, ‖v i‖ ^ 2) := by
  classical
  have hnorm :
      ‖∑ i ∈ F, c i • v i‖ ≤
        ∑ i ∈ F, ‖c i‖ * ‖v i‖ := by
    simpa only [norm_smul] using
      norm_sum_le F (fun i => c i • v i)
  have hsum :
      0 ≤ ∑ i ∈ F, ‖c i‖ * ‖v i‖ :=
    Finset.sum_nonneg
      (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq :
      ‖∑ i ∈ F, c i • v i‖ ^ 2 ≤
        (∑ i ∈ F, ‖c i‖ * ‖v i‖) ^ 2 := by
    have hproduct :=
      mul_nonneg (sub_nonneg.mpr hnorm)
        (add_nonneg hsum (norm_nonneg (∑ i ∈ F, c i • v i)))
    nlinarith
  exact hsq.trans
    (Finset.sum_mul_sq_le_sq_mul_sq F
      (fun i => ‖c i‖) (fun i => ‖v i‖))

theorem hpThetaHankel_finite_basis_sum_norm_sq_le
    (F : Finset hpThetaHankelBasisSet)
    (x : HPThetaHankelSpace) :
    ‖∑ i ∈ F,
      inner ℂ (hpThetaHankelHilbertBasis i) x •
        hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2 ≤
      hpThetaHankelFiniteBasisEnergy F * ‖x‖ ^ 2 := by
  classical
  have hbessel :
      (∑ i ∈ F,
        ‖inner ℂ (hpThetaHankelHilbertBasis i) x‖ ^ 2) ≤
        ‖x‖ ^ 2 :=
    hpThetaHankelHilbertBasis_orthonormal.sum_inner_products_le
      (s := F) (x := x)
  have henergy :
      0 ≤ ∑ i ∈ F,
        ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc
    ‖∑ i ∈ F,
      inner ℂ (hpThetaHankelHilbertBasis i) x •
        hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2
        ≤
          (∑ i ∈ F,
            ‖inner ℂ (hpThetaHankelHilbertBasis i) x‖ ^ 2) *
          (∑ i ∈ F,
            ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2) :=
      hpThetaHankel_finite_vector_sum_norm_sq_le F
        (fun i => inner ℂ (hpThetaHankelHilbertBasis i) x)
        (fun i => hpThetaHankelOperator (hpThetaHankelHilbertBasis i))
    _ ≤ ‖x‖ ^ 2 *
        (∑ i ∈ F,
          ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hbessel henergy
    _ = hpThetaHankelFiniteBasisEnergy F * ‖x‖ ^ 2 := by
      unfold hpThetaHankelFiniteBasisEnergy
      ring

theorem hpThetaHankelFiniteApproximation_norm_sq_le
    (F : Finset hpThetaHankelBasisSet)
    (x : HPThetaHankelSpace) :
    ‖hpThetaHankelFiniteApproximation F x‖ ^ 2 ≤
      hpThetaHankelFiniteBasisEnergy F * ‖x‖ ^ 2 := by
  rw [hpThetaHankelFiniteApproximation_apply]
  exact hpThetaHankel_finite_basis_sum_norm_sq_le F x

#print axioms hpThetaHankel_finite_vector_sum_norm_sq_le
#print axioms hpThetaHankel_finite_basis_sum_norm_sq_le
#print axioms hpThetaHankelFiniteApproximation_norm_sq_le

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFiniteSumBound

printf '%s\n' 'PASS: Stage4ThetaHankelFiniteSumBound'
