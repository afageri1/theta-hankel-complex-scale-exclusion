#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaDerivativeEnvelopesSimplified.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaDerivativeEnvelopes

/-!
Explicit numerical constants in the theta derivative envelopes.
The existing theta decay theorem is displayed for the subsequent limit proofs.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaGaussianFirstComparisonConstant_diag (u : ℝ) :
    hpThetaGaussianFirstComparisonConstant u u =
      (9 / 2 : ℝ) * Real.exp (u / 2) := by
  have he : Real.exp (2 * u) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  have hratio :
      4 * Real.exp (2 * u) / Real.exp (2 * u) = (4 : ℝ) := by
    field_simp [he]
  unfold hpThetaGaussianFirstComparisonConstant
  rw [hratio]
  ring

theorem hpThetaGaussianSecondComparisonConstant_diag (u : ℝ) :
    hpThetaGaussianSecondComparisonConstant u u =
      (459 / 4 : ℝ) * Real.exp (u / 2) := by
  have he : Real.exp (2 * u) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  have hratio₁ :
      4 * Real.exp (2 * u) / Real.exp (2 * u) = (4 : ℝ) := by
    field_simp [he]
  have hratio₂ :
      4 * Real.exp (2 * u) / (Real.exp (2 * u) / 2) = (8 : ℝ) := by
    field_simp [he] <;> ring
  unfold hpThetaGaussianSecondComparisonConstant
  rw [hratio₁, hratio₂]
  ring

theorem hpRiemannThetaLogProfile_deriv_norm_le_explicit (u : ℝ) :
    ‖deriv hpRiemannThetaLogProfile u‖ ≤
      ((9 / 2 : ℝ) * Real.exp (u / 2)) *
        hpRiemannThetaKernel (Real.exp (2 * u) / 2) := by
  simpa only [hpThetaGaussianFirstComparisonConstant_diag] using
    hpRiemannThetaLogProfile_deriv_norm_le_theta u

theorem hpRiemannThetaLogProfile_secondDeriv_norm_le_explicit (u : ℝ) :
    ‖deriv (deriv hpRiemannThetaLogProfile) u‖ ≤
      ((459 / 4 : ℝ) * Real.exp (u / 2)) *
        hpRiemannThetaKernel (Real.exp (2 * u) / 4) := by
  simpa only [hpThetaGaussianSecondComparisonConstant_diag] using
    hpRiemannThetaLogProfile_secondDeriv_norm_le_theta u

#print axioms hpThetaGaussianFirstComparisonConstant_diag
#print axioms hpThetaGaussianSecondComparisonConstant_diag
#print axioms hpRiemannThetaLogProfile_deriv_norm_le_explicit
#print axioms hpRiemannThetaLogProfile_secondDeriv_norm_le_explicit

#check hpRiemannThetaKernel_exponential_decay
#print hpRiemannThetaKernel_exponential_decay

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaDerivativeEnvelopes
lake env lean HodgeProofHP/Stage4ThetaDerivativeEnvelopesSimplified.lean
lake build HodgeProofHP.Stage4ThetaDerivativeEnvelopesSimplified
