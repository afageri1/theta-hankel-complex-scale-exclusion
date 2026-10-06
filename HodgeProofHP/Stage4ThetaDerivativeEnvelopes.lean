import HodgeProofHP.Stage4ThetaDifferentialKernelSeries

/-!
Pointwise theta-kernel envelopes for the first and second derivatives.
Limits at infinity are not asserted in this module.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaGaussianParameter_series_hasSum
    (x : ℝ) (hx : 0 < x) :
    HasSum
      (fun n : ℕ =>
        2 * Real.exp (-hpThetaGaussianParameter n * x))
      (hpRiemannThetaKernel x) := by
  simpa only [hpThetaGaussianParameter, neg_mul, mul_assoc] using
    hpRiemannThetaKernel_hasSum x hx

theorem hpRiemannThetaLogProfile_deriv_norm_le_theta (u : ℝ) :
    ‖deriv hpRiemannThetaLogProfile u‖ ≤
      hpThetaGaussianFirstComparisonConstant u u *
        hpRiemannThetaKernel (Real.exp (2 * u) / 2) := by
  have hx : 0 < Real.exp (2 * u) / 2 := by
    positivity
  have hfirst :
      HasSum
        (fun n : ℕ => hpThetaGaussianFirstTerm n u)
        (deriv hpRiemannThetaLogProfile u) := by
    rw [hpRiemannThetaLogProfile_deriv_eq_tsum]
    exact (hpThetaGaussianFirstTerm_summable u).hasSum
  have hbound :
      HasSum
        (fun n : ℕ =>
          hpThetaGaussianFirstComparisonConstant u u *
            (2 * Real.exp
              (-hpThetaGaussianParameter n *
                (Real.exp (2 * u) / 2))))
        (hpThetaGaussianFirstComparisonConstant u u *
          hpRiemannThetaKernel (Real.exp (2 * u) / 2)) :=
    HasSum.mul_left
      (hpThetaGaussianFirstComparisonConstant u u)
      (hpThetaGaussianParameter_series_hasSum
        (Real.exp (2 * u) / 2) hx)
  apply HasSum.norm_le_of_bounded hfirst hbound
  intro n
  exact
    (hpThetaGaussianFirstTerm_norm_le_majorant
      u u u n le_rfl le_rfl).trans
    (hpThetaGaussianFirstMajorant_le_gaussian u u n)

theorem hpRiemannThetaLogProfile_secondDeriv_norm_le_theta (u : ℝ) :
    ‖deriv (deriv hpRiemannThetaLogProfile) u‖ ≤
      hpThetaGaussianSecondComparisonConstant u u *
        hpRiemannThetaKernel (Real.exp (2 * u) / 4) := by
  have hx : 0 < Real.exp (2 * u) / 4 := by
    positivity
  have hsecond :
      HasSum
        (fun n : ℕ => hpThetaGaussianSecondTerm n u)
        (deriv (deriv hpRiemannThetaLogProfile) u) := by
    rw [hpRiemannThetaLogProfile_secondDeriv_eq_tsum]
    exact (hpThetaGaussianSecondTerm_summable u).hasSum
  have hbound :
      HasSum
        (fun n : ℕ =>
          hpThetaGaussianSecondComparisonConstant u u *
            (2 * Real.exp
              (-hpThetaGaussianParameter n *
                (Real.exp (2 * u) / 4))))
        (hpThetaGaussianSecondComparisonConstant u u *
          hpRiemannThetaKernel (Real.exp (2 * u) / 4)) :=
    HasSum.mul_left
      (hpThetaGaussianSecondComparisonConstant u u)
      (hpThetaGaussianParameter_series_hasSum
        (Real.exp (2 * u) / 4) hx)
  apply HasSum.norm_le_of_bounded hsecond hbound
  intro n
  exact
    (hpThetaGaussianSecondTerm_norm_le_majorant
      u u u n le_rfl le_rfl).trans
    (hpThetaGaussianSecondMajorant_le_gaussian u u n)

#print axioms hpThetaGaussianParameter_series_hasSum
#print axioms hpRiemannThetaLogProfile_deriv_norm_le_theta
#print axioms hpRiemannThetaLogProfile_secondDeriv_norm_le_theta

end HodgeProofHP
