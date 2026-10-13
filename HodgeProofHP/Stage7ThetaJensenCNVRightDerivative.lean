/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVZeroBoundary

/-!
# CNV derivative at the endpoint of the nonnegative half-line

The interval-integral model agrees with the actual weighted tail on Ici 0.
It supplies derivatives within that half-line, including its endpoint.
The endpoint CNV derivative is identified but its positivity is not proved.
-/
noncomputable section
open Set MeasureTheory
namespace HodgeProofHP

theorem hpThetaPhiWeightedTail_hasDerivWithinAt_nonnegative
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt hpThetaPhiWeightedTail
      (-(t * hpRiemannThetaDifferentialKernel t)) (Set.Ici 0) t := by
  have h := (hpThetaPhi_weightedIntegrand_continuous.integral_hasStrictDerivAt
    0 t).hasDerivAt
  have hmodel := h.const_sub (hpThetaPhiWeightedTail 0)
  exact hmodel.hasDerivWithinAt.congr
    (fun u hu => hpThetaPhiWeightedTail_eq_total_sub_integral u hu)
    (hpThetaPhiWeightedTail_eq_total_sub_integral t ht)

theorem hpThetaPhiWeightedTail_hasDerivWithinAt_zero :
    HasDerivWithinAt hpThetaPhiWeightedTail 0 (Set.Ici 0) 0 := by
  simpa only [zero_mul, neg_zero] using
    hpThetaPhiWeightedTail_hasDerivWithinAt_nonnegative 0 le_rfl

theorem hpThetaPhiCNVTailExpression_hasDerivWithinAt_nonnegative
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt hpThetaPhiCNVTailExpression
      (hpThetaPhiCNVTailFirstDerivative t) (Set.Ici 0) t := by
  have hI := hpThetaPhiWeightedTail_hasDerivWithinAt_nonnegative t ht
  have hphi := hpThetaPhi_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_deriv_eq_kernelSeries t] at hphi
  have hphi1 := hpThetaPhi_deriv_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_secondDeriv_eq_kernelSeries t] at hphi1
  have h := (hI.mul hphi1.hasDerivWithinAt).add
    ((hasDerivAt_id t).hasDerivWithinAt.mul (hphi.hasDerivWithinAt.pow 2))
  change HasDerivWithinAt hpThetaPhiCNVTailExpression _ (Set.Ici 0) t at h
  convert h using 1 <;> norm_num [hpThetaPhiCNVTailFirstDerivative] <;> ring

theorem hpThetaPhiCNVTailFirstDerivative_zero :
    hpThetaPhiCNVTailFirstDerivative 0 =
      hpThetaPhiWeightedTail 0 * deriv (deriv hpRiemannThetaDifferentialKernel) 0 +
        hpRiemannThetaDifferentialKernel 0 ^ 2 := by
  simp [hpThetaPhiCNVTailFirstDerivative]

theorem hpThetaPhiCNVTailExpression_hasDerivWithinAt_zero :
    HasDerivWithinAt hpThetaPhiCNVTailExpression
      (hpThetaPhiWeightedTail 0 * deriv (deriv hpRiemannThetaDifferentialKernel) 0 +
        hpRiemannThetaDifferentialKernel 0 ^ 2) (Set.Ici 0) 0 := by
  simpa only [hpThetaPhiCNVTailFirstDerivative_zero] using
    hpThetaPhiCNVTailExpression_hasDerivWithinAt_nonnegative 0 le_rfl

#print axioms hpThetaPhiWeightedTail_hasDerivWithinAt_nonnegative
#print axioms hpThetaPhiWeightedTail_hasDerivWithinAt_zero
#print axioms hpThetaPhiCNVTailExpression_hasDerivWithinAt_nonnegative
#print axioms hpThetaPhiCNVTailFirstDerivative_zero
#print axioms hpThetaPhiCNVTailExpression_hasDerivWithinAt_zero
end HodgeProofHP
