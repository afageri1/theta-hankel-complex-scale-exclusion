/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVKernelUpperOnOneFiftieth
import HodgeProofHP.Stage7ThetaJensenCNVWeightedTailSharpUpper
import HodgeProofHP.Stage7ThetaJensenCNVRightDerivative

/-!
# Quantitative CNV positivity on (0, 1/50]

Assemble the bounds for the actual kernel, its derivatives and weighted tail.
The derivative coefficient is greater than 11439/250000 = 0.045756 throughout
[0, 1/50]. The mean value inequality then supplies a linear lower bound for
G and strict positivity on (0, 1/50], including the right endpoint.
This module makes no claim of CNV positivity beyond 1/50 or of RH.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_tail_mul_secondDeriv_ge_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (-609 / 200 : ℝ) ≤
      hpThetaPhiWeightedTail t * deriv (deriv hpRiemannThetaDifferentialKernel) t := by
  have hI := hpThetaPhiWeightedTail_bounds_eightySeven_thousandths t ht.1
  have hD := hpThetaPhi_secondDeriv_ge_neg35_on_oneFiftieth t ht
  have hprod := mul_nonneg hI.1 (sub_nonneg.mpr hD)
  nlinarith [hI.2]

theorem hpThetaCNV_mixed_term_ge_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (-7 / 250 : ℝ) ≤ t * hpRiemannThetaDifferentialKernel t *
      deriv hpRiemannThetaDifferentialKernel t := by
  have hphi0 := (hpThetaPhi_pos_on_nonnegative t ht.1).le
  have hphiU := hpThetaPhi_le_two_on_oneFiftieth t ht
  have hD := hpThetaPhi_deriv_ge_neg_seven_tenths_on_oneFiftieth t ht
  have htp : t * hpRiemannThetaDifferentialKernel t ≤ (1 / 25 : ℝ) := by
    have h := mul_le_mul ht.2 hphiU hphi0 (by norm_num : (0 : ℝ) ≤ 1 / 50)
    nlinarith
  calc
    (-7 / 250 : ℝ) ≤ (t * hpRiemannThetaDifferentialKernel t) * (-7 / 10) := by
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (mul_nonneg ht.1 hphi0)

theorem hpThetaPhiCNVTailFirstDerivative_gt_certified_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (11439 / 250000 : ℝ) < hpThetaPhiCNVTailFirstDerivative t := by
  have htail := hpThetaCNV_tail_mul_secondDeriv_ge_on_oneFiftieth t ht
  have hmixed := hpThetaCNV_mixed_term_ge_on_oneFiftieth t ht
  have hsquare := hpThetaPhi_sq_gt_certified_on_oneFiftieth t ht
  unfold hpThetaPhiCNVTailFirstDerivative
  linarith

theorem hpThetaPhiCNVTailExpression_deriv_gt_certified_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 50)) :
    (11439 / 250000 : ℝ) < deriv hpThetaPhiCNVTailExpression t := by
  rw [hpThetaPhiCNVTailExpression_deriv t ht.1]
  exact hpThetaPhiCNVTailFirstDerivative_gt_certified_on_oneFiftieth t ⟨ht.1.le, ht.2⟩

theorem hpThetaPhiCNVTailExpression_linear_lower_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (11439 / 250000 : ℝ) * t ≤ hpThetaPhiCNVTailExpression t := by
  have hc : ContinuousOn hpThetaPhiCNVTailExpression (Set.Icc (0 : ℝ) (1 / 50)) := by
    intro u hu
    exact (hpThetaPhiCNVTailExpression_hasDerivWithinAt_nonnegative u hu.1)
      .continuousWithinAt.mono (fun v hv => hv.1)
  have hd : DifferentiableOn ℝ hpThetaPhiCNVTailExpression
      (interior (Set.Icc (0 : ℝ) (1 / 50))) := by
    intro u hu
    have hu' : u ∈ Set.Ioo (0 : ℝ) (1 / 50) := by
      simpa only [interior_Icc] using hu
    exact (hpThetaPhiCNVTailExpression_hasDerivAt u hu'.1)
      .differentiableAt.differentiableWithinAt
  have hbound : ∀ u ∈ interior (Set.Icc (0 : ℝ) (1 / 50)),
      (11439 / 250000 : ℝ) ≤ deriv hpThetaPhiCNVTailExpression u := by
    intro u hu
    have hu' : u ∈ Set.Ioo (0 : ℝ) (1 / 50) := by
      simpa only [interior_Icc] using hu
    exact (hpThetaPhiCNVTailExpression_deriv_gt_certified_on_oneFiftieth
      u ⟨hu'.1, hu'.2.le⟩).le
  have h := (convex_Icc (0 : ℝ) (1 / 50)).mul_sub_le_image_sub_of_le_deriv
    hc hd hbound 0 (by constructor <;> norm_num) t ht ht.1
  simpa only [sub_zero, hpThetaPhiCNVTailExpression_zero] using h

theorem hpThetaPhiCNVTailExpression_pos_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 50)) :
    0 < hpThetaPhiCNVTailExpression t := by
  have h := hpThetaPhiCNVTailExpression_linear_lower_on_oneFiftieth t ⟨ht.1.le, ht.2⟩
  have hp : 0 < (11439 / 250000 : ℝ) * t := mul_pos (by norm_num) ht.1
  exact hp.trans_le h

#print axioms hpThetaCNV_tail_mul_secondDeriv_ge_on_oneFiftieth
#print axioms hpThetaCNV_mixed_term_ge_on_oneFiftieth
#print axioms hpThetaPhiCNVTailFirstDerivative_gt_certified_on_oneFiftieth
#print axioms hpThetaPhiCNVTailExpression_deriv_gt_certified_on_oneFiftieth
#print axioms hpThetaPhiCNVTailExpression_linear_lower_on_oneFiftieth
#print axioms hpThetaPhiCNVTailExpression_pos_on_oneFiftieth
end HodgeProofHP
