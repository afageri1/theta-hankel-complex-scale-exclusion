/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVKernelSecondOnOneFiftieth
import HodgeProofHP.Stage7ThetaJensenCNVKernelZeroSharpLower
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform lower bounds for the actual kernel and its first derivative

The certified second derivative bound and the zero first derivative at the
origin give Phi'(t) >= -35*t >= -0.7 on [0, 1/50]. A second mean value inequality
then gives Phi(t) > 1.766. This does not establish an upper bound for Phi or
positivity of the CNV expression on the whole interval.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaPhi_deriv_ge_neg35_mul_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    -35 * t ≤ deriv hpRiemannThetaDifferentialKernel t := by
  have hd : Differentiable ℝ (deriv hpRiemannThetaDifferentialKernel) :=
    fun u => (hpThetaPhi_deriv_hasDerivAt_kernelSeries u).differentiableAt
  have hbound : ∀ u ∈ interior (Set.Icc (0 : ℝ) (1 / 50)),
      (-35 : ℝ) ≤ deriv (deriv hpRiemannThetaDifferentialKernel) u := by
    intro u hu
    exact hpThetaPhi_secondDeriv_ge_neg35_on_oneFiftieth u (Set.interior_subset hu)
  have h := (convex_Icc (0 : ℝ) (1 / 50)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn hbound
    0 (by constructor <;> norm_num) t ht ht.1
  simpa only [sub_zero, hpThetaPhi_deriv_zero] using h

theorem hpThetaPhi_deriv_ge_neg_seven_tenths_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (-7 / 10 : ℝ) ≤ deriv hpRiemannThetaDifferentialKernel t := by
  have h := hpThetaPhi_deriv_ge_neg35_mul_on_oneFiftieth t ht
  have hupper := ht.2
  linarith

theorem hpThetaPhi_ge_zero_sub_seven_tenths_mul_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    hpRiemannThetaDifferentialKernel 0 - (7 / 10 : ℝ) * t ≤
      hpRiemannThetaDifferentialKernel t := by
  have hd : Differentiable ℝ hpRiemannThetaDifferentialKernel :=
    fun u => (hpThetaPhi_hasDerivAt_kernelSeries u).differentiableAt
  have hbound : ∀ u ∈ interior (Set.Icc (0 : ℝ) (1 / 50)),
      (-7 / 10 : ℝ) ≤ deriv hpRiemannThetaDifferentialKernel u := by
    intro u hu
    exact hpThetaPhi_deriv_ge_neg_seven_tenths_on_oneFiftieth u (Set.interior_subset hu)
  have h := (convex_Icc (0 : ℝ) (1 / 50)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn hbound
    0 (by constructor <;> norm_num) t ht ht.1
  simp only [sub_zero] at h
  linarith

theorem hpThetaPhi_gt_eightHundredEightyThree_fiveHundredths_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (883 / 500 : ℝ) < hpRiemannThetaDifferentialKernel t := by
  have h := hpThetaPhi_ge_zero_sub_seven_tenths_mul_on_oneFiftieth t ht
  have hzero := hpThetaPhi_zero_gt_eightyNine_fiftieths
  have hupper := ht.2
  linarith

theorem hpThetaPhi_sq_gt_certified_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (779689 / 250000 : ℝ) < hpRiemannThetaDifferentialKernel t ^ 2 := by
  have h := hpThetaPhi_gt_eightHundredEightyThree_fiveHundredths_on_oneFiftieth t ht
  nlinarith [sq_nonneg (hpRiemannThetaDifferentialKernel t - (883 / 500 : ℝ))]

#print axioms hpThetaPhi_deriv_ge_neg35_mul_on_oneFiftieth
#print axioms hpThetaPhi_deriv_ge_neg_seven_tenths_on_oneFiftieth
#print axioms hpThetaPhi_ge_zero_sub_seven_tenths_mul_on_oneFiftieth
#print axioms hpThetaPhi_gt_eightHundredEightyThree_fiveHundredths_on_oneFiftieth
#print axioms hpThetaPhi_sq_gt_certified_on_oneFiftieth
end HodgeProofHP
