/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVKernelSecondZeroLower

/-!
# A sharper rational lower certificate for the CNV kernel value at zero

The first Gaussian term supplies a strict lower bound for Phi(0) and its
square. This certifies the positive square term in the endpoint derivative.
No bound for I(0) * Phi''(0), or positivity of the full derivative, is claimed.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_exp_small_upper_sharp :
    Real.exp (3927 / 20000 : ℝ) ≤ (3803 / 3125 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (3927 / 20000) (3803 / 3125) 6
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaCNV_exp_neg_pi_lower_sharp :
    (27 / 625 : ℝ) ≤ Real.exp (-Real.pi) := by
  have h := hpThetaTrace_exp_neg_nat_mul_lower
    (3927 / 20000) (3803 / 3125) (27 / 625) 16
    (by norm_num) (by norm_num) hpThetaCNV_exp_small_upper_sharp (by norm_num)
  have h31416 : (27 / 625 : ℝ) ≤ Real.exp (-(3927 / 1250 : ℝ)) := by
    convert h using 1 <;> norm_num
  have hpi : Real.pi ≤ (3927 / 1250 : ℝ) := by
    have hbound := Real.pi_lt_d4
    linarith
  exact h31416.trans (Real.exp_le_exp.mpr (by linarith))

theorem hpThetaPhi_zero_gt_eightyNine_fiftieths :
    (89 / 50 : ℝ) < hpRiemannThetaDifferentialKernel 0 := by
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have hbound := Real.pi_gt_d4
    linarith
  have hpoly := hpThetaTrace_scalar_polynomial_mono
    (31415 / 10000) Real.pi (by norm_num) hpi
  have hpoly0 : 0 ≤ 4 * Real.pi ^ 2 - 6 * Real.pi :=
    le_trans (by norm_num : (0 : ℝ) ≤ 4 * (31415 / 10000 : ℝ) ^ 2 - 6 * (31415 / 10000)) hpoly
  have hexp := mul_le_mul_of_nonneg_left hpThetaCNV_exp_neg_pi_lower_sharp
    (by norm_num : (0 : ℝ) ≤ 2)
  have hfirst : (4 * Real.pi ^ 2 - 6 * Real.pi) * (2 * Real.exp (-Real.pi)) ≤
      hpRiemannThetaDifferentialKernel 0 := by
    simpa [hpThetaTraceEndpointLower] using
      hpThetaJensenKernel_endpointLower_le 0 0 0 le_rfl le_rfl le_rfl
  calc
    (89 / 50 : ℝ) <
        (4 * (31415 / 10000 : ℝ) ^ 2 - 6 * (31415 / 10000)) * (2 * (27 / 625)) := by
      norm_num
    _ ≤ (4 * Real.pi ^ 2 - 6 * Real.pi) * (2 * Real.exp (-Real.pi)) :=
      mul_le_mul hpoly hexp (by norm_num) hpoly0
    _ ≤ hpRiemannThetaDifferentialKernel 0 := hfirst

theorem hpThetaPhi_zero_sq_gt_certified_sharp :
    (7921 / 2500 : ℝ) < hpRiemannThetaDifferentialKernel 0 ^ 2 := by
  have h := hpThetaPhi_zero_gt_eightyNine_fiftieths
  nlinarith

#print axioms hpThetaCNV_exp_small_upper_sharp
#print axioms hpThetaCNV_exp_neg_pi_lower_sharp
#print axioms hpThetaPhi_zero_gt_eightyNine_fiftieths
#print axioms hpThetaPhi_zero_sq_gt_certified_sharp
end HodgeProofHP
