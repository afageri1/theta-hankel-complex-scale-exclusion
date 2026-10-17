/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureIntervalCriterion
import HodgeProofHP.Stage7ThetaJensenCNVWeightedTailExponential

/-!
# A certified density curvature cell away from the endpoint

The actual density curvature is positive on [1/5, 200001/1000000]. Bounds
are scaled by the first positive Gaussian profile. A geometric estimate
controls the entire second derivative remainder, not a finite truncation.

This pilot cell is separated from the endpoint interval. No coverage of
[1/10000, 1/5], no outer density sign and no global conclusion are asserted.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaDensityPilot_exp_lower :
    (7459 / 5000 : ℝ) ≤ Real.exp (2 / 5 : ℝ) := by
  exact hpThetaTrace_exp_lower_of_taylor (2 / 5) (7459 / 5000) 12
    (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])

theorem hpThetaDensityPilot_exp_upper :
    Real.exp (200001 / 500000 : ℝ) ≤ (14919 / 10000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (200001 / 500000) (14919 / 10000) 12
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 2000000 in
-- The 32-term rational Taylor lower bound controls the infinite-series ratio.
theorem hpThetaDensityPilot_exp_fourteen_lower :
    (1024000 : ℝ) ≤ Real.exp (14 : ℝ) := by
  exact hpThetaTrace_exp_lower_of_taylor 14 1024000 32
    (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])

theorem hpThetaDensityPilot_parameter_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    Real.pi * Real.exp (2 * t) ∈ Set.Icc (2343 / 500 : ℝ) (4687 / 1000) := by
  have hpL : (31415 / 10000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d4]
  have hpU : Real.pi ≤ (3927 / 1250 : ℝ) := by linarith [Real.pi_lt_d4]
  have heL : (7459 / 5000 : ℝ) ≤ Real.exp (2 * t) :=
    hpThetaDensityPilot_exp_lower.trans (Real.exp_le_exp.mpr (by linarith [ht.1]))
  have heU : Real.exp (2 * t) ≤ (14919 / 10000 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith [ht.2])).trans hpThetaDensityPilot_exp_upper
  have hL := mul_le_mul hpL heL (by norm_num) Real.pi_pos.le
  have hU := mul_le_mul hpU heU (Real.exp_nonneg _) (by norm_num)
  constructor <;> nlinarith only [hL, hU]

private theorem hpDensityPilot_polynomial_bounds (b : ℝ)
    (hb : b ∈ Set.Icc (2343 / 500 : ℝ) (4687 / 1000)) :
    59 ≤ 4 * b ^ 2 - 6 * b ∧
    4 * b ^ 2 - 6 * b ≤ 60 ∧
    230 ≤ 8 * b ^ 3 - 30 * b ^ 2 + 15 * b ∧
    8 * b ^ 3 - 30 * b ^ 2 + 15 * b ≤ 236 ∧
    16 * b ^ 4 - 112 * b ^ 3 + 165 * b ^ 2 - (75 / 2 : ℝ) * b ≤ -352 ∧
    8 * b ^ 3 / 250 ≤ 4 ∧ 16 * b ^ 4 ≤ 7998 := by
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2343 / 500) hb.1 2
  have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2343 / 500) hb.1 3
  have h2U := pow_le_pow_left₀ hb0 hb.2 2
  have h3U := pow_le_pow_left₀ hb0 hb.2 3
  have h4U := pow_le_pow_left₀ hb0 hb.2 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith only [hb.1, hb.2, h2L, h3L, h2U, h3U, h4U]

private theorem hpDensityPilot_second_ratio_bounds (b : ℝ) (hb : (2343 / 500 : ℝ) ≤ b) :
    0 ≤ 256 * Real.exp (-3 * b) ∧
      256 * Real.exp (-3 * b) ≤ (1 / 4000 : ℝ) := by
  have hprod := mul_le_mul_of_nonneg_right hpThetaDensityPilot_exp_fourteen_lower
    (Real.exp_nonneg (-(14 : ℝ)))
  have hid : Real.exp (14 : ℝ) * Real.exp (-(14 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at hprod
  have he : Real.exp (-3 * b) ≤ Real.exp (-(14 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  constructor
  · positivity
  · nlinarith only [hprod, he]

private theorem hpDensityPilot_second_polynomial_le (q : ℝ) (hq : 2 ≤ q) :
    16 * q ^ 4 - 112 * q ^ 3 + 165 * q ^ 2 - (75 / 2 : ℝ) * q ≤
      16 * q ^ 4 := by
  have hq0 : 0 ≤ q := by linarith
  have h := mul_nonneg (sq_nonneg q) (show 0 ≤ 112 * q - 165 by linarith)
  nlinarith only [h, hq0]

theorem hpThetaDensityPilot_secondTerm_le_geometric (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t ≤
      (7998 * hpThetaGaussianProfile Real.pi t) * (1 / 4000 : ℝ) ^ n := by
  let b := Real.pi * Real.exp (2 * t)
  let m : ℝ := (n : ℝ) + 1
  let S := hpThetaGaussianProfile Real.pi t
  have hb := hpThetaDensityPilot_parameter_bounds t ht
  change b ∈ Set.Icc (2343 / 500 : ℝ) (4687 / 1000) at hb
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hm : 1 ≤ m := by dsimp [m]; positivity
  have hm0 : 0 ≤ m := by linarith
  have hq : 2 ≤ b * m ^ 2 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm 2
    have h := mul_le_mul_of_nonneg_left hs hb0
    nlinarith [hb.1]
  have hpoly := hpDensityPilot_second_polynomial_le (b * m ^ 2) hq
  have hgap : 3 * (n : ℝ) ≤ m ^ 2 - 1 := hpThetaKernelUpper_square_growth n
  have hscaled := mul_le_mul_of_nonneg_left hgap hb0
  have hexp : Real.exp (-b * (m ^ 2 - 1)) ≤ Real.exp (-3 * b * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hscaled]
  have hprofile : hpThetaGaussianProfile (hpThetaGaussianParameter n) t =
      S * Real.exp (-b * (m ^ 2 - 1)) := by
    unfold hpThetaGaussianProfile hpThetaGaussianParameter
    dsimp [S, hpThetaGaussianProfile, b, m]
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  have hterm : hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t ≤
      (16 * b ^ 4 * S) * (m ^ 8 * Real.exp (-b * (m ^ 2 - 1))) := by
    have h := mul_le_mul_of_nonneg_right hpoly
      (hpThetaGaussianProfile_pos (hpThetaGaussianParameter n) t).le
    rw [hprofile] at h
    unfold hpThetaGaussianKernelSecondDerivativeTerm
    rw [hprofile]
    convert h using 1 <;> dsimp [hpThetaGaussianParameter, b, m] <;> ring
  have hgrowth : m ^ 8 ≤ (256 : ℝ) ^ n := by
    have h := pow_le_pow_left₀ hm0 (hpThetaKernelUpper_nat_growth n) 8
    calc
      _ ≤ ((2 : ℝ) ^ n) ^ 8 := h
      _ = ((2 : ℝ) ^ 8) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by norm_num
  have hratio : (256 : ℝ) ^ n * Real.exp (-3 * b * (n : ℝ)) =
      (256 * Real.exp (-3 * b)) ^ n := by
    rw [mul_pow, hpThetaKernelUpper_exp_pow]
  have hS0 : 0 ≤ S := (hpThetaGaussianProfile_pos Real.pi t).le
  have hA0 : 0 ≤ 16 * b ^ 4 * S := by positivity
  have hgeom : hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t ≤
      (16 * b ^ 4 * S) * (256 * Real.exp (-3 * b)) ^ n := by
    calc
      _ ≤ _ := hterm
      _ ≤ (16 * b ^ 4 * S) *
          ((256 : ℝ) ^ n * Real.exp (-3 * b * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hgrowth hexp (Real.exp_nonneg _) (by positivity)) hA0
      _ = _ := by rw [hratio]
  have hR := hpDensityPilot_second_ratio_bounds b hb.1
  have hcoef : 16 * b ^ 4 * S ≤ 7998 * S :=
    mul_le_mul_of_nonneg_right (hpDensityPilot_polynomial_bounds b hb).2.2.2.2.2.2 hS0
  exact hgeom.trans (mul_le_mul hcoef (pow_le_pow_left₀ hR.1 hR.2 n)
    (pow_nonneg hR.1 n) (by positivity))

theorem hpThetaDensityPilot_second_remainder_le (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t -
      hpThetaGaussianKernelSecondDerivativeTerm Real.pi t ≤
      2 * hpThetaGaussianProfile Real.pi t := by
  let A := 7998 * hpThetaGaussianProfile Real.pi t
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t) := by
    rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
    exact (hpThetaGaussianKernelSecondDerivativeTerm_summable t).hasSum
  have htail : HasSum
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) t)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t -
        hpThetaGaussianKernelSecondDerivativeTerm Real.pi t) := by
    simpa [hpThetaGaussianParameter] using (hasSum_nat_add_iff' 1).mpr hactual
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) t ≤
        (A / 4000) * (1 / 4000 : ℝ) ^ n := by
    intro n
    have h := hpThetaDensityPilot_secondTerm_le_geometric (n + 1) t ht
    simpa only [A, pow_succ, div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have hgeom : HasSum (fun n : ℕ => (A / 4000) * (1 / 4000 : ℝ) ^ n)
      ((A / 4000) * (1 - (1 / 4000 : ℝ))⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 4000 : ℝ))
      (by norm_num : (1 / 4000 : ℝ) < 1)).mul_left (A / 4000)
  have h := hasSum_le hpoint htail hgeom
  have heq : (A / 4000) * (1 - (1 / 4000 : ℝ))⁻¹ =
      2 * hpThetaGaussianProfile Real.pi t := by norm_num [A] <;> ring
  rw [heq] at h
  exact h

private theorem hpDensityPilot_firstDerivative_le (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    deriv hpRiemannThetaDifferentialKernel t ≤ hpThetaGaussianKernelDerivativeTerm Real.pi t := by
  have hs := hpThetaGaussianKernelDerivativeTerm_summable t
  have htail : (∑' n : ℕ,
      hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t) ≤ 0 :=
    tsum_nonpos (fun n => (hpThetaCNV_kernelDerivativeTerm_neg_on_far (n + 1) t ht).le)
  have hparam : hpThetaGaussianParameter 0 = Real.pi := by simp [hpThetaGaussianParameter]
  rw [hpThetaPhi_deriv_eq_kernelSeries, hs.tsum_eq_zero_add, hparam]
  linarith

private theorem hpDensityPilot_first_identities (t : ℝ) :
    hpThetaGaussianKernelTerm Real.pi t =
      (4 * (Real.pi * Real.exp (2 * t)) ^ 2 - 6 * (Real.pi * Real.exp (2 * t))) *
        hpThetaGaussianProfile Real.pi t ∧
    -hpThetaGaussianKernelDerivativeTerm Real.pi t =
      (8 * (Real.pi * Real.exp (2 * t)) ^ 3 -
        30 * (Real.pi * Real.exp (2 * t)) ^ 2 + 15 * (Real.pi * Real.exp (2 * t))) *
        hpThetaGaussianProfile Real.pi t ∧
    hpThetaGaussianKernelSecondDerivativeTerm Real.pi t =
      (16 * (Real.pi * Real.exp (2 * t)) ^ 4 -
        112 * (Real.pi * Real.exp (2 * t)) ^ 3 +
        165 * (Real.pi * Real.exp (2 * t)) ^ 2 -
        (75 / 2 : ℝ) * (Real.pi * Real.exp (2 * t))) *
        hpThetaGaussianProfile Real.pi t := by
  refine ⟨?_, ?_, ?_⟩ <;>
    dsimp [hpThetaGaussianKernelTerm, hpThetaGaussianKernelDerivativeTerm,
      hpThetaGaussianKernelSecondDerivativeTerm] <;> ring

theorem hpThetaDensityPilot_scaled_kernel_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    hpRiemannThetaDifferentialKernel t / hpThetaGaussianProfile Real.pi t ∈
      Set.Icc (59 : ℝ) 61 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hfar : (1 / 50 : ℝ) ≤ t := by linarith [ht.1]
  let S := hpThetaGaussianProfile Real.pi t
  have hS : 0 < S := hpThetaGaussianProfile_pos Real.pi t
  have hp := hpDensityPilot_polynomial_bounds _ (hpThetaDensityPilot_parameter_bounds t ht)
  have hid := (hpDensityPilot_first_identities t).1
  have hlo := hpThetaPhi_first_term_le t ht0
  have hfirstL := mul_le_mul_of_nonneg_right hp.1 hS.le
  have hfirstU := mul_le_mul_of_nonneg_right hp.2.1 hS.le
  rw [← hid] at hfirstL hfirstU
  have hr := hpThetaCNV_farKernelRatio_bounds t hfar
  have hc : hpThetaCNVFarKernelCoefficient t ≤ (1005 / 1003 : ℝ) := by
    have hd : 0 < 1 - hpThetaCNVFarKernelRatio t := by linarith [hr.2]
    unfold hpThetaCNVFarKernelCoefficient
    apply (div_le_iff₀ hd).mpr
    linarith [hr.2]
  have hcu := hpThetaPhi_le_frozen_firstTerm_upper t t hfar le_rfl
  have hmult := mul_le_mul hc hfirstU
    (hpThetaKernelUpper_first_nonneg t ht0) (by norm_num : (0 : ℝ) ≤ 1005 / 1003)
  constructor
  · apply (le_div_iff₀ hS).mpr
    exact hfirstL.trans hlo
  · apply (div_le_iff₀ hS).mpr
    have hscale := mul_le_mul_of_nonneg_right
      (by norm_num : (1005 / 1003 : ℝ) * 60 ≤ 61) hS.le
    nlinarith only [hcu, hmult, hscale]

theorem hpThetaDensityPilot_scaled_neg_deriv_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    -deriv hpRiemannThetaDifferentialKernel t / hpThetaGaussianProfile Real.pi t ∈
      Set.Icc (230 : ℝ) 240 := by
  have hfar : (1 / 50 : ℝ) ≤ t := by linarith [ht.1]
  have hS := hpThetaGaussianProfile_pos Real.pi t
  have hp := hpDensityPilot_polynomial_bounds _ (hpThetaDensityPilot_parameter_bounds t ht)
  have hid := (hpDensityPilot_first_identities t).2.1
  have hlo := hpDensityPilot_firstDerivative_le t hfar
  have hfirstL := mul_le_mul_of_nonneg_right hp.2.2.1 hS.le
  have hfirstU := mul_le_mul_of_nonneg_right hp.2.2.2.1 hS.le
  rw [← hid] at hfirstL hfirstU
  have hrem := hpThetaPhi_abs_deriv_le_first_add_remainder_on_far t hfar
  rw [abs_of_neg (hpThetaPhi_deriv_neg_on_far t hfar)] at hrem
  have hAU := mul_le_mul_of_nonneg_right hp.2.2.2.2.2.1 hS.le
  have hA : hpThetaCNVFarDerivativeAmplitude t / 250 ≤
      4 * hpThetaGaussianProfile Real.pi t := by
    dsimp [hpThetaCNVFarDerivativeAmplitude]
    nlinarith only [hAU]
  constructor
  · apply (le_div_iff₀ hS).mpr
    linarith only [hfirstL, hlo]
  · apply (div_le_iff₀ hS).mpr
    linarith only [hrem, hfirstU, hA]

theorem hpThetaDensityPilot_scaled_second_deriv_le (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t /
      hpThetaGaussianProfile Real.pi t ≤ (-350 : ℝ) := by
  have hS := hpThetaGaussianProfile_pos Real.pi t
  have hp := hpDensityPilot_polynomial_bounds _ (hpThetaDensityPilot_parameter_bounds t ht)
  have hid := (hpDensityPilot_first_identities t).2.2
  have hfirst := mul_le_mul_of_nonneg_right hp.2.2.2.2.1 hS.le
  rw [← hid] at hfirst
  have hrem := hpThetaDensityPilot_second_remainder_le t ht
  apply (div_le_iff₀ hS).mpr
  linarith only [hfirst, hrem]

theorem hpThetaPhiDensityCurvature_ge_seventy_gaussian_sq_on_pilot (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    70 * hpThetaGaussianProfile Real.pi t ^ 2 ≤ hpThetaPhiDensityCurvature t := by
  have h := hpThetaPhiDensityCurvature_lower_of_scaled_bounds
    (1 / 5) (200001 / 1000000) 59 61 230 240 (-350) t
    (hpThetaGaussianProfile Real.pi t) (by norm_num) ht
    (hpThetaGaussianProfile_pos Real.pi t) (by norm_num) (by norm_num)
    (hpThetaDensityPilot_scaled_kernel_bounds t ht)
    (hpThetaDensityPilot_scaled_neg_deriv_bounds t ht)
    (hpThetaDensityPilot_scaled_second_deriv_le t ht)
  norm_num [hpThetaDensityCurvatureBoxMargin] at h ⊢
  exact h

theorem hpThetaPhiDensityCurvature_pos_on_pilot_cell (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    0 < hpThetaPhiDensityCurvature t := by
  exact (mul_pos (by norm_num : (0 : ℝ) < 70)
    (sq_pos_of_pos (hpThetaGaussianProfile_pos Real.pi t))).trans_le
    (hpThetaPhiDensityCurvature_ge_seventy_gaussian_sq_on_pilot t ht)

#print axioms hpThetaDensityPilot_exp_lower
#print axioms hpThetaDensityPilot_exp_upper
#print axioms hpThetaDensityPilot_exp_fourteen_lower
#print axioms hpThetaDensityPilot_parameter_bounds
#print axioms hpThetaDensityPilot_secondTerm_le_geometric
#print axioms hpThetaDensityPilot_second_remainder_le
#print axioms hpThetaDensityPilot_scaled_kernel_bounds
#print axioms hpThetaDensityPilot_scaled_neg_deriv_bounds
#print axioms hpThetaDensityPilot_scaled_second_deriv_le
#print axioms hpThetaPhiDensityCurvature_ge_seventy_gaussian_sq_on_pilot
#print axioms hpThetaPhiDensityCurvature_pos_on_pilot_cell
end HodgeProofHP
