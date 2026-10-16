/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVFarComparisonCriterion

/-!
# Analytic closure of the CNV comparison for t >= 1

A five-term Taylor lower bound for exp(3*q) gives r*q <= 1/100 when
q >= 8 and r = 16*exp(-3*q). Coarse polynomial estimates then bound the
scalar numerator below by a positive multiple of t*q^3 for t >= 1.
No interval sampling is used. The compact interval [1/50, 1] remains an
explicit obligation in the final conditional global theorem.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_exp_three_mul_ge_linear (q : ℝ) (hq : 8 ≤ q) :
    1600 * q ≤ Real.exp (3 * q) := by
  have hq0 : 0 ≤ q := by linarith
  have hq3 : (512 : ℝ) ≤ q ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hq 3
    norm_num at h
    exact h
  have hq4 := mul_le_mul_of_nonneg_right hq3 hq0
  apply hpThetaTrace_exp_lower_of_taylor (3 * q) (1600 * q) 5 (by linarith)
  norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial]
  nlinarith [sq_nonneg q]

theorem hpThetaCNV_farParameter_ge_eight (t : ℝ) (ht : 1 ≤ t) :
    8 ≤ hpThetaCNVFarParameter t := by
  have he : (3 : ℝ) ≤ Real.exp (2 * t) := by
    have h := Real.add_one_le_exp (2 * t)
    linarith
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have h := mul_le_mul hpi he (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le
  change 8 ≤ Real.pi * Real.exp (2 * t)
  nlinarith

theorem hpThetaCNV_farKernelRatio_mul_parameter_le (t : ℝ) (ht : 1 ≤ t) :
    hpThetaCNVFarKernelRatio t * hpThetaCNVFarParameter t ≤ (1 / 100 : ℝ) := by
  let q := hpThetaCNVFarParameter t
  have hq : 8 ≤ q := hpThetaCNV_farParameter_ge_eight t ht
  have he := hpThetaCNV_exp_three_mul_ge_linear q hq
  have hprod := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-3 * q))
  have hid : Real.exp (3 * q) * Real.exp (-3 * q) = 1 := by
    rw [← Real.exp_add]
    rw [show 3 * q + -3 * q = 0 by ring, Real.exp_zero]
  rw [hid] at hprod
  change (16 * Real.exp (-3 * q)) * q ≤ (1 / 100 : ℝ)
  nlinarith

set_option maxHeartbeats 800000 in
-- The coarse polynomial estimates are deliberately separated from the analytic inputs.
theorem hpThetaCNV_scalar_numerator_pos (t q r : ℝ)
    (ht : 1 ≤ t) (hq : 8 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ (1 / 1000 : ℝ))
    (hrq : r * q ≤ (1 / 100 : ℝ)) :
    0 < t * q * (16 * q ^ 2 - 9 * q + 15 / 2) - q * (8 * q ^ 2 - 30 * q + 15) -
      r * (t * (4 * q ^ 2 - 6 * q) ^ 2 +
        (1 + t * (2 * q - 1 / 2)) * (8 * q ^ 3 - 30 * q ^ 2 + 15 * q) +
        (4016 / 125 : ℝ) * (1 + r) * (1 + t * (2 * q - 1 / 2)) * q ^ 3) := by
  let P := 4 * q ^ 2 - 6 * q
  let D := 8 * q ^ 3 - 30 * q ^ 2 + 15 * q
  let F := 1 + t * (2 * q - 1 / 2)
  let A := q * (16 * q ^ 2 - 9 * q + 15 / 2)
  change 0 < t * A - D - r * (t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3)
  have ht0 : 0 ≤ t := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  have hqpow : 0 ≤ q ^ 3 := pow_nonneg hq0 3
  have hP0 : 0 ≤ P := by
    have h := mul_nonneg hq0 (show 0 ≤ 4 * q - 6 by linarith)
    dsimp [P]
    nlinarith
  have hP : P ≤ 4 * q ^ 2 := by dsimp [P]; linarith
  have hP2 : P ^ 2 ≤ 16 * q ^ 4 := by
    have h := pow_le_pow_left₀ hP0 hP 2
    nlinarith
  have hD0 : 0 ≤ D := by
    have h := mul_nonneg hq0 (show 0 ≤ 8 * q - 30 by linarith)
    have hquad : 0 ≤ 8 * q ^ 2 - 30 * q + 15 := by nlinarith
    have hprod := mul_nonneg hq0 hquad
    dsimp [D]
    nlinarith
  have hD : D ≤ 8 * q ^ 3 := by
    have h := mul_nonneg hq0 (show 0 ≤ 2 * q - 1 by linarith)
    dsimp [D]
    nlinarith
  have hF0 : 0 ≤ F := by
    have hk : 0 ≤ 2 * q - (1 / 2 : ℝ) := by linarith
    dsimp [F]
    positivity
  have hF : F ≤ 3 * t * q := by
    have h := mul_le_mul_of_nonneg_right ht hq0
    dsimp [F]
    nlinarith
  have hcoef : (4016 / 125 : ℝ) * (1 + r) ≤ 33 := by linarith
  have hbase : 8 * t * q ^ 3 ≤ t * A - D := by
    have hnonneg := mul_nonneg hq0 (show 0 ≤ 21 * q - (15 / 2 : ℝ) by linarith)
    have hAD : 8 * q ^ 3 ≤ A - D := by dsimp [A, D]; nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hAD ht0
    have hDscaled := mul_le_mul_of_nonneg_right ht hD0
    nlinarith only [hscaled, hDscaled]
  have hPscaled := mul_le_mul_of_nonneg_left hP2 ht0
  have hFD : F * D ≤ 24 * t * q ^ 4 := by
    have h := mul_le_mul hF hD hD0 (show 0 ≤ 3 * t * q by positivity)
    nlinarith only [h]
  have hR : (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3 ≤ 99 * t * q ^ 4 := by
    have h1 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hF0 hqpow)
    have h2 := mul_le_mul_of_nonneg_left hF (show 0 ≤ 33 * q ^ 3 by positivity)
    nlinarith only [h1, h2]
  have hsum : t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3 ≤
      139 * t * q ^ 4 := by nlinarith only [hPscaled, hFD, hR]
  have hscaled := mul_le_mul_of_nonneg_left hsum hr0
  have hsmall := mul_le_mul_of_nonneg_right hrq
    (show 0 ≤ 139 * t * q ^ 3 by positivity)
  have herror : r * (t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3) ≤
      (139 / 100 : ℝ) * t * q ^ 3 := by nlinarith only [hscaled, hsmall]
  have hpos : 0 < t * q ^ 3 := mul_pos (by linarith) (pow_pos hqpos 3)
  nlinarith only [hbase, herror, hpos]

theorem hpThetaCNV_farComparisonNumerator_pos_on_outer (t : ℝ) (ht : 1 ≤ t) :
    0 < hpThetaCNVFarComparisonNumerator t := by
  have hfar : (1 / 50 : ℝ) ≤ t := by linarith
  have hr := hpThetaCNV_farKernelRatio_bounds t hfar
  have hr1 : hpThetaCNVFarKernelRatio t ≤ (1 / 1000 : ℝ) := by linarith [hr.2]
  have h := hpThetaCNV_scalar_numerator_pos t (hpThetaCNVFarParameter t)
    (hpThetaCNVFarKernelRatio t) ht (hpThetaCNV_farParameter_ge_eight t ht)
    hr.1 hr1 (hpThetaCNV_farKernelRatio_mul_parameter_le t ht)
  simpa only [hpThetaCNVFarComparisonNumerator, hpThetaCNVFarKernelPolynomial,
    hpThetaCNVFarDerivativePolynomial, hpThetaCNVFarTailPolynomial] using h

theorem hpThetaPhiCNVTailExpression_pos_on_outer (t : ℝ) (ht : 1 ≤ t) :
    0 < hpThetaPhiCNVTailExpression t := by
  have hfar : (1 / 50 : ℝ) ≤ t := by linarith
  exact hpThetaPhiCNVTailExpression_pos_of_far_margin t hfar
    ((hpThetaCNV_farComparisonMargin_pos_iff t hfar).mpr
      (hpThetaCNV_farComparisonNumerator_pos_on_outer t ht))

theorem hpThetaCNV_weightedTail_comparison_on_outer (t : ℝ) (ht : 1 ≤ t) :
    hpThetaPhiWeightedTail t * |deriv hpRiemannThetaDifferentialKernel t| <
      t * hpRiemannThetaDifferentialKernel t ^ 2 := by
  exact hpThetaCNV_far_weightedTail_comparison_of_numerator t (by linarith)
    (hpThetaCNV_farComparisonNumerator_pos_on_outer t ht)

theorem hpThetaPhiCNVTailPositive_of_compact_numerator
    (hcompact : ∀ t ∈ Set.Icc (1 / 50 : ℝ) 1, 0 < hpThetaCNVFarComparisonNumerator t) :
    hpThetaPhiCNVTailPositive := by
  apply hpThetaPhiCNVTailPositive_of_far_numerator
  intro t ht
  by_cases houter : 1 ≤ t
  · exact hpThetaCNV_farComparisonNumerator_pos_on_outer t houter
  · exact hcompact t ⟨ht, (lt_of_not_ge houter).le⟩

#print axioms hpThetaCNV_exp_three_mul_ge_linear
#print axioms hpThetaCNV_farParameter_ge_eight
#print axioms hpThetaCNV_farKernelRatio_mul_parameter_le
#print axioms hpThetaCNV_scalar_numerator_pos
#print axioms hpThetaCNV_farComparisonNumerator_pos_on_outer
#print axioms hpThetaPhiCNVTailExpression_pos_on_outer
#print axioms hpThetaCNV_weightedTail_comparison_on_outer
#print axioms hpThetaPhiCNVTailPositive_of_compact_numerator
end HodgeProofHP
