/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityUpperExpCoverage

/-! Analytic bounds for the unbounded density interval. No sampling is used. -/
noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- A fixed Taylor certificate supplies the large numerical exponential constant.
theorem hpThetaDensityOuter_exp_cubic_lower (b : ℝ) (hb : 8 ≤ b) :
    10000 * b ^ 4 ≤ Real.exp (3 * b) := by
  let z := b - 8
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz2 := pow_nonneg hz 2
  have hz3 := pow_nonneg hz 3
  have hz4 := pow_nonneg hz 4
  have hc : (100000000 : ℝ) ≤ Real.exp 24 := by
    exact hpThetaTrace_exp_lower_of_taylor 24 100000000 16 (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have he : hpThetaTraceExpTaylorSum (3 * z) 5 ≤ Real.exp (3 * z) := by
    apply hpThetaTrace_exp_lower_of_taylor (3 * z)
      (hpThetaTraceExpTaylorSum (3 * z) 5) 5 (by positivity)
    exact le_rfl
  have hp : 10000 * b ^ 4 ≤
      100000000 * hpThetaTraceExpTaylorSum (3 * z) 5 := by
    have hbz : b = z + 8 := by dsimp [z]; ring
    rw [hbz]
    norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial]
    nlinarith only [hz, hz2, hz3, hz4]
  have hm := mul_le_mul hc he
    (show 0 ≤ hpThetaTraceExpTaylorSum (3 * z) 5 by
      norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial]
      positivity) (Real.exp_nonneg 24)
  calc
    _ ≤ 100000000 * hpThetaTraceExpTaylorSum (3 * z) 5 := hp
    _ ≤ Real.exp 24 * Real.exp (3 * z) := hm
    _ = Real.exp (3 * b) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [z]
      ring

theorem hpThetaDensityOuter_parameter_ge_eight (t : ℝ) (ht : (1 / 2 : ℝ) ≤ t) :
    8 ≤ Real.pi * Real.exp (2 * t) := by
  have he1 : (8 / 3 : ℝ) ≤ Real.exp 1 := by
    exact hpThetaTrace_exp_lower_of_taylor 1 (8 / 3) 4 (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have he : (8 / 3 : ℝ) ≤ Real.exp (2 * t) :=
    he1.trans (Real.exp_le_exp.mpr (by linarith))
  have hm := mul_le_mul Real.pi_gt_three.le he (by norm_num : (0 : ℝ) ≤ 8 / 3)
    Real.pi_pos.le
  nlinarith only [hm]

theorem hpThetaDensityOuter_exp_moment_bounds (b : ℝ) (hb : 8 ≤ b) :
    Real.exp (-3 * b) ≤ (1 / 10000 : ℝ) ∧
    b ^ 2 * Real.exp (-3 * b) ≤ (1 / 10000 : ℝ) ∧
    b ^ 3 * Real.exp (-3 * b) ≤ (1 / 10000 : ℝ) ∧
    b ^ 4 * Real.exp (-3 * b) ≤ (1 / 10000 : ℝ) := by
  have hb0 : 0 ≤ b := by linarith
  have hb2 : (1 : ℝ) ≤ b ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (show (1 : ℝ) ≤ b by linarith) 2
    simpa only [one_pow] using h
  have hb4 : (1 : ℝ) ≤ b ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (show (1 : ℝ) ≤ b by linarith) 4
    simpa only [one_pow] using h
  have h24 : b ^ 2 ≤ b ^ 4 := by
    have h := mul_nonneg (sq_nonneg b) (show 0 ≤ b ^ 2 - 1 by linarith)
    nlinarith only [h]
  have h34 : b ^ 3 ≤ b ^ 4 := by
    have h := mul_nonneg (pow_nonneg hb0 3) (show 0 ≤ b - 1 by linarith)
    nlinarith only [h]
  have he0 := Real.exp_nonneg (-3 * b)
  have hm := mul_le_mul_of_nonneg_right (hpThetaDensityOuter_exp_cubic_lower b hb) he0
  have hid : Real.exp (3 * b) * Real.exp (-3 * b) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hid] at hm
  have h4 : b ^ 4 * Real.exp (-3 * b) ≤ (1 / 10000 : ℝ) := by
    nlinarith only [hm]
  have h0 := mul_le_mul_of_nonneg_right hb4 he0
  have h2 := mul_le_mul_of_nonneg_right h24 he0
  have h3 := mul_le_mul_of_nonneg_right h34 he0
  exact ⟨by nlinarith only [h0, h4], h2.trans h4, h3.trans h4, h4⟩

private theorem hpDensityOuter_first_identities (t : ℝ) :
    hpThetaGaussianKernelTerm Real.pi t =
      hpThetaDensityTwoTermP (Real.pi * Real.exp (2 * t)) * hpThetaGaussianProfile Real.pi t ∧
    -hpThetaGaussianKernelDerivativeTerm Real.pi t =
      hpThetaDensityTwoTermD (Real.pi * Real.exp (2 * t)) * hpThetaGaussianProfile Real.pi t ∧
    hpThetaGaussianKernelSecondDerivativeTerm Real.pi t =
      hpThetaDensityTwoTermQ (Real.pi * Real.exp (2 * t)) * hpThetaGaussianProfile Real.pi t := by
  refine ⟨?_, ?_, ?_⟩ <;>
    dsimp [hpThetaGaussianKernelTerm, hpThetaGaussianKernelDerivativeTerm,
      hpThetaGaussianKernelSecondDerivativeTerm, hpThetaDensityTwoTermP,
      hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ] <;> ring

private theorem hpDensityOuter_first_derivative_le (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    deriv hpRiemannThetaDifferentialKernel t ≤ hpThetaGaussianKernelDerivativeTerm Real.pi t := by
  have hs := hpThetaGaussianKernelDerivativeTerm_summable t
  have htail : (∑' n : ℕ,
      hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t) ≤ 0 :=
    tsum_nonpos (fun n => (hpThetaCNV_kernelDerivativeTerm_neg_on_far (n + 1) t ht).le)
  have hparam : hpThetaGaussianParameter 0 = Real.pi := by simp [hpThetaGaussianParameter]
  rw [hpThetaPhi_deriv_eq_kernelSeries, hs.tsum_eq_zero_add, hparam]
  linarith

set_option maxHeartbeats 2000000 in
-- The kernel coefficient and both infinite derivative remainders are retained.
theorem hpThetaDensityOuter_scaled_bounds (t : ℝ) (ht : (1 / 2 : ℝ) ≤ t) :
    hpRiemannThetaDifferentialKernel t / hpThetaGaussianProfile Real.pi t ∈
      Set.Icc (hpThetaDensityTwoTermP (Real.pi * Real.exp (2 * t)))
        (hpThetaDensityTwoTermP (Real.pi * Real.exp (2 * t)) + 1) ∧
    -deriv hpRiemannThetaDifferentialKernel t / hpThetaGaussianProfile Real.pi t ∈
      Set.Icc (hpThetaDensityTwoTermD (Real.pi * Real.exp (2 * t)))
        (hpThetaDensityTwoTermD (Real.pi * Real.exp (2 * t)) + 1) ∧
    deriv (deriv hpRiemannThetaDifferentialKernel) t / hpThetaGaussianProfile Real.pi t ≤
      hpThetaDensityTwoTermQ (Real.pi * Real.exp (2 * t)) + 1 := by
  let b := Real.pi * Real.exp (2 * t)
  let e := Real.exp (-3 * b)
  let S := hpThetaGaussianProfile Real.pi t
  have hb : 8 ≤ b := hpThetaDensityOuter_parameter_ge_eight t ht
  have hb0 : 0 ≤ b := by linarith
  have he := hpThetaDensityOuter_exp_moment_bounds b hb
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have heU : e ≤ (1 / 10000 : ℝ) := he.1
  have h2e : b ^ 2 * e ≤ (1 / 10000 : ℝ) := he.2.1
  have h3e : b ^ 3 * e ≤ (1 / 10000 : ℝ) := he.2.2.1
  have h4e : b ^ 4 * e ≤ (1 / 10000 : ℝ) := he.2.2.2
  have hfar : (1 / 50 : ℝ) ≤ t := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hS : 0 < S := hpThetaGaussianProfile_pos Real.pi t
  have hid := hpDensityOuter_first_identities t
  change hpThetaGaussianKernelTerm Real.pi t = hpThetaDensityTwoTermP b * S ∧
    -hpThetaGaussianKernelDerivativeTerm Real.pi t = hpThetaDensityTwoTermD b * S ∧
    hpThetaGaussianKernelSecondDerivativeTerm Real.pi t = hpThetaDensityTwoTermQ b * S at hid
  have hden : 0 < 1 - 16 * e := by linarith only [heU]
  have hPC : hpThetaCNVFarKernelCoefficient t * hpThetaDensityTwoTermP b ≤
      hpThetaDensityTwoTermP b + 1 := by
    have hcoef : hpThetaCNVFarKernelCoefficient t * hpThetaDensityTwoTermP b =
        ((1 + 16 * e) * hpThetaDensityTwoTermP b) / (1 - 16 * e) := by
      dsimp [hpThetaCNVFarKernelCoefficient, hpThetaCNVFarKernelRatio, e, b]
      ring
    rw [hcoef]
    apply (div_le_iff₀ hden).mpr
    -- The coefficient (1+q)/(1-q) contributes twice q*P.
    have hsmall2 : (16 * e) * (2 * hpThetaDensityTwoTermP b + 1) ≤ 1 := by
      dsimp [hpThetaDensityTwoTermP]
      have hbe : 0 ≤ b * e := mul_nonneg (by linarith) he0
      nlinarith only [heU, h2e, hbe]
    nlinarith only [hsmall2]
  have hkernel : hpRiemannThetaDifferentialKernel t / S ∈
      Set.Icc (hpThetaDensityTwoTermP b) (hpThetaDensityTwoTermP b + 1) := by
    constructor
    · apply (le_div_iff₀ hS).mpr
      rw [← hid.1]
      exact hpThetaPhi_first_term_le t ht0
    · apply (div_le_iff₀ hS).mpr
      have hupper := hpThetaPhi_le_frozen_firstTerm_upper t t hfar le_rfl
      rw [hid.1] at hupper
      have hm := mul_le_mul_of_nonneg_right hPC hS.le
      nlinarith only [hupper, hm]
  have hquot := hpThetaCNV_farDerivativeRatio_quotient_le_mul_ratio t hfar
  have hAmp : hpThetaCNVFarDerivativeAmplitude t = 8 * b ^ 3 * S := by
    rfl
  have hratio : hpThetaCNVFarDerivativeRatio t = 64 * e := by rfl
  rw [hratio] at hquot
  have hcoefD : (8 * b ^ 3) * ((251 / 250 : ℝ) * (64 * e)) ≤ 1 := by
    nlinarith only [h3e]
  have hRemD : hpThetaCNVFarDerivativeAmplitude t *
      (hpThetaCNVFarDerivativeRatio t / (1 - hpThetaCNVFarDerivativeRatio t)) ≤ S := by
    rw [hAmp, hratio]
    calc
      _ ≤ (8 * b ^ 3 * S) * ((251 / 250 : ℝ) * (64 * e)) :=
        mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = ((8 * b ^ 3) * ((251 / 250 : ℝ) * (64 * e))) * S := by ring
      _ ≤ 1 * S := mul_le_mul_of_nonneg_right hcoefD hS.le
      _ = S := one_mul S
  have hderiv : -deriv hpRiemannThetaDifferentialKernel t / S ∈
      Set.Icc (hpThetaDensityTwoTermD b) (hpThetaDensityTwoTermD b + 1) := by
    constructor
    · apply (le_div_iff₀ hS).mpr
      have h := hpDensityOuter_first_derivative_le t hfar
      linarith only [h, hid.2.1]
    · apply (div_le_iff₀ hS).mpr
      have h := hpThetaCNV_derivative_remainder_le_geometric t hfar
      nlinarith only [h, hRemD, hid.2.1]
  have hr0 : 0 ≤ 256 * e := by positivity
  have hr1 : 256 * e < 1 := by linarith only [heU]
  have hRemQ : (16 * b ^ 4) * (256 * e) / (1 - 256 * e) ≤ 1 := by
    apply (div_le_iff₀ (show 0 < 1 - 256 * e by linarith only [hr1])).mpr
    nlinarith only [h4e, heU]
  have hfirstQ : hpThetaGaussianKernelSecondDerivativeTerm Real.pi t / S ≤
      hpThetaDensityTwoTermQ b := by
    apply (div_le_iff₀ hS).mpr
    rw [hid.2.2]
  have hsecond := hpThetaDensityCell_scaled_second_deriv_le t (16 * b ^ 4)
    (256 * e) (hpThetaDensityTwoTermQ b) (by dsimp [b] at hb ⊢; linarith)
    le_rfl hr0 hr1 le_rfl hfirstQ
  change deriv (deriv hpRiemannThetaDifferentialKernel) t / S ≤
    hpThetaDensityTwoTermQ b + (16 * b ^ 4) * (256 * e) / (1 - 256 * e) at hsecond
  exact ⟨hkernel, hderiv, by linarith only [hsecond, hRemQ]⟩

#print axioms hpThetaDensityOuter_exp_cubic_lower
#print axioms hpThetaDensityOuter_parameter_ge_eight
#print axioms hpThetaDensityOuter_exp_moment_bounds
#print axioms hpThetaDensityOuter_scaled_bounds
end HodgeProofHP
