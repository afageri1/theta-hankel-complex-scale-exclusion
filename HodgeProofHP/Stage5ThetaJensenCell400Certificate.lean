import HodgeProofHP.Stage5ThetaJensenTailNumericBounds
import Mathlib.Tactic

/-!
# A kernel-checked interval certificate for Jensen cell 400

The cell is [1/4, 401/1600]. Rational data are checked with norm_num;
Taylor certificates enclose the actual exponential. No JSON is trusted.
This module does not claim the complete moment inequality.
-/

noncomputable section
namespace HodgeProofHP

theorem hpThetaJensen_exp_lower_scaled32
    (x a q : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hs : a ≤ hpThetaTraceExpTaylorSum (x / 32) 12)
    (hp : q ≤ a ^ 32) : q ≤ Real.exp x := by
  have h := hpThetaTrace_exp_lower_of_taylor (x / 32) a 12
    (by positivity) hs
  have hpow := pow_le_pow_left₀ ha h 32
  have he : (Real.exp (x / 32)) ^ 32 = Real.exp x := by
    rw [hpThetaKernelUpper_exp_pow]
    congr 1
    norm_num
  rw [he] at hpow
  exact le_trans hp hpow

theorem hpThetaJensen_exp_upper_scaled32
    (x a q : ℝ) (hx : 0 ≤ x) (hx32 : x ≤ 32)
    (hs : hpThetaTraceExpTaylorUpper (x / 32) 12 ≤ a)
    (hp : a ^ 32 ≤ q) : Real.exp x ≤ q := by
  have h := hpThetaTrace_exp_upper_of_taylor (x / 32) a 12
    (by positivity) (by linarith) (by norm_num) hs
  have hpow := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h 32
  have he : (Real.exp (x / 32)) ^ 32 = Real.exp x := by
    rw [hpThetaKernelUpper_exp_pow]
    congr 1
    norm_num
  rw [he] at hpow
  exact le_trans hpow hp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell400_leftExp :
    (8243606353 / 5000000000 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 2 : ℝ) (507873854293 / 500000000000 : ℝ) (8243606353
    / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell400_rightExp :
    Real.exp (401 / 800 : ℝ) ≤ (1650783461 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (401 / 800 : ℝ) (1015787387007 / 1000000000000 : ℝ)
    (1650783461 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell400_denomUpper :
    Real.exp (5061089765593373 / 1000000000000000 : ℝ) ≤ (788811733289 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5061089765593373 / 1000000000000000 : ℝ) (1171352489567
    / 1000000000000 : ℝ) (788811733289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell400_denomLower :
    (1566943439483 / 10000000000 : ℝ) ≤ Real.exp (3158935658716747 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3158935658716747 / 625000000000000 : ℝ) (1171103870339 /
    1000000000000 : ℝ) (1566943439483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell400_product_lower :
    (3237255971216747 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 2 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell400_leftExp
    (by norm_num : (0 : ℝ) ≤ (8243606353 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell400_product_upper :
    Real.pi * Real.exp (401 / 800 : ℝ) ≤ (5186089765593373 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell400_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell400_endpointLower :
    (4832316761 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 4 : ℝ) (401 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3237255971216747 / 625000000000000 : ℝ) (Real.pi * Real.exp (1 / 2 : ℝ))
    (by norm_num) hpThetaJensenCell400_product_lower
  have hD : Real.exp (Real.pi * Real.exp (401 / 800 : ℝ) - (1 / 8 : ℝ)) ≤
      (788811733289 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell400_denomUpper
    linarith [hpThetaJensenCell400_product_upper]
  have hi : (1 / (788811733289 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (401 / 800 : ℝ) - (1 / 8 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (788811733289 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (788811733289 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 8 : ℝ) - Real.pi * Real.exp (401 / 800 : ℝ)) := by
    rw [show (1 / 8 : ℝ) - Real.pi * Real.exp (401 / 800 : ℝ) =
      -(Real.pi * Real.exp (401 / 800 : ℝ) - (1 / 8 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 2 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 2 : ℝ)) := by
    have h := hpThetaJensenCell400_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (788811733289 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell400_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 4 : ℝ) (401 / 1600 : ℝ) ≤ (4892770341 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (401 / 800 : ℝ)) (5186089765593373 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (401 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell400_product_upper
  have hD : (1566943439483 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 2 : ℝ) - (401 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell400_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell400_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 2 : ℝ) - (401 / 3200 : ℝ)) ≤
      (1 / (1566943439483 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1566943439483 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((401 / 3200 : ℝ) - Real.pi * Real.exp (1 / 2 : ℝ)) ≤
      (2 / (1566943439483 / 10000000000 : ℝ) : ℝ) := by
    rw [show (401 / 3200 : ℝ) - Real.pi * Real.exp (1 / 2 : ℝ) =
      -(Real.pi * Real.exp (1 / 2 : ℝ) - (401 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5186089765593373 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5186089765593373 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell400_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 4 : ℝ) (401 / 1600 : ℝ)) :
    (4832316761 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4892770341 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell400_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell400_endpointUpper

#print axioms hpThetaJensen_exp_lower_scaled32
#print axioms hpThetaJensen_exp_upper_scaled32
#print axioms hpThetaJensenCell400_leftExp
#print axioms hpThetaJensenCell400_rightExp
#print axioms hpThetaJensenCell400_denomUpper
#print axioms hpThetaJensenCell400_denomLower
#print axioms hpThetaJensenCell400_product_lower
#print axioms hpThetaJensenCell400_product_upper
#print axioms hpThetaJensenCell400_endpointLower
#print axioms hpThetaJensenCell400_endpointUpper
#print axioms hpThetaJensenCell400_kernel_bounds

end HodgeProofHP
