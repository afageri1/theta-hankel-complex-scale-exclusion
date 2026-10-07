import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell580_leftExp :
    (20647310999 / 10000000000 : ℝ) ≤ Real.exp (29 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 40 : ℝ) (1022914852123 / 1000000000000 : ℝ)
    (20647310999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell580_rightExp :
    Real.exp (581 / 800 : ℝ) ≤ (5168284069 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (581 / 800 : ℝ) (255738702629 / 250000000000 : ℝ)
    (5168284069 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell580_denomUpper :
    Real.exp (15783520053181917 / 2500000000000000 : ℝ) ≤ (5519227116197 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15783520053181917 / 2500000000000000 : ℝ) (609051055449
    / 500000000000 : ℝ) (5519227116197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell580_denomLower :
    (5472907547789 / 10000000000 : ℝ) ≤ Real.exp (7881225256996301 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7881225256996301 / 1250000000000000 : ℝ) (76111333907 /
    62500000000 : ℝ) (5472907547789 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell580_product_lower :
    (8108178381996301 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell580_leftExp
    (by norm_num : (0 : ℝ) ≤ (20647310999 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell580_product_upper :
    Real.pi * Real.exp (581 / 800 : ℝ) ≤ (16236645053181917 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell580_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell580_endpointLower :
    (1172099699 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 80 : ℝ) (581 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8108178381996301 / 1250000000000000 : ℝ) (Real.pi * Real.exp (29 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell580_product_lower
  have hD : Real.exp (Real.pi * Real.exp (581 / 800 : ℝ) - (29 / 160 : ℝ)) ≤
      (5519227116197 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell580_denomUpper
    linarith [hpThetaJensenCell580_product_upper]
  have hi : (1 / (5519227116197 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (581 / 800 : ℝ) - (29 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5519227116197 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5519227116197 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 160 : ℝ) - Real.pi * Real.exp (581 / 800 : ℝ)) := by
    rw [show (29 / 160 : ℝ) - Real.pi * Real.exp (581 / 800 : ℝ) =
      -(Real.pi * Real.exp (581 / 800 : ℝ) - (29 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 40 : ℝ)) := by
    have h := hpThetaJensenCell580_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5519227116197 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell580_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 80 : ℝ) (581 / 1600 : ℝ) ≤ (950837147 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (581 / 800 : ℝ)) (16236645053181917 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (581 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell580_product_upper
  have hD : (5472907547789 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 40 : ℝ) - (581 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell580_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell580_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 40 : ℝ) - (581 / 3200 : ℝ)) ≤
      (1 / (5472907547789 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5472907547789 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((581 / 3200 : ℝ) - Real.pi * Real.exp (29 / 40 : ℝ)) ≤
      (2 / (5472907547789 / 10000000000 : ℝ) : ℝ) := by
    rw [show (581 / 3200 : ℝ) - Real.pi * Real.exp (29 / 40 : ℝ) =
      -(Real.pi * Real.exp (29 / 40 : ℝ) - (581 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16236645053181917 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (16236645053181917 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell580_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 80 : ℝ) (581 / 1600 : ℝ)) :
    (1172099699 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (950837147 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell580_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell580_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell581_leftExp :
    (826925451 / 400000000 : ℝ) ≤ Real.exp (581 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (581 / 800 : ℝ) (204590962103 / 200000000000 : ℝ)
    (826925451 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell581_rightExp :
    Real.exp (291 / 400 : ℝ) ≤ (4139798771 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (291 / 400 : ℝ) (1022994770469 / 1000000000000 : ℝ)
    (4139798771 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell581_denomUpper :
    Real.exp (12642437840382203 / 2000000000000000 : ℝ) ≤ (5562506044833 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12642437840382203 / 2000000000000000 : ℝ) (304599868613
    / 250000000000 : ℝ) (5562506044833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell581_denomLower :
    (2757883636119 / 5000000000 : ℝ) ≤ Real.exp (315639047682249 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (315639047682249 / 50000000000000 : ℝ) (152259780171 /
    125000000000 : ℝ) (2757883636119 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell581_product_lower :
    (324732797682249 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (581 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell581_leftExp
    (by norm_num : (0 : ℝ) ≤ (826925451 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell581_product_upper :
    Real.pi * Real.exp (291 / 400 : ℝ) ≤ (13005562840382203 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell581_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell581_endpointLower :
    (291582353 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (581 / 1600 : ℝ) (291 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (324732797682249 / 50000000000000 : ℝ) (Real.pi * Real.exp (581 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell581_product_lower
  have hD : Real.exp (Real.pi * Real.exp (291 / 400 : ℝ) - (581 / 3200 : ℝ)) ≤
      (5562506044833 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell581_denomUpper
    linarith [hpThetaJensenCell581_product_upper]
  have hi : (1 / (5562506044833 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (291 / 400 : ℝ) - (581 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5562506044833 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5562506044833 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((581 / 3200 : ℝ) - Real.pi * Real.exp (291 / 400 : ℝ)) := by
    rw [show (581 / 3200 : ℝ) - Real.pi * Real.exp (291 / 400 : ℝ) =
      -(Real.pi * Real.exp (291 / 400 : ℝ) - (581 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (581 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (581 / 800 : ℝ)) := by
    have h := hpThetaJensenCell581_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5562506044833 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell581_endpointUpper :
    hpThetaJensenKernelEndpointUpper (581 / 1600 : ℝ) (291 / 800 : ℝ) ≤ (94616517 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (291 / 400 : ℝ)) (13005562840382203 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (291 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell581_product_upper
  have hD : (2757883636119 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (581 / 800 : ℝ) - (291 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell581_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell581_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (581 / 800 : ℝ) - (291 / 1600 : ℝ)) ≤
      (1 / (2757883636119 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2757883636119 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((291 / 1600 : ℝ) - Real.pi * Real.exp (581 / 800 : ℝ)) ≤
      (2 / (2757883636119 / 5000000000 : ℝ) : ℝ) := by
    rw [show (291 / 1600 : ℝ) - Real.pi * Real.exp (581 / 800 : ℝ) =
      -(Real.pi * Real.exp (581 / 800 : ℝ) - (291 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13005562840382203 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (13005562840382203 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell581_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (581 / 1600 : ℝ) (291 / 800 : ℝ)) :
    (291582353 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (94616517 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell581_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell581_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell582_leftExp :
    (20698993853 / 10000000000 : ℝ) ≤ Real.exp (291 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (291 / 400 : ℝ) (255748692617 / 250000000000 : ℝ)
    (20698993853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell582_rightExp :
    Real.exp (583 / 800 : ℝ) ≤ (828995351 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (583 / 800 : ℝ) (1023034731983 / 1000000000000 : ℝ)
    (828995351 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell582_denomUpper :
    Real.exp (2531615991734143 / 400000000000000 : ℝ) ≤ (1401545326121 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2531615991734143 / 400000000000000 : ℝ) (243739459509 /
    200000000000 : ℝ) (1401545326121 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell582_denomLower :
    (555901905451 / 1000000000 : ℝ) ≤ Real.exp (7900739812079247 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7900739812079247 / 1250000000000000 : ℝ) (243675119797 /
    200000000000 : ℝ) (555901905451 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell582_product_lower :
    (8128474187079247 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (291 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell582_leftExp
    (by norm_num : (0 : ℝ) ≤ (20698993853 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell582_product_upper :
    Real.pi * Real.exp (583 / 800 : ℝ) ≤ (2604365991734143 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell582_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell582_endpointLower :
    (4642300129 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (291 / 800 : ℝ) (583 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8128474187079247 / 1250000000000000 : ℝ) (Real.pi * Real.exp (291 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell582_product_lower
  have hD : Real.exp (Real.pi * Real.exp (583 / 800 : ℝ) - (291 / 1600 : ℝ)) ≤
      (1401545326121 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell582_denomUpper
    linarith [hpThetaJensenCell582_product_upper]
  have hi : (1 / (1401545326121 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (583 / 800 : ℝ) - (291 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1401545326121 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1401545326121 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((291 / 1600 : ℝ) - Real.pi * Real.exp (583 / 800 : ℝ)) := by
    rw [show (291 / 1600 : ℝ) - Real.pi * Real.exp (583 / 800 : ℝ) =
      -(Real.pi * Real.exp (583 / 800 : ℝ) - (291 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (291 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (291 / 400 : ℝ)) := by
    have h := hpThetaJensenCell582_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1401545326121 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell582_endpointUpper :
    hpThetaJensenKernelEndpointUpper (291 / 800 : ℝ) (583 / 1600 : ℝ) ≤ (2353765053 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (583 / 800 : ℝ)) (2604365991734143 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (583 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell582_product_upper
  have hD : (555901905451 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (291 / 400 : ℝ) - (583 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell582_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell582_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (291 / 400 : ℝ) - (583 / 3200 : ℝ)) ≤
      (1 / (555901905451 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (555901905451 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((583 / 3200 : ℝ) - Real.pi * Real.exp (291 / 400 : ℝ)) ≤
      (2 / (555901905451 / 1000000000 : ℝ) : ℝ) := by
    rw [show (583 / 3200 : ℝ) - Real.pi * Real.exp (291 / 400 : ℝ) =
      -(Real.pi * Real.exp (291 / 400 : ℝ) - (583 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2604365991734143 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2604365991734143 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell582_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (291 / 800 : ℝ) (583 / 1600 : ℝ)) :
    (4642300129 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2353765053 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell582_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell582_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell583_leftExp :
    (20724883773 / 10000000000 : ℝ) ≤ Real.exp (583 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (583 / 800 : ℝ) (511517365991 / 500000000000 : ℝ)
    (20724883773 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell583_rightExp :
    Real.exp (73 / 100 : ℝ) ≤ (10375403039 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 100 : ℝ) (511537347529 / 500000000000 : ℝ)
    (10375403039 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell583_denomUpper :
    Real.exp (31684356059501127 / 5000000000000000 : ℝ) ≤ (5650256972119 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31684356059501127 / 5000000000000000 : ℝ) (609497790489
    / 500000000000 : ℝ) (5650256972119 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell583_denomLower :
    (1400666730181 / 2500000000 : ℝ) ≤ Real.exp (7910516132773327 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7910516132773327 / 1250000000000000 : ℝ) (1218673416143
    / 1000000000000 : ℝ) (1400666730181 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell583_product_lower :
    (8138641132773327 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (583 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell583_leftExp
    (by norm_num : (0 : ℝ) ≤ (20724883773 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell583_product_upper :
    Real.pi * Real.exp (73 / 100 : ℝ) ≤ (32595293559501127 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell583_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell583_endpointLower :
    (923869273 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (583 / 1600 : ℝ) (73 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8138641132773327 / 1250000000000000 : ℝ) (Real.pi * Real.exp (583 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell583_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 100 : ℝ) - (583 / 3200 : ℝ)) ≤
      (5650256972119 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell583_denomUpper
    linarith [hpThetaJensenCell583_product_upper]
  have hi : (1 / (5650256972119 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 100 : ℝ) - (583 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5650256972119 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5650256972119 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((583 / 3200 : ℝ) - Real.pi * Real.exp (73 / 100 : ℝ)) := by
    rw [show (583 / 3200 : ℝ) - Real.pi * Real.exp (73 / 100 : ℝ) =
      -(Real.pi * Real.exp (73 / 100 : ℝ) - (583 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (583 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (583 / 800 : ℝ)) := by
    have h := hpThetaJensenCell583_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5650256972119 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell583_endpointUpper :
    hpThetaJensenKernelEndpointUpper (583 / 1600 : ℝ) (73 / 200 : ℝ) ≤ (4684298633 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 100 : ℝ)) (32595293559501127 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell583_product_upper
  have hD : (1400666730181 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (583 / 800 : ℝ) - (73 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell583_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell583_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (583 / 800 : ℝ) - (73 / 400 : ℝ)) ≤
      (1 / (1400666730181 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1400666730181 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 400 : ℝ) - Real.pi * Real.exp (583 / 800 : ℝ)) ≤
      (2 / (1400666730181 / 2500000000 : ℝ) : ℝ) := by
    rw [show (73 / 400 : ℝ) - Real.pi * Real.exp (583 / 800 : ℝ) =
      -(Real.pi * Real.exp (583 / 800 : ℝ) - (73 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32595293559501127 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (32595293559501127 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell583_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (583 / 1600 : ℝ) (73 / 200 : ℝ)) :
    (923869273 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4684298633 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell583_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell583_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell584_leftExp :
    (5187701519 / 2500000000 : ℝ) ≤ Real.exp (73 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 100 : ℝ) (1023074695057 / 1000000000000 : ℝ)
    (5187701519 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell584_rightExp :
    Real.exp (117 / 160 : ℝ) ≤ (20776760803 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (117 / 160 : ℝ) (1023114659693 / 1000000000000 : ℝ)
    (20776760803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell584_denomUpper :
    Real.exp (63447126301379179 / 10000000000000000 : ℝ) ≤ (1138947433251 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63447126301379179 / 10000000000000000 : ℝ)
    (1219294325523 / 1000000000000 : ℝ) (1138947433251 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell584_denomLower :
    (1129342988769 / 2000000000 : ℝ) ≤ Real.exp (1980076292559781 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1980076292559781 / 312500000000000 : ℝ) (1218971693633 /
    1000000000000 : ℝ) (1129342988769 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell584_product_lower :
    (2037205198809781 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell584_leftExp
    (by norm_num : (0 : ℝ) ≤ (5187701519 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell584_product_upper :
    Real.pi * Real.exp (117 / 160 : ℝ) ≤ (65272126301379179 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell584_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell584_endpointLower :
    (1149114121 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 200 : ℝ) (117 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2037205198809781 / 312500000000000 : ℝ) (Real.pi * Real.exp (73 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell584_product_lower
  have hD : Real.exp (Real.pi * Real.exp (117 / 160 : ℝ) - (73 / 400 : ℝ)) ≤
      (1138947433251 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell584_denomUpper
    linarith [hpThetaJensenCell584_product_upper]
  have hi : (1 / (1138947433251 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (117 / 160 : ℝ) - (73 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1138947433251 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1138947433251 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 400 : ℝ) - Real.pi * Real.exp (117 / 160 : ℝ)) := by
    rw [show (73 / 400 : ℝ) - Real.pi * Real.exp (117 / 160 : ℝ) =
      -(Real.pi * Real.exp (117 / 160 : ℝ) - (73 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 100 : ℝ)) := by
    have h := hpThetaJensenCell584_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1138947433251 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell584_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 200 : ℝ) (117 / 320 : ℝ) ≤ (116528289 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (117 / 160 : ℝ)) (65272126301379179 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (117 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell584_product_upper
  have hD : (1129342988769 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 100 : ℝ) - (117 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell584_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell584_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 100 : ℝ) - (117 / 640 : ℝ)) ≤
      (1 / (1129342988769 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1129342988769 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((117 / 640 : ℝ) - Real.pi * Real.exp (73 / 100 : ℝ)) ≤
      (2 / (1129342988769 / 2000000000 : ℝ) : ℝ) := by
    rw [show (117 / 640 : ℝ) - Real.pi * Real.exp (73 / 100 : ℝ) =
      -(Real.pi * Real.exp (73 / 100 : ℝ) - (117 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (65272126301379179 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (65272126301379179 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell584_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 200 : ℝ) (117 / 320 : ℝ)) :
    (1149114121 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (116528289 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell584_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell584_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell585_leftExp :
    (10388380401 / 5000000000 : ℝ) ≤ Real.exp (117 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (117 / 160 : ℝ) (255778664923 / 250000000000 : ℝ)
    (10388380401 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell585_rightExp :
    Real.exp (293 / 400 : ℝ) ≤ (20802747993 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (293 / 400 : ℝ) (102315462589 / 100000000000 : ℝ)
    (20802747993 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell585_denomUpper :
    Real.exp (63525642475572849 / 10000000000000000 : ℝ) ≤ (5739626058341 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63525642475572849 / 10000000000000000 : ℝ) (304898382999
    / 250000000000 : ℝ) (5739626058341 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell585_denomLower :
    (1422791810289 / 2500000000 : ℝ) ≤ Real.exp (3965053470092299 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3965053470092299 / 625000000000000 : ℝ) (304817608059 /
    250000000000 : ℝ) (1422791810289 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell585_product_lower :
    (4079506595092299 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (117 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell585_leftExp
    (by norm_num : (0 : ℝ) ≤ (10388380401 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell585_product_upper :
    Real.pi * Real.exp (293 / 400 : ℝ) ≤ (65353767475572849 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell585_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell585_endpointLower :
    (2286815303 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (117 / 320 : ℝ) (293 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4079506595092299 / 625000000000000 : ℝ) (Real.pi * Real.exp (117 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell585_product_lower
  have hD : Real.exp (Real.pi * Real.exp (293 / 400 : ℝ) - (117 / 640 : ℝ)) ≤
      (5739626058341 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell585_denomUpper
    linarith [hpThetaJensenCell585_product_upper]
  have hi : (1 / (5739626058341 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (293 / 400 : ℝ) - (117 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5739626058341 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5739626058341 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((117 / 640 : ℝ) - Real.pi * Real.exp (293 / 400 : ℝ)) := by
    rw [show (117 / 640 : ℝ) - Real.pi * Real.exp (293 / 400 : ℝ) =
      -(Real.pi * Real.exp (293 / 400 : ℝ) - (117 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (117 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (117 / 160 : ℝ)) := by
    have h := hpThetaJensenCell585_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5739626058341 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell585_endpointUpper :
    hpThetaJensenKernelEndpointUpper (117 / 320 : ℝ) (293 / 800 : ℝ) ≤ (4638029013 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (293 / 400 : ℝ)) (65353767475572849 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (293 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell585_product_upper
  have hD : (1422791810289 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (117 / 160 : ℝ) - (293 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell585_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell585_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (117 / 160 : ℝ) - (293 / 1600 : ℝ)) ≤
      (1 / (1422791810289 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1422791810289 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((293 / 1600 : ℝ) - Real.pi * Real.exp (117 / 160 : ℝ)) ≤
      (2 / (1422791810289 / 2500000000 : ℝ) : ℝ) := by
    rw [show (293 / 1600 : ℝ) - Real.pi * Real.exp (117 / 160 : ℝ) =
      -(Real.pi * Real.exp (117 / 160 : ℝ) - (293 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (65353767475572849 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (65353767475572849 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell585_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (117 / 320 : ℝ) (293 / 800 : ℝ)) :
    (2286815303 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4638029013 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell585_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell585_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell586_leftExp :
    (20802747991 / 10000000000 : ℝ) ≤ Real.exp (293 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (293 / 400 : ℝ) (1023154625889 / 1000000000000 : ℝ)
    (20802747991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell586_rightExp :
    Real.exp (587 / 800 : ℝ) ≤ (20828767687 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (587 / 800 : ℝ) (1023194593649 / 1000000000000 : ℝ)
    (20828767687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell586_denomUpper :
    Real.exp (63604260764105391 / 10000000000000000 : ℝ) ≤ (5784927860223 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63604260764105391 / 10000000000000000 : ℝ)
    (1219893201169 / 1000000000000 : ℝ) (5784927860223 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell586_denomLower :
    (5736027976559 / 10000000000 : ℝ) ≤ Real.exp (7939921458317709 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7939921458317709 / 1250000000000000 : ℝ) (243913926547 /
    200000000000 : ℝ) (5736027976559 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell586_product_lower :
    (8169218333317709 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (293 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell586_leftExp
    (by norm_num : (0 : ℝ) ≤ (20802747991 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell586_product_upper :
    Real.pi * Real.exp (587 / 800 : ℝ) ≤ (65435510764105391 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell586_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell586_endpointLower :
    (2275434427 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (293 / 800 : ℝ) (587 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8169218333317709 / 1250000000000000 : ℝ) (Real.pi * Real.exp (293 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell586_product_lower
  have hD : Real.exp (Real.pi * Real.exp (587 / 800 : ℝ) - (293 / 1600 : ℝ)) ≤
      (5784927860223 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell586_denomUpper
    linarith [hpThetaJensenCell586_product_upper]
  have hi : (1 / (5784927860223 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (587 / 800 : ℝ) - (293 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5784927860223 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5784927860223 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((293 / 1600 : ℝ) - Real.pi * Real.exp (587 / 800 : ℝ)) := by
    rw [show (293 / 1600 : ℝ) - Real.pi * Real.exp (587 / 800 : ℝ) =
      -(Real.pi * Real.exp (587 / 800 : ℝ) - (293 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (293 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (293 / 400 : ℝ)) := by
    have h := hpThetaJensenCell586_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5784927860223 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell586_endpointUpper :
    hpThetaJensenKernelEndpointUpper (293 / 800 : ℝ) (587 / 1600 : ℝ) ≤ (2307495559 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (587 / 800 : ℝ)) (65435510764105391 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (587 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell586_product_upper
  have hD : (5736027976559 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (293 / 400 : ℝ) - (587 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell586_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell586_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (293 / 400 : ℝ) - (587 / 3200 : ℝ)) ≤
      (1 / (5736027976559 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5736027976559 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((587 / 3200 : ℝ) - Real.pi * Real.exp (293 / 400 : ℝ)) ≤
      (2 / (5736027976559 / 10000000000 : ℝ) : ℝ) := by
    rw [show (587 / 3200 : ℝ) - Real.pi * Real.exp (293 / 400 : ℝ) =
      -(Real.pi * Real.exp (293 / 400 : ℝ) - (587 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (65435510764105391 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (65435510764105391 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell586_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (293 / 800 : ℝ) (587 / 1600 : ℝ)) :
    (2275434427 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2307495559 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell586_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell586_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell587_leftExp :
    (10414383843 / 5000000000 : ℝ) ≤ Real.exp (587 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (587 / 800 : ℝ) (63949662103 / 62500000000 : ℝ)
    (10414383843 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell587_rightExp :
    Real.exp (147 / 200 : ℝ) ≤ (10427409963 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (147 / 200 : ℝ) (127904320371 / 125000000000 : ℝ)
    (10427409963 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell587_denomUpper :
    Real.exp (31841490647891059 / 5000000000000000 : ℝ) ≤ (5830646835007 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31841490647891059 / 5000000000000000 : ℝ) (1220193333839
    / 1000000000000 : ℝ) (5830646835007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell587_denomLower :
    (5781301366309 / 10000000000 : ℝ) ≤ Real.exp (3974874370762257 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3974874370762257 / 625000000000000 : ℝ) (1219869295949 /
    1000000000000 : ℝ) (5781301366309 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell587_product_lower :
    (4089718120762257 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (587 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell587_leftExp
    (by norm_num : (0 : ℝ) ≤ (10414383843 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell587_product_upper :
    Real.pi * Real.exp (147 / 200 : ℝ) ≤ (32758678147891059 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell587_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell587_endpointLower :
    (4528171349 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (587 / 1600 : ℝ) (147 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4089718120762257 / 625000000000000 : ℝ) (Real.pi * Real.exp (587 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell587_product_lower
  have hD : Real.exp (Real.pi * Real.exp (147 / 200 : ℝ) - (587 / 3200 : ℝ)) ≤
      (5830646835007 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell587_denomUpper
    linarith [hpThetaJensenCell587_product_upper]
  have hi : (1 / (5830646835007 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (147 / 200 : ℝ) - (587 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5830646835007 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5830646835007 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((587 / 3200 : ℝ) - Real.pi * Real.exp (147 / 200 : ℝ)) := by
    rw [show (587 / 3200 : ℝ) - Real.pi * Real.exp (147 / 200 : ℝ) =
      -(Real.pi * Real.exp (147 / 200 : ℝ) - (587 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (587 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (587 / 800 : ℝ)) := by
    have h := hpThetaJensenCell587_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5830646835007 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell587_endpointUpper :
    hpThetaJensenKernelEndpointUpper (587 / 1600 : ℝ) (147 / 400 : ℝ) ≤ (4592017993 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (147 / 200 : ℝ)) (32758678147891059 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (147 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell587_product_upper
  have hD : (5781301366309 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (587 / 800 : ℝ) - (147 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell587_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell587_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (587 / 800 : ℝ) - (147 / 800 : ℝ)) ≤
      (1 / (5781301366309 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5781301366309 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((147 / 800 : ℝ) - Real.pi * Real.exp (587 / 800 : ℝ)) ≤
      (2 / (5781301366309 / 10000000000 : ℝ) : ℝ) := by
    rw [show (147 / 800 : ℝ) - Real.pi * Real.exp (587 / 800 : ℝ) =
      -(Real.pi * Real.exp (587 / 800 : ℝ) - (147 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32758678147891059 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (32758678147891059 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell587_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (587 / 1600 : ℝ) (147 / 400 : ℝ)) :
    (4528171349 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4592017993 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell587_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell587_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell588_leftExp :
    (5213704981 / 2500000000 : ℝ) ≤ Real.exp (147 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (147 / 200 : ℝ) (1023234562967 / 1000000000000 : ℝ)
    (5213704981 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell588_rightExp :
    Real.exp (589 / 800 : ℝ) ≤ (20880904751 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (589 / 800 : ℝ) (1023274533849 / 1000000000000 : ℝ)
    (20880904751 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell588_denomUpper :
    Real.exp (63761804199408343 / 10000000000000000 : ℝ) ≤ (5876787293621 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63761804199408343 / 10000000000000000 : ℝ)
    (1220493930801 / 1000000000000 : ℝ) (5876787293621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell588_denomLower :
    (5826991663279 / 10000000000 : ℝ) ≤ Real.exp (1989897201083719 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1989897201083719 / 312500000000000 : ℝ) (9761355381 /
    8000000000 : ℝ) (5826991663279 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell588_product_lower :
    (2047416732333719 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (147 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell588_leftExp
    (by norm_num : (0 : ℝ) ≤ (5213704981 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell588_product_upper :
    Real.pi * Real.exp (589 / 800 : ℝ) ≤ (65599304199408343 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell588_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell588_endpointLower :
    (4505538207 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (147 / 400 : ℝ) (589 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2047416732333719 / 312500000000000 : ℝ) (Real.pi * Real.exp (147 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell588_product_lower
  have hD : Real.exp (Real.pi * Real.exp (589 / 800 : ℝ) - (147 / 800 : ℝ)) ≤
      (5876787293621 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell588_denomUpper
    linarith [hpThetaJensenCell588_product_upper]
  have hi : (1 / (5876787293621 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (589 / 800 : ℝ) - (147 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5876787293621 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5876787293621 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((147 / 800 : ℝ) - Real.pi * Real.exp (589 / 800 : ℝ)) := by
    rw [show (147 / 800 : ℝ) - Real.pi * Real.exp (589 / 800 : ℝ) =
      -(Real.pi * Real.exp (589 / 800 : ℝ) - (147 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (147 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (147 / 200 : ℝ)) := by
    have h := hpThetaJensenCell588_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5876787293621 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell588_endpointUpper :
    hpThetaJensenKernelEndpointUpper (147 / 400 : ℝ) (589 / 1600 : ℝ) ≤ (913821953 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (589 / 800 : ℝ)) (65599304199408343 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (589 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell588_product_upper
  have hD : (5826991663279 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (147 / 200 : ℝ) - (589 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell588_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell588_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (147 / 200 : ℝ) - (589 / 3200 : ℝ)) ≤
      (1 / (5826991663279 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5826991663279 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((589 / 3200 : ℝ) - Real.pi * Real.exp (147 / 200 : ℝ)) ≤
      (2 / (5826991663279 / 10000000000 : ℝ) : ℝ) := by
    rw [show (589 / 3200 : ℝ) - Real.pi * Real.exp (147 / 200 : ℝ) =
      -(Real.pi * Real.exp (147 / 200 : ℝ) - (589 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (65599304199408343 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (65599304199408343 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell588_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (147 / 400 : ℝ) (589 / 1600 : ℝ)) :
    (4505538207 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (913821953 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell588_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell588_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell589_leftExp :
    (20880904749 / 10000000000 : ℝ) ≤ Real.exp (589 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (589 / 800 : ℝ) (127909316731 / 125000000000 : ℝ)
    (20880904749 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell589_rightExp :
    Real.exp (59 / 80 : ℝ) ≤ (20907022201 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 80 : ℝ) (1023314506291 / 1000000000000 : ℝ)
    (20907022201 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell589_denomUpper :
    Real.exp (63840729597506193 / 10000000000000000 : ℝ) ≤ (23693414371 / 40000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63840729597506193 / 10000000000000000 : ℝ)
    (1220794992831 / 1000000000000 : ℝ) (23693414371 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell589_denomLower :
    (5873103181763 / 10000000000 : ℝ) ≤ Real.exp (7969441664027551 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7969441664027551 / 1250000000000000 : ℝ) (610235006799 /
    500000000000 : ℝ) (5873103181763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell589_product_lower :
    (8199910414027551 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (589 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell589_leftExp
    (by norm_num : (0 : ℝ) ≤ (20880904749 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell589_product_upper :
    Real.pi * Real.exp (59 / 80 : ℝ) ≤ (65681354597506193 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell589_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell589_endpointLower :
    (2241484773 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (589 / 1600 : ℝ) (59 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8199910414027551 / 1250000000000000 : ℝ) (Real.pi * Real.exp (589 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell589_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 80 : ℝ) - (589 / 3200 : ℝ)) ≤
      (23693414371 / 40000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell589_denomUpper
    linarith [hpThetaJensenCell589_product_upper]
  have hi : (1 / (23693414371 / 40000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 80 : ℝ) - (589 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23693414371 / 40000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23693414371 / 40000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((589 / 3200 : ℝ) - Real.pi * Real.exp (59 / 80 : ℝ)) := by
    rw [show (589 / 3200 : ℝ) - Real.pi * Real.exp (59 / 80 : ℝ) =
      -(Real.pi * Real.exp (59 / 80 : ℝ) - (589 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (589 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (589 / 800 : ℝ)) := by
    have h := hpThetaJensenCell589_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23693414371 / 40000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell589_endpointUpper :
    hpThetaJensenKernelEndpointUpper (589 / 1600 : ℝ) (59 / 160 : ℝ) ≤ (2273133273 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 80 : ℝ)) (65681354597506193 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell589_product_upper
  have hD : (5873103181763 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (589 / 800 : ℝ) - (59 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell589_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell589_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (589 / 800 : ℝ) - (59 / 320 : ℝ)) ≤
      (1 / (5873103181763 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5873103181763 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 320 : ℝ) - Real.pi * Real.exp (589 / 800 : ℝ)) ≤
      (2 / (5873103181763 / 10000000000 : ℝ) : ℝ) := by
    rw [show (59 / 320 : ℝ) - Real.pi * Real.exp (589 / 800 : ℝ) =
      -(Real.pi * Real.exp (589 / 800 : ℝ) - (59 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (65681354597506193 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (65681354597506193 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell589_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (589 / 1600 : ℝ) (59 / 160 : ℝ)) :
    (2241484773 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2273133273 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell589_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell589_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell590_leftExp :
    (104535111 / 50000000 : ℝ) ≤ Real.exp (59 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 80 : ℝ) (102331450629 / 100000000000 : ℝ)
    (104535111 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell590_rightExp :
    Real.exp (591 / 800 : ℝ) ≤ (130832327 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (591 / 800 : ℝ) (204670896059 / 200000000000 : ℝ)
    (130832327 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell590_denomUpper :
    Real.exp (399498485176911 / 62500000000000 : ℝ) ≤ (5970350147517 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (399498485176911 / 62500000000000 : ℝ) (305274130191 /
    250000000000 : ℝ) (5970350147517 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell590_denomLower :
    (59196402753 / 100000000 : ℝ) ≤ Real.exp (39896536679589 / 6250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39896536679589 / 6250000000000 : ℝ) (1220771069641 /
    1000000000000 : ℝ) (59196402753 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell590_product_lower :
    (41050833554589 / 6250000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell590_leftExp
    (by norm_num : (0 : ℝ) ≤ (104535111 / 50000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell590_product_upper :
    Real.pi * Real.exp (591 / 800 : ℝ) ≤ (411021922676911 / 62500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell590_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell590_endpointLower :
    (1115116369 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 160 : ℝ) (591 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (41050833554589 / 6250000000000 : ℝ) (Real.pi * Real.exp (59 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell590_product_lower
  have hD : Real.exp (Real.pi * Real.exp (591 / 800 : ℝ) - (59 / 320 : ℝ)) ≤
      (5970350147517 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell590_denomUpper
    linarith [hpThetaJensenCell590_product_upper]
  have hi : (1 / (5970350147517 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (591 / 800 : ℝ) - (59 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5970350147517 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5970350147517 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 320 : ℝ) - Real.pi * Real.exp (591 / 800 : ℝ)) := by
    rw [show (59 / 320 : ℝ) - Real.pi * Real.exp (591 / 800 : ℝ) =
      -(Real.pi * Real.exp (591 / 800 : ℝ) - (59 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 80 : ℝ)) := by
    have h := hpThetaJensenCell590_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5970350147517 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell590_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 160 : ℝ) (591 / 1600 : ℝ) ≤ (904697691 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (591 / 800 : ℝ)) (411021922676911 / 62500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (591 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell590_product_upper
  have hD : (59196402753 / 100000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 80 : ℝ) - (591 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell590_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell590_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 80 : ℝ) - (591 / 3200 : ℝ)) ≤
      (1 / (59196402753 / 100000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (59196402753 / 100000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((591 / 3200 : ℝ) - Real.pi * Real.exp (59 / 80 : ℝ)) ≤
      (2 / (59196402753 / 100000000 : ℝ) : ℝ) := by
    rw [show (591 / 3200 : ℝ) - Real.pi * Real.exp (59 / 80 : ℝ) =
      -(Real.pi * Real.exp (59 / 80 : ℝ) - (591 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (411021922676911 / 62500000000000 : ℝ) ^ 2 - 6 *
      (411021922676911 / 62500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell590_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 160 : ℝ) (591 / 1600 : ℝ)) :
    (1115116369 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (904697691 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell590_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell590_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell591_leftExp :
    (10466586159 / 5000000000 : ℝ) ≤ Real.exp (591 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (591 / 800 : ℝ) (511677240147 / 500000000000 : ℝ)
    (10466586159 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell591_rightExp :
    Real.exp (37 / 50 : ℝ) ≤ (10479677573 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 50 : ℝ) (51169722793 / 50000000000 : ℝ)
    (10479677573 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell591_denomUpper :
    Real.exp (31999444205593789 / 5000000000000000 : ℝ) ≤ (1203556282357 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31999444205593789 / 5000000000000000 : ℝ) (1221398515363
    / 1000000000000 : ℝ) (1203556282357 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell591_denomLower :
    (2983303675249 / 5000000000 : ℝ) ≤ Real.exp (3994592918053141 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3994592918053141 / 625000000000000 : ℝ) (19079259243 /
    15625000000 : ℝ) (2983303675249 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell591_product_lower :
    (4110217918053141 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (591 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell591_leftExp
    (by norm_num : (0 : ℝ) ≤ (10466586159 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell591_product_upper :
    Real.pi * Real.exp (37 / 50 : ℝ) ≤ (32922881705593789 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell591_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell591_endpointLower :
    (4438026113 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (591 / 1600 : ℝ) (37 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4110217918053141 / 625000000000000 : ℝ) (Real.pi * Real.exp (591 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell591_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 50 : ℝ) - (591 / 3200 : ℝ)) ≤
      (1203556282357 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell591_denomUpper
    linarith [hpThetaJensenCell591_product_upper]
  have hi : (1 / (1203556282357 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 50 : ℝ) - (591 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1203556282357 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1203556282357 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((591 / 3200 : ℝ) - Real.pi * Real.exp (37 / 50 : ℝ)) := by
    rw [show (591 / 3200 : ℝ) - Real.pi * Real.exp (37 / 50 : ℝ) =
      -(Real.pi * Real.exp (37 / 50 : ℝ) - (591 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (591 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (591 / 800 : ℝ)) := by
    have h := hpThetaJensenCell591_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1203556282357 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell591_endpointUpper :
    hpThetaJensenKernelEndpointUpper (591 / 1600 : ℝ) (37 / 100 : ℝ) ≤ (562596951 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 50 : ℝ)) (32922881705593789 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell591_product_upper
  have hD : (2983303675249 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (591 / 800 : ℝ) - (37 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell591_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell591_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (591 / 800 : ℝ) - (37 / 200 : ℝ)) ≤
      (1 / (2983303675249 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2983303675249 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 200 : ℝ) - Real.pi * Real.exp (591 / 800 : ℝ)) ≤
      (2 / (2983303675249 / 5000000000 : ℝ) : ℝ) := by
    rw [show (37 / 200 : ℝ) - Real.pi * Real.exp (591 / 800 : ℝ) =
      -(Real.pi * Real.exp (591 / 800 : ℝ) - (37 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32922881705593789 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (32922881705593789 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell591_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (591 / 1600 : ℝ) (37 / 100 : ℝ)) :
    (4438026113 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (562596951 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell591_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell591_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell592_leftExp :
    (2619919393 / 1250000000 : ℝ) ≤ Real.exp (37 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 50 : ℝ) (1023394455859 / 1000000000000 : ℝ)
    (2619919393 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell592_rightExp :
    Real.exp (593 / 800 : ℝ) ≤ (20985570721 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (593 / 800 : ℝ) (511717216493 / 500000000000 : ℝ)
    (20985570721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell592_denomUpper :
    Real.exp (64078122078098553 / 10000000000000000 : ℝ) ≤ (606565189787 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (64078122078098553 / 10000000000000000 : ℝ) (610850488721
    / 500000000000 : ℝ) (606565189787 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell592_denomLower :
    (1503502216159 / 2500000000 : ℝ) ≤ Real.exp (999884647586707 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (999884647586707 / 156250000000000 : ℝ) (610687290067 /
    500000000000 : ℝ) (1503502216159 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell592_product_lower :
    (1028839725711707 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell592_leftExp
    (by norm_num : (0 : ℝ) ≤ (2619919393 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell592_product_upper :
    Real.pi * Real.exp (593 / 800 : ℝ) ≤ (65928122078098553 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell592_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell592_endpointLower :
    (1103912891 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 100 : ℝ) (593 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1028839725711707 / 156250000000000 : ℝ) (Real.pi * Real.exp (37 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell592_product_lower
  have hD : Real.exp (Real.pi * Real.exp (593 / 800 : ℝ) - (37 / 200 : ℝ)) ≤
      (606565189787 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell592_denomUpper
    linarith [hpThetaJensenCell592_product_upper]
  have hi : (1 / (606565189787 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (593 / 800 : ℝ) - (37 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (606565189787 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (606565189787 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 200 : ℝ) - Real.pi * Real.exp (593 / 800 : ℝ)) := by
    rw [show (37 / 200 : ℝ) - Real.pi * Real.exp (593 / 800 : ℝ) =
      -(Real.pi * Real.exp (593 / 800 : ℝ) - (37 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 50 : ℝ)) := by
    have h := hpThetaJensenCell592_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (606565189787 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell592_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 100 : ℝ) (593 / 1600 : ℝ) ≤ (2239064057 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (593 / 800 : ℝ)) (65928122078098553 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (593 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell592_product_upper
  have hD : (1503502216159 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 50 : ℝ) - (593 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell592_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell592_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 50 : ℝ) - (593 / 3200 : ℝ)) ≤
      (1 / (1503502216159 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1503502216159 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((593 / 3200 : ℝ) - Real.pi * Real.exp (37 / 50 : ℝ)) ≤
      (2 / (1503502216159 / 2500000000 : ℝ) : ℝ) := by
    rw [show (593 / 3200 : ℝ) - Real.pi * Real.exp (37 / 50 : ℝ) =
      -(Real.pi * Real.exp (37 / 50 : ℝ) - (593 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (65928122078098553 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (65928122078098553 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell592_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 100 : ℝ) (593 / 1600 : ℝ)) :
    (1103912891 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2239064057 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell592_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell592_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell593_leftExp :
    (20985570719 / 10000000000 : ℝ) ≤ Real.exp (593 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (593 / 800 : ℝ) (204686886597 / 200000000000 : ℝ)
    (20985570719 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell593_rightExp :
    Real.exp (297 / 400 : ℝ) ≤ (10505909543 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (297 / 400 : ℝ) (40938976467 / 40000000000 : ℝ)
    (10505909543 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell593_denomUpper :
    Real.exp (32078729378921999 / 5000000000000000 : ℝ) ≤ (3056983083611 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32078729378921999 / 5000000000000000 : ℝ) (611001953901
    / 500000000000 : ℝ) (3056983083611 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell593_denomLower :
    (6061849324711 / 10000000000 : ℝ) ≤ Real.exp (8008981385780581 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8008981385780581 / 1250000000000000 : ℝ) (244335407237 /
    200000000000 : ℝ) (6061849324711 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell593_product_lower :
    (8241012635780581 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (593 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell593_leftExp
    (by norm_num : (0 : ℝ) ≤ (20985570719 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell593_product_upper :
    Real.pi * Real.exp (297 / 400 : ℝ) ≤ (33005291878921999 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell593_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell593_endpointLower :
    (2196670969 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (593 / 1600 : ℝ) (297 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8241012635780581 / 1250000000000000 : ℝ) (Real.pi * Real.exp (593 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell593_product_lower
  have hD : Real.exp (Real.pi * Real.exp (297 / 400 : ℝ) - (593 / 3200 : ℝ)) ≤
      (3056983083611 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell593_denomUpper
    linarith [hpThetaJensenCell593_product_upper]
  have hi : (1 / (3056983083611 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (297 / 400 : ℝ) - (593 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3056983083611 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3056983083611 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((593 / 3200 : ℝ) - Real.pi * Real.exp (297 / 400 : ℝ)) := by
    rw [show (593 / 3200 : ℝ) - Real.pi * Real.exp (297 / 400 : ℝ) =
      -(Real.pi * Real.exp (297 / 400 : ℝ) - (593 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (593 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (593 / 800 : ℝ)) := by
    have h := hpThetaJensenCell593_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3056983083611 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell593_endpointUpper :
    hpThetaJensenKernelEndpointUpper (593 / 1600 : ℝ) (297 / 800 : ℝ) ≤ (2227773043 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (297 / 400 : ℝ)) (33005291878921999 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (297 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell593_product_upper
  have hD : (6061849324711 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (593 / 800 : ℝ) - (297 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell593_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell593_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (593 / 800 : ℝ) - (297 / 1600 : ℝ)) ≤
      (1 / (6061849324711 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6061849324711 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((297 / 1600 : ℝ) - Real.pi * Real.exp (593 / 800 : ℝ)) ≤
      (2 / (6061849324711 / 10000000000 : ℝ) : ℝ) := by
    rw [show (297 / 1600 : ℝ) - Real.pi * Real.exp (593 / 800 : ℝ) =
      -(Real.pi * Real.exp (593 / 800 : ℝ) - (297 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33005291878921999 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (33005291878921999 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell593_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (593 / 1600 : ℝ) (297 / 800 : ℝ)) :
    (2196670969 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2227773043 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell593_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell593_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell594_leftExp :
    (4202363817 / 2000000000 : ℝ) ≤ Real.exp (297 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (297 / 400 : ℝ) (511737205837 / 500000000000 : ℝ)
    (4202363817 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell594_rightExp :
    Real.exp (119 / 160 : ℝ) ≤ (10519050141 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (119 / 160 : ℝ) (40940575677 / 40000000000 : ℝ)
    (10519050141 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell594_denomUpper :
    Real.exp (32118449289614613 / 5000000000000000 : ℝ) ≤ (3081364416857 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32118449289614613 / 5000000000000000 : ℝ) (76394206703 /
    62500000000 : ℝ) (3081364416857 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell594_denomLower :
    (1527533322927 / 2500000000 : ℝ) ≤ Real.exp (1603779693572083 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1603779693572083 / 250000000000000 : ℝ) (1221979960521 /
    1000000000000 : ℝ) (1527533322927 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell594_product_lower :
    (1650264068572083 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (297 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell594_leftExp
    (by norm_num : (0 : ℝ) ≤ (4202363817 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell594_product_upper :
    Real.pi * Real.exp (119 / 160 : ℝ) ≤ (33046574289614613 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell594_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell594_endpointLower :
    (4371097341 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (297 / 800 : ℝ) (119 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1650264068572083 / 250000000000000 : ℝ) (Real.pi * Real.exp (297 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell594_product_lower
  have hD : Real.exp (Real.pi * Real.exp (119 / 160 : ℝ) - (297 / 1600 : ℝ)) ≤
      (3081364416857 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell594_denomUpper
    linarith [hpThetaJensenCell594_product_upper]
  have hi : (1 / (3081364416857 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (119 / 160 : ℝ) - (297 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3081364416857 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3081364416857 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((297 / 1600 : ℝ) - Real.pi * Real.exp (119 / 160 : ℝ)) := by
    rw [show (297 / 1600 : ℝ) - Real.pi * Real.exp (119 / 160 : ℝ) =
      -(Real.pi * Real.exp (119 / 160 : ℝ) - (297 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (297 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (297 / 400 : ℝ)) := by
    have h := hpThetaJensenCell594_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3081364416857 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell594_endpointUpper :
    hpThetaJensenKernelEndpointUpper (297 / 800 : ℝ) (119 / 320 : ℝ) ≤ (443302963 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (119 / 160 : ℝ)) (33046574289614613 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (119 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell594_product_upper
  have hD : (1527533322927 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (297 / 400 : ℝ) - (119 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell594_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell594_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (297 / 400 : ℝ) - (119 / 640 : ℝ)) ≤
      (1 / (1527533322927 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1527533322927 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((119 / 640 : ℝ) - Real.pi * Real.exp (297 / 400 : ℝ)) ≤
      (2 / (1527533322927 / 2500000000 : ℝ) : ℝ) := by
    rw [show (119 / 640 : ℝ) - Real.pi * Real.exp (297 / 400 : ℝ) =
      -(Real.pi * Real.exp (297 / 400 : ℝ) - (119 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33046574289614613 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (33046574289614613 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell594_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (297 / 800 : ℝ) (119 / 320 : ℝ)) :
    (4371097341 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (443302963 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell594_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell594_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell595_leftExp :
    (21038100281 / 10000000000 : ℝ) ≤ Real.exp (119 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (119 / 160 : ℝ) (255878597981 / 250000000000 : ℝ)
    (21038100281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell595_rightExp :
    Real.exp (149 / 200 : ℝ) ≤ (21064414351 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (149 / 200 : ℝ) (1023554373737 / 1000000000000 : ℝ)
    (21064414351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell595_denomUpper :
    Real.exp (64316441674201143 / 10000000000000000 : ℝ) ≤ (776493070659 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (64316441674201143 / 10000000000000000 : ℝ) (244522235319
    / 200000000000 : ℝ) (776493070659 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell595_denomLower :
    (6158865372461 / 10000000000 : ℝ) ≤ Real.exp (8028828442248419 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8028828442248419 / 1250000000000000 : ℝ) (1222283353921
    / 1000000000000 : ℝ) (6158865372461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell595_product_lower :
    (8261640942248419 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (119 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell595_leftExp
    (by norm_num : (0 : ℝ) ≤ (21038100281 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell595_product_upper :
    Real.pi * Real.exp (149 / 200 : ℝ) ≤ (66175816674201143 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell595_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell595_endpointLower :
    (2174458937 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (119 / 320 : ℝ) (149 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8261640942248419 / 1250000000000000 : ℝ) (Real.pi * Real.exp (119 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell595_product_lower
  have hD : Real.exp (Real.pi * Real.exp (149 / 200 : ℝ) - (119 / 640 : ℝ)) ≤
      (776493070659 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell595_denomUpper
    linarith [hpThetaJensenCell595_product_upper]
  have hi : (1 / (776493070659 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (149 / 200 : ℝ) - (119 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (776493070659 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (776493070659 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((119 / 640 : ℝ) - Real.pi * Real.exp (149 / 200 : ℝ)) := by
    rw [show (119 / 640 : ℝ) - Real.pi * Real.exp (149 / 200 : ℝ) =
      -(Real.pi * Real.exp (149 / 200 : ℝ) - (119 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (119 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (119 / 160 : ℝ)) := by
    have h := hpThetaJensenCell595_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (776493070659 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell595_endpointUpper :
    hpThetaJensenKernelEndpointUpper (119 / 320 : ℝ) (149 / 400 : ℝ) ≤ (882115771 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (149 / 200 : ℝ)) (66175816674201143 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (149 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell595_product_upper
  have hD : (6158865372461 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (119 / 160 : ℝ) - (149 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell595_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell595_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (119 / 160 : ℝ) - (149 / 800 : ℝ)) ≤
      (1 / (6158865372461 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6158865372461 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((149 / 800 : ℝ) - Real.pi * Real.exp (119 / 160 : ℝ)) ≤
      (2 / (6158865372461 / 10000000000 : ℝ) : ℝ) := by
    rw [show (149 / 800 : ℝ) - Real.pi * Real.exp (119 / 160 : ℝ) =
      -(Real.pi * Real.exp (119 / 160 : ℝ) - (149 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66175816674201143 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (66175816674201143 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell595_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (119 / 320 : ℝ) (149 / 400 : ℝ)) :
    (2174458937 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (882115771 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell595_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell595_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell596_leftExp :
    (21064414349 / 10000000000 : ℝ) ≤ Real.exp (149 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (149 / 200 : ℝ) (127944296717 / 125000000000 : ℝ)
    (21064414349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell596_rightExp :
    Real.exp (597 / 800 : ℝ) ≤ (5272690333 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (597 / 800 : ℝ) (102359435711 / 100000000000 : ℝ)
    (5272690333 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell596_denomUpper :
    Real.exp (16099022041320469 / 2500000000000000 : ℝ) ≤ (3130809038767 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16099022041320469 / 2500000000000000 : ℝ) (9783324133 /
    8000000000 : ℝ) (3130809038767 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell596_denomLower :
    (1241610046417 / 2000000000 : ℝ) ≤ Real.exp (8038771325437951 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8038771325437951 / 1250000000000000 : ℝ) (1222587217201
    / 1000000000000 : ℝ) (1241610046417 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell596_product_lower :
    (8271974450437951 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (149 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell596_leftExp
    (by norm_num : (0 : ℝ) ≤ (21064414349 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell596_product_upper :
    Real.pi * Real.exp (597 / 800 : ℝ) ≤ (16564647041320469 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell596_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell596_endpointLower :
    (1081700911 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (149 / 400 : ℝ) (597 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8271974450437951 / 1250000000000000 : ℝ) (Real.pi * Real.exp (149 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell596_product_lower
  have hD : Real.exp (Real.pi * Real.exp (597 / 800 : ℝ) - (149 / 800 : ℝ)) ≤
      (3130809038767 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell596_denomUpper
    linarith [hpThetaJensenCell596_product_upper]
  have hi : (1 / (3130809038767 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (597 / 800 : ℝ) - (149 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3130809038767 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3130809038767 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((149 / 800 : ℝ) - Real.pi * Real.exp (597 / 800 : ℝ)) := by
    rw [show (149 / 800 : ℝ) - Real.pi * Real.exp (597 / 800 : ℝ) =
      -(Real.pi * Real.exp (597 / 800 : ℝ) - (149 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (149 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (149 / 200 : ℝ)) := by
    have h := hpThetaJensenCell596_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3130809038767 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell596_endpointUpper :
    hpThetaJensenKernelEndpointUpper (149 / 400 : ℝ) (597 / 1600 : ℝ) ≤ (548524233 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (597 / 800 : ℝ)) (16564647041320469 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (597 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell596_product_upper
  have hD : (1241610046417 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (149 / 200 : ℝ) - (597 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell596_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell596_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (149 / 200 : ℝ) - (597 / 3200 : ℝ)) ≤
      (1 / (1241610046417 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1241610046417 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((597 / 3200 : ℝ) - Real.pi * Real.exp (149 / 200 : ℝ)) ≤
      (2 / (1241610046417 / 2000000000 : ℝ) : ℝ) := by
    rw [show (597 / 3200 : ℝ) - Real.pi * Real.exp (149 / 200 : ℝ) =
      -(Real.pi * Real.exp (149 / 200 : ℝ) - (597 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16564647041320469 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (16564647041320469 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell596_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (149 / 400 : ℝ) (597 / 1600 : ℝ)) :
    (1081700911 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (548524233 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell596_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell596_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell597_leftExp :
    (2109076133 / 1000000000 : ℝ) ≤ Real.exp (597 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (597 / 800 : ℝ) (1023594357109 / 1000000000000 : ℝ)
    (2109076133 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell597_rightExp :
    Real.exp (299 / 400 : ℝ) ≤ (5279285317 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (299 / 400 : ℝ) (511817171023 / 500000000000 : ℝ)
    (5279285317 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell597_denomUpper :
    Real.exp (16118959546889981 / 2500000000000000 : ℝ) ≤ (1262350829501 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16118959546889981 / 2500000000000000 : ℝ) (1223220328167
    / 1000000000000 : ℝ) (1262350829501 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell597_denomLower :
    (6257692586983 / 10000000000 : ℝ) ≤ Real.exp (804872713352967 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (804872713352967 / 125000000000000 : ℝ) (611445775583 /
    500000000000 : ℝ) (6257692586983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell597_product_lower :
    (828232088352967 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (597 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell597_leftExp
    (by norm_num : (0 : ℝ) ≤ (2109076133 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell597_product_upper :
    Real.pi * Real.exp (299 / 400 : ℝ) ≤ (16585365796889981 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell597_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell597_endpointLower :
    (4304754747 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (597 / 1600 : ℝ) (299 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (828232088352967 / 125000000000000 : ℝ) (Real.pi * Real.exp (597 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell597_product_lower
  have hD : Real.exp (Real.pi * Real.exp (299 / 400 : ℝ) - (597 / 3200 : ℝ)) ≤
      (1262350829501 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell597_denomUpper
    linarith [hpThetaJensenCell597_product_upper]
  have hi : (1 / (1262350829501 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (299 / 400 : ℝ) - (597 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1262350829501 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1262350829501 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((597 / 3200 : ℝ) - Real.pi * Real.exp (299 / 400 : ℝ)) := by
    rw [show (597 / 3200 : ℝ) - Real.pi * Real.exp (299 / 400 : ℝ) =
      -(Real.pi * Real.exp (299 / 400 : ℝ) - (597 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (597 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (597 / 800 : ℝ)) := by
    have h := hpThetaJensenCell597_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1262350829501 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell597_endpointUpper :
    hpThetaJensenKernelEndpointUpper (597 / 1600 : ℝ) (299 / 800 : ℝ) ≤ (4365874761 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (299 / 400 : ℝ)) (16585365796889981 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (299 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell597_product_upper
  have hD : (6257692586983 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (597 / 800 : ℝ) - (299 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell597_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell597_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (597 / 800 : ℝ) - (299 / 1600 : ℝ)) ≤
      (1 / (6257692586983 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6257692586983 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((299 / 1600 : ℝ) - Real.pi * Real.exp (597 / 800 : ℝ)) ≤
      (2 / (6257692586983 / 10000000000 : ℝ) : ℝ) := by
    rw [show (299 / 1600 : ℝ) - Real.pi * Real.exp (597 / 800 : ℝ) =
      -(Real.pi * Real.exp (597 / 800 : ℝ) - (299 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16585365796889981 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (16585365796889981 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell597_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (597 / 1600 : ℝ) (299 / 800 : ℝ)) :
    (4304754747 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4365874761 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell597_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell597_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell598_leftExp :
    (10558570633 / 5000000000 : ℝ) ≤ Real.exp (299 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (299 / 400 : ℝ) (204726868409 / 200000000000 : ℝ)
    (10558570633 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell598_rightExp :
    Real.exp (599 / 800 : ℝ) ≤ (21143554199 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (599 / 800 : ℝ) (1023674328543 / 1000000000000 : ℝ)
    (21143554199 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell598_denomUpper :
    Real.exp (64555691866699007 / 10000000000000000 : ℝ) ≤ (3181178800681 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (64555691866699007 / 10000000000000000 : ℝ) (611762806009
    / 500000000000 : ℝ) (3181178800681 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell598_denomLower :
    (6307797209391 / 10000000000 : ℝ) ≤ Real.exp (4029347941508467 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4029347941508467 / 625000000000000 : ℝ) (611598178317 /
    500000000000 : ℝ) (6307797209391 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell598_product_lower :
    (4146340129008467 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (299 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell598_leftExp
    (by norm_num : (0 : ℝ) ≤ (10558570633 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell598_product_upper :
    Real.pi * Real.exp (599 / 800 : ℝ) ≤ (66424441866699007 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell598_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell598_endpointLower :
    (4282771283 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (299 / 800 : ℝ) (599 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4146340129008467 / 625000000000000 : ℝ) (Real.pi * Real.exp (299 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell598_product_lower
  have hD : Real.exp (Real.pi * Real.exp (599 / 800 : ℝ) - (299 / 1600 : ℝ)) ≤
      (3181178800681 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell598_denomUpper
    linarith [hpThetaJensenCell598_product_upper]
  have hi : (1 / (3181178800681 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (599 / 800 : ℝ) - (299 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3181178800681 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3181178800681 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((299 / 1600 : ℝ) - Real.pi * Real.exp (599 / 800 : ℝ)) := by
    rw [show (299 / 1600 : ℝ) - Real.pi * Real.exp (599 / 800 : ℝ) =
      -(Real.pi * Real.exp (599 / 800 : ℝ) - (299 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (299 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (299 / 400 : ℝ)) := by
    have h := hpThetaJensenCell598_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3181178800681 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell598_endpointUpper :
    hpThetaJensenKernelEndpointUpper (299 / 800 : ℝ) (599 / 1600 : ℝ) ≤ (4343621643 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (599 / 800 : ℝ)) (66424441866699007 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (599 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell598_product_upper
  have hD : (6307797209391 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (299 / 400 : ℝ) - (599 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell598_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell598_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (299 / 400 : ℝ) - (599 / 3200 : ℝ)) ≤
      (1 / (6307797209391 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6307797209391 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((599 / 3200 : ℝ) - Real.pi * Real.exp (299 / 400 : ℝ)) ≤
      (2 / (6307797209391 / 10000000000 : ℝ) : ℝ) := by
    rw [show (599 / 3200 : ℝ) - Real.pi * Real.exp (299 / 400 : ℝ) =
      -(Real.pi * Real.exp (299 / 400 : ℝ) - (599 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66424441866699007 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (66424441866699007 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell598_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (299 / 800 : ℝ) (599 / 1600 : ℝ)) :
    (4282771283 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4343621643 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell598_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell598_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell599_leftExp :
    (21143554197 / 10000000000 : ℝ) ≤ Real.exp (599 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (599 / 800 : ℝ) (511837164271 / 500000000000 : ℝ)
    (21143554197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell599_rightExp :
    Real.exp (3 / 4 : ℝ) ≤ (21170000167 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 4 : ℝ) (1023714316603 / 1000000000000 : ℝ)
    (21170000167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell599_denomUpper :
    Real.exp (64635649334646031 / 10000000000000000 : ℝ) ≤ (3206716661903 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (64635649334646031 / 10000000000000000 : ℝ) (305957842249
    / 250000000000 : ℝ) (3206716661903 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell599_denomLower :
    (6358368922127 / 10000000000 : ℝ) ≤ Real.exp (8068677589607703 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8068677589607703 / 1250000000000000 : ℝ) (1529377043 /
    1250000000 : ℝ) (6358368922127 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell599_product_lower :
    (8303052589607703 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (599 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell599_leftExp
    (by norm_num : (0 : ℝ) ≤ (21143554197 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell599_product_upper :
    Real.pi * Real.exp (3 / 4 : ℝ) ≤ (66507524334646031 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell599_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell599_endpointLower :
    (1065213337 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (599 / 1600 : ℝ) (3 / 8 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8303052589607703 / 1250000000000000 : ℝ) (Real.pi * Real.exp (599 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell599_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 4 : ℝ) - (599 / 3200 : ℝ)) ≤
      (3206716661903 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell599_denomUpper
    linarith [hpThetaJensenCell599_product_upper]
  have hi : (1 / (3206716661903 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 4 : ℝ) - (599 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3206716661903 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3206716661903 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((599 / 3200 : ℝ) - Real.pi * Real.exp (3 / 4 : ℝ)) := by
    rw [show (599 / 3200 : ℝ) - Real.pi * Real.exp (3 / 4 : ℝ) =
      -(Real.pi * Real.exp (3 / 4 : ℝ) - (599 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (599 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (599 / 800 : ℝ)) := by
    have h := hpThetaJensenCell599_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3206716661903 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell599_endpointUpper :
    hpThetaJensenKernelEndpointUpper (599 / 1600 : ℝ) (3 / 8 : ℝ) ≤ (1080358653 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 4 : ℝ)) (66507524334646031 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 8 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell599_product_upper
  have hD : (6358368922127 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (599 / 800 : ℝ) - (3 / 16 : ℝ)) := by
    apply le_trans hpThetaJensenCell599_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell599_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (599 / 800 : ℝ) - (3 / 16 : ℝ)) ≤
      (1 / (6358368922127 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6358368922127 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 16 : ℝ) - Real.pi * Real.exp (599 / 800 : ℝ)) ≤
      (2 / (6358368922127 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 16 : ℝ) - Real.pi * Real.exp (599 / 800 : ℝ) =
      -(Real.pi * Real.exp (599 / 800 : ℝ) - (3 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66507524334646031 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (66507524334646031 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell599_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (599 / 1600 : ℝ) (3 / 8 : ℝ)) :
    (1065213337 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1080358653 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell599_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell599_endpointUpper

def hpThetaJensenCellsBatch029Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1172099699 / 2500000000 : ℝ)
  | 1 => (291582353 / 625000000 : ℝ)
  | 2 => (4642300129 / 10000000000 : ℝ)
  | 3 => (923869273 / 2000000000 : ℝ)
  | 4 => (1149114121 / 2500000000 : ℝ)
  | 5 => (2286815303 / 5000000000 : ℝ)
  | 6 => (2275434427 / 5000000000 : ℝ)
  | 7 => (4528171349 / 10000000000 : ℝ)
  | 8 => (4505538207 / 10000000000 : ℝ)
  | 9 => (2241484773 / 5000000000 : ℝ)
  | 10 => (1115116369 / 2500000000 : ℝ)
  | 11 => (4438026113 / 10000000000 : ℝ)
  | 12 => (1103912891 / 2500000000 : ℝ)
  | 13 => (2196670969 / 5000000000 : ℝ)
  | 14 => (4371097341 / 10000000000 : ℝ)
  | 15 => (2174458937 / 5000000000 : ℝ)
  | 16 => (1081700911 / 2500000000 : ℝ)
  | 17 => (4304754747 / 10000000000 : ℝ)
  | 18 => (4282771283 / 10000000000 : ℝ)
  | 19 => (1065213337 / 2500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch029Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (950837147 / 2000000000 : ℝ)
  | 1 => (94616517 / 200000000 : ℝ)
  | 2 => (2353765053 / 5000000000 : ℝ)
  | 3 => (4684298633 / 10000000000 : ℝ)
  | 4 => (116528289 / 250000000 : ℝ)
  | 5 => (4638029013 / 10000000000 : ℝ)
  | 6 => (2307495559 / 5000000000 : ℝ)
  | 7 => (4592017993 / 10000000000 : ℝ)
  | 8 => (913821953 / 2000000000 : ℝ)
  | 9 => (2273133273 / 5000000000 : ℝ)
  | 10 => (904697691 / 2000000000 : ℝ)
  | 11 => (562596951 / 1250000000 : ℝ)
  | 12 => (2239064057 / 5000000000 : ℝ)
  | 13 => (2227773043 / 5000000000 : ℝ)
  | 14 => (443302963 / 1000000000 : ℝ)
  | 15 => (882115771 / 2000000000 : ℝ)
  | 16 => (548524233 / 1250000000 : ℝ)
  | 17 => (4365874761 / 10000000000 : ℝ)
  | 18 => (4343621643 / 10000000000 : ℝ)
  | 19 => (1080358653 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch029_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch029Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch029Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell580_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell581_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell582_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell583_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell584_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell585_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell586_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell587_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell588_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell589_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell590_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell591_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell592_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell593_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell594_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell595_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell596_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell597_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell598_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell599_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper] at h ⊢
    exact h

end HodgeProofHP
