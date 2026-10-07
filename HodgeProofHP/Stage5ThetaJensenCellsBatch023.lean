import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell460_leftExp :
    (4442826317 / 2500000000 : ℝ) ≤ Real.exp (23 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 40 : ℝ) (1018131159293 / 1000000000000 : ℝ)
    (4442826317 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell460_rightExp :
    Real.exp (461 / 800 : ℝ) ≤ (17793533291 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (461 / 800 : ℝ) (50908546541 / 50000000000 : ℝ)
    (17793533291 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell460_denomUpper :
    Real.exp (54462539632272563 / 10000000000000000 : ℝ) ≤ (2318878763501 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (54462539632272563 / 10000000000000000 : ℝ) (592768262807
    / 500000000000 : ℝ) (2318878763501 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell460_denomLower :
    (2302018530387 / 10000000000 : ℝ) ≤ Real.exp (1699673920609583 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1699673920609583 / 312500000000000 : ℝ) (592633100801 /
    500000000000 : ℝ) (2302018530387 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell460_product_lower :
    (1744693451859583 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell460_leftExp
    (by norm_num : (0 : ℝ) ≤ (4442826317 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell460_product_upper :
    Real.pi * Real.exp (461 / 800 : ℝ) ≤ (55900039632272563 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell460_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell460_endpointLower :
    (3932171609 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 80 : ℝ) (461 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1744693451859583 / 312500000000000 : ℝ) (Real.pi * Real.exp (23 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell460_product_lower
  have hD : Real.exp (Real.pi * Real.exp (461 / 800 : ℝ) - (23 / 160 : ℝ)) ≤
      (2318878763501 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell460_denomUpper
    linarith [hpThetaJensenCell460_product_upper]
  have hi : (1 / (2318878763501 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (461 / 800 : ℝ) - (23 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2318878763501 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2318878763501 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 160 : ℝ) - Real.pi * Real.exp (461 / 800 : ℝ)) := by
    rw [show (23 / 160 : ℝ) - Real.pi * Real.exp (461 / 800 : ℝ) =
      -(Real.pi * Real.exp (461 / 800 : ℝ) - (23 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 40 : ℝ)) := by
    have h := hpThetaJensenCell460_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2318878763501 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell460_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 80 : ℝ) (461 / 1600 : ℝ) ≤ (796634737 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (461 / 800 : ℝ)) (55900039632272563 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (461 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell460_product_upper
  have hD : (2302018530387 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 40 : ℝ) - (461 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell460_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell460_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 40 : ℝ) - (461 / 3200 : ℝ)) ≤
      (1 / (2302018530387 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2302018530387 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((461 / 3200 : ℝ) - Real.pi * Real.exp (23 / 40 : ℝ)) ≤
      (2 / (2302018530387 / 10000000000 : ℝ) : ℝ) := by
    rw [show (461 / 3200 : ℝ) - Real.pi * Real.exp (23 / 40 : ℝ) =
      -(Real.pi * Real.exp (23 / 40 : ℝ) - (461 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55900039632272563 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (55900039632272563 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell460_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 80 : ℝ) (461 / 1600 : ℝ)) :
    (3932171609 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (796634737 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell460_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell460_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell461_leftExp :
    (1779353329 / 1000000000 : ℝ) ≤ Real.exp (461 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (461 / 800 : ℝ) (1018170930819 / 1000000000000 : ℝ)
    (1779353329 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell461_rightExp :
    Real.exp (231 / 400 : ℝ) ≤ (8907894557 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (231 / 400 : ℝ) (509105351949 / 500000000000 : ℝ)
    (8907894557 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell461_denomUpper :
    Real.exp (27264666685009301 / 5000000000000000 : ℝ) ≤ (18675354113 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27264666685009301 / 5000000000000000 : ℝ) (1185784008991
    / 1000000000000 : ℝ) (18675354113 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell461_denomLower :
    (2317425792771 / 10000000000 : ℝ) ≤ Real.exp (680703397944971 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (680703397944971 / 125000000000000 : ℝ) (1185513304897 /
    1000000000000 : ℝ) (2317425792771 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell461_product_lower :
    (698750272944971 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (461 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell461_leftExp
    (by norm_num : (0 : ℝ) ≤ (1779353329 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell461_product_upper :
    Real.pi * Real.exp (231 / 400 : ℝ) ≤ (27984979185009301 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell461_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell461_endpointLower :
    (313405517 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (461 / 1600 : ℝ) (231 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (698750272944971 / 125000000000000 : ℝ) (Real.pi * Real.exp (461 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell461_product_lower
  have hD : Real.exp (Real.pi * Real.exp (231 / 400 : ℝ) - (461 / 3200 : ℝ)) ≤
      (18675354113 / 80000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell461_denomUpper
    linarith [hpThetaJensenCell461_product_upper]
  have hi : (1 / (18675354113 / 80000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (231 / 400 : ℝ) - (461 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18675354113 / 80000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18675354113 / 80000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((461 / 3200 : ℝ) - Real.pi * Real.exp (231 / 400 : ℝ)) := by
    rw [show (461 / 3200 : ℝ) - Real.pi * Real.exp (231 / 400 : ℝ) =
      -(Real.pi * Real.exp (231 / 400 : ℝ) - (461 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (461 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (461 / 800 : ℝ)) := by
    have h := hpThetaJensenCell461_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18675354113 / 80000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell461_endpointUpper :
    hpThetaJensenKernelEndpointUpper (461 / 1600 : ℝ) (231 / 800 : ℝ) ≤ (7936826389 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (231 / 400 : ℝ)) (27984979185009301 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (231 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell461_product_upper
  have hD : (2317425792771 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (461 / 800 : ℝ) - (231 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell461_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell461_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (461 / 800 : ℝ) - (231 / 1600 : ℝ)) ≤
      (1 / (2317425792771 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2317425792771 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((231 / 1600 : ℝ) - Real.pi * Real.exp (461 / 800 : ℝ)) ≤
      (2 / (2317425792771 / 10000000000 : ℝ) : ℝ) := by
    rw [show (231 / 1600 : ℝ) - Real.pi * Real.exp (461 / 800 : ℝ) =
      -(Real.pi * Real.exp (461 / 800 : ℝ) - (231 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27984979185009301 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (27984979185009301 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell461_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (461 / 1600 : ℝ) (231 / 800 : ℝ)) :
    (313405517 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7936826389 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell461_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell461_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell462_leftExp :
    (17815789113 / 10000000000 : ℝ) ≤ Real.exp (231 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (231 / 400 : ℝ) (1018210703897 / 1000000000000 : ℝ)
    (17815789113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell462_rightExp :
    Real.exp (463 / 800 : ℝ) ≤ (2229759097 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (463 / 800 : ℝ) (1018250478531 / 1000000000000 : ℝ)
    (2229759097 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell462_denomUpper :
    Real.exp (6824526820821521 / 1250000000000000 : ℝ) ≤ (2350084466429 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6824526820821521 / 1250000000000000 : ℝ) (1186031868183
    / 1000000000000 : ℝ) (2350084466429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell462_denomLower :
    (93318262031 / 400000000 : ℝ) ≤ Real.exp (6815383193885987 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6815383193885987 / 1250000000000000 : ℝ) (74110048959 /
    62500000000 : ℝ) (93318262031 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell462_product_lower :
    (6996242568885987 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (231 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell462_leftExp
    (by norm_num : (0 : ℝ) ≤ (17815789113 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell462_product_upper :
    Real.pi * Real.exp (463 / 800 : ℝ) ≤ (7004995570821521 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell462_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell462_endpointLower :
    (7805966703 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (231 / 800 : ℝ) (463 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6996242568885987 / 1250000000000000 : ℝ) (Real.pi * Real.exp (231 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell462_product_lower
  have hD : Real.exp (Real.pi * Real.exp (463 / 800 : ℝ) - (231 / 1600 : ℝ)) ≤
      (2350084466429 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell462_denomUpper
    linarith [hpThetaJensenCell462_product_upper]
  have hi : (1 / (2350084466429 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (463 / 800 : ℝ) - (231 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2350084466429 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2350084466429 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((231 / 1600 : ℝ) - Real.pi * Real.exp (463 / 800 : ℝ)) := by
    rw [show (231 / 1600 : ℝ) - Real.pi * Real.exp (463 / 800 : ℝ) =
      -(Real.pi * Real.exp (463 / 800 : ℝ) - (231 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (231 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (231 / 400 : ℝ)) := by
    have h := hpThetaJensenCell462_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2350084466429 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell462_endpointUpper :
    hpThetaJensenKernelEndpointUpper (231 / 800 : ℝ) (463 / 1600 : ℝ) ≤ (7907339563 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (463 / 800 : ℝ)) (7004995570821521 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (463 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell462_product_upper
  have hD : (93318262031 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (231 / 400 : ℝ) - (463 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell462_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell462_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (231 / 400 : ℝ) - (463 / 3200 : ℝ)) ≤
      (1 / (93318262031 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (93318262031 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((463 / 3200 : ℝ) - Real.pi * Real.exp (231 / 400 : ℝ)) ≤
      (2 / (93318262031 / 400000000 : ℝ) : ℝ) := by
    rw [show (463 / 3200 : ℝ) - Real.pi * Real.exp (231 / 400 : ℝ) =
      -(Real.pi * Real.exp (231 / 400 : ℝ) - (463 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7004995570821521 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (7004995570821521 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell462_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (231 / 800 : ℝ) (463 / 1600 : ℝ)) :
    (7805966703 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7907339563 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell462_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell462_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell463_leftExp :
    (8919036387 / 5000000000 : ℝ) ≤ Real.exp (463 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (463 / 800 : ℝ) (101825047853 / 100000000000 : ℝ)
    (8919036387 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell463_rightExp :
    Real.exp (29 / 50 : ℝ) ≤ (4465096077 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 50 : ℝ) (1018290254717 / 1000000000000 : ℝ)
    (4465096077 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell463_denomUpper :
    Real.exp (13665795829830661 / 2500000000000000 : ℝ) ≤ (2365875505323 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13665795829830661 / 2500000000000000 : ℝ) (1186280103767
    / 1000000000000 : ℝ) (2365875505323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell463_denomLower :
    (2348611931581 / 10000000000 : ℝ) ≤ Real.exp (3411871670138513 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3411871670138513 / 625000000000000 : ℝ) (296502159397 /
    250000000000 : ℝ) (2348611931581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell463_product_lower :
    (3502496670138513 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (463 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell463_leftExp
    (by norm_num : (0 : ℝ) ≤ (8919036387 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell463_product_upper :
    Real.pi * Real.exp (29 / 50 : ℝ) ≤ (14027514579830661 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell463_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell463_endpointLower :
    (3888414961 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (463 / 1600 : ℝ) (29 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3502496670138513 / 625000000000000 : ℝ) (Real.pi * Real.exp (463 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell463_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 50 : ℝ) - (463 / 3200 : ℝ)) ≤
      (2365875505323 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell463_denomUpper
    linarith [hpThetaJensenCell463_product_upper]
  have hi : (1 / (2365875505323 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 50 : ℝ) - (463 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2365875505323 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2365875505323 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((463 / 3200 : ℝ) - Real.pi * Real.exp (29 / 50 : ℝ)) := by
    rw [show (463 / 3200 : ℝ) - Real.pi * Real.exp (29 / 50 : ℝ) =
      -(Real.pi * Real.exp (29 / 50 : ℝ) - (463 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (463 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (463 / 800 : ℝ)) := by
    have h := hpThetaJensenCell463_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2365875505323 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell463_endpointUpper :
    hpThetaJensenKernelEndpointUpper (463 / 1600 : ℝ) (29 / 100 : ℝ) ≤ (1969471811 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 50 : ℝ)) (14027514579830661 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell463_product_upper
  have hD : (2348611931581 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (463 / 800 : ℝ) - (29 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell463_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell463_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (463 / 800 : ℝ) - (29 / 200 : ℝ)) ≤
      (1 / (2348611931581 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2348611931581 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 200 : ℝ) - Real.pi * Real.exp (463 / 800 : ℝ)) ≤
      (2 / (2348611931581 / 10000000000 : ℝ) : ℝ) := by
    rw [show (29 / 200 : ℝ) - Real.pi * Real.exp (463 / 800 : ℝ) =
      -(Real.pi * Real.exp (463 / 800 : ℝ) - (29 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14027514579830661 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14027514579830661 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell463_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (463 / 1600 : ℝ) (29 / 100 : ℝ)) :
    (3888414961 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1969471811 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell463_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell463_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell464_leftExp :
    (17860384307 / 10000000000 : ℝ) ≤ Real.exp (29 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 50 : ℝ) (254572563679 / 250000000000 : ℝ)
    (17860384307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell464_rightExp :
    Real.exp (93 / 160 : ℝ) ≤ (4470680937 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93 / 160 : ℝ) (1018330032457 / 1000000000000 : ℝ)
    (4470680937 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell464_denomUpper :
    Real.exp (13682559936912641 / 2500000000000000 : ℝ) ≤ (1190896766043 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13682559936912641 / 2500000000000000 : ℝ) (593264358199
    / 500000000000 : ℝ) (1190896766043 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell464_denomLower :
    (295549133927 / 1250000000 : ℝ) ≤ Real.exp (6832114431974593 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6832114431974593 / 1250000000000000 : ℝ) (593128434119 /
    500000000000 : ℝ) (295549133927 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell464_product_lower :
    (7013755056974593 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell464_leftExp
    (by norm_num : (0 : ℝ) ≤ (17860384307 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell464_product_upper :
    Real.pi * Real.exp (93 / 160 : ℝ) ≤ (14045059936912641 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell464_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell464_endpointLower :
    (7747727927 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 100 : ℝ) (93 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7013755056974593 / 1250000000000000 : ℝ) (Real.pi * Real.exp (29 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell464_product_lower
  have hD : Real.exp (Real.pi * Real.exp (93 / 160 : ℝ) - (29 / 200 : ℝ)) ≤
      (1190896766043 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell464_denomUpper
    linarith [hpThetaJensenCell464_product_upper]
  have hi : (1 / (1190896766043 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (93 / 160 : ℝ) - (29 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1190896766043 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1190896766043 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 200 : ℝ) - Real.pi * Real.exp (93 / 160 : ℝ)) := by
    rw [show (29 / 200 : ℝ) - Real.pi * Real.exp (93 / 160 : ℝ) =
      -(Real.pi * Real.exp (93 / 160 : ℝ) - (29 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 50 : ℝ)) := by
    have h := hpThetaJensenCell464_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1190896766043 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell464_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 100 : ℝ) (93 / 320 : ℝ) ≤ (1962117449 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (93 / 160 : ℝ)) (14045059936912641 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (93 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell464_product_upper
  have hD : (295549133927 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 50 : ℝ) - (93 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell464_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell464_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 50 : ℝ) - (93 / 640 : ℝ)) ≤
      (1 / (295549133927 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (295549133927 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((93 / 640 : ℝ) - Real.pi * Real.exp (29 / 50 : ℝ)) ≤
      (2 / (295549133927 / 1250000000 : ℝ) : ℝ) := by
    rw [show (93 / 640 : ℝ) - Real.pi * Real.exp (29 / 50 : ℝ) =
      -(Real.pi * Real.exp (29 / 50 : ℝ) - (93 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14045059936912641 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14045059936912641 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell464_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 100 : ℝ) (93 / 320 : ℝ)) :
    (7747727927 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1962117449 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell464_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell464_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell465_leftExp :
    (8941361873 / 5000000000 : ℝ) ≤ Real.exp (93 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (93 / 160 : ℝ) (127291254057 / 125000000000 : ℝ)
    (8941361873 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell465_rightExp :
    Real.exp (233 / 400 : ℝ) ≤ (17905091129 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (233 / 400 : ℝ) (1018369811751 / 1000000000000 : ℝ)
    (17905091129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell465_denomUpper :
    Real.exp (54797383955228497 / 10000000000000000 : ℝ) ≤ (2397839706119 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (54797383955228497 / 10000000000000000 : ℝ)
    (1186777706677 / 1000000000000 : ℝ) (2397839706119 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell465_denomLower :
    (2380301118039 / 10000000000 : ℝ) ≤ Real.exp (3420248241165227 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3420248241165227 / 625000000000000 : ℝ) (237301095181 /
    200000000000 : ℝ) (2380301118039 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell465_product_lower :
    (3511263866165227 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (93 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell465_leftExp
    (by norm_num : (0 : ℝ) ≤ (8941361873 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell465_product_upper :
    Real.pi * Real.exp (233 / 400 : ℝ) ≤ (56250508955228497 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell465_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell465_endpointLower :
    (3859330537 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 320 : ℝ) (233 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3511263866165227 / 625000000000000 : ℝ) (Real.pi * Real.exp (93 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell465_product_lower
  have hD : Real.exp (Real.pi * Real.exp (233 / 400 : ℝ) - (93 / 640 : ℝ)) ≤
      (2397839706119 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell465_denomUpper
    linarith [hpThetaJensenCell465_product_upper]
  have hi : (1 / (2397839706119 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (233 / 400 : ℝ) - (93 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2397839706119 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2397839706119 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((93 / 640 : ℝ) - Real.pi * Real.exp (233 / 400 : ℝ)) := by
    rw [show (93 / 640 : ℝ) - Real.pi * Real.exp (233 / 400 : ℝ) =
      -(Real.pi * Real.exp (233 / 400 : ℝ) - (93 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (93 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (93 / 160 : ℝ)) := by
    have h := hpThetaJensenCell465_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2397839706119 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell465_endpointUpper :
    hpThetaJensenKernelEndpointUpper (93 / 320 : ℝ) (233 / 800 : ℝ) ≤ (977385947 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (233 / 400 : ℝ)) (56250508955228497 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (233 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell465_product_upper
  have hD : (2380301118039 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (93 / 160 : ℝ) - (233 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell465_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell465_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (93 / 160 : ℝ) - (233 / 1600 : ℝ)) ≤
      (1 / (2380301118039 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2380301118039 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((233 / 1600 : ℝ) - Real.pi * Real.exp (93 / 160 : ℝ)) ≤
      (2 / (2380301118039 / 10000000000 : ℝ) : ℝ) := by
    rw [show (233 / 1600 : ℝ) - Real.pi * Real.exp (93 / 160 : ℝ) =
      -(Real.pi * Real.exp (93 / 160 : ℝ) - (233 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56250508955228497 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (56250508955228497 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell465_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (93 / 320 : ℝ) (233 / 800 : ℝ)) :
    (3859330537 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (977385947 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell465_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell465_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell466_leftExp :
    (2238136391 / 1250000000 : ℝ) ≤ Real.exp (233 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (233 / 400 : ℝ) (4073479247 / 4000000000 : ℝ) (2238136391
    / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell466_rightExp :
    Real.exp (467 / 800 : ℝ) ≤ (2240935811 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (467 / 800 : ℝ) (1018409592599 / 1000000000000 : ℝ)
    (2240935811 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell466_denomUpper :
    Real.exp (6858077007286923 / 1250000000000000 : ℝ) ≤ (2414015201463 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6858077007286923 / 1250000000000000 : ℝ) (1187027075251
    / 1000000000000 : ℝ) (2414015201463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell466_denomLower :
    (2396337233069 / 10000000000 : ℝ) ≤ Real.exp (856111188234309 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (856111188234309 / 156250000000000 : ℝ) (296688615309 /
    250000000000 : ℝ) (2396337233069 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell466_product_lower :
    (878913922609309 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (233 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell466_leftExp
    (by norm_num : (0 : ℝ) ≤ (2238136391 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell466_product_upper :
    Real.pi * Real.exp (467 / 800 : ℝ) ≤ (7040108257286923 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell466_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell466_endpointLower :
    (480601857 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (233 / 800 : ℝ) (467 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (878913922609309 / 156250000000000 : ℝ) (Real.pi * Real.exp (233 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell466_product_lower
  have hD : Real.exp (Real.pi * Real.exp (467 / 800 : ℝ) - (233 / 1600 : ℝ)) ≤
      (2414015201463 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell466_denomUpper
    linarith [hpThetaJensenCell466_product_upper]
  have hi : (1 / (2414015201463 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (467 / 800 : ℝ) - (233 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2414015201463 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2414015201463 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((233 / 1600 : ℝ) - Real.pi * Real.exp (467 / 800 : ℝ)) := by
    rw [show (233 / 1600 : ℝ) - Real.pi * Real.exp (467 / 800 : ℝ) =
      -(Real.pi * Real.exp (467 / 800 : ℝ) - (233 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (233 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (233 / 400 : ℝ)) := by
    have h := hpThetaJensenCell466_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2414015201463 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell466_endpointUpper :
    hpThetaJensenKernelEndpointUpper (233 / 800 : ℝ) (467 / 1600 : ℝ) ≤ (7789740937 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (467 / 800 : ℝ)) (7040108257286923 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (467 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell466_product_upper
  have hD : (2396337233069 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (233 / 400 : ℝ) - (467 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell466_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell466_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (233 / 400 : ℝ) - (467 / 3200 : ℝ)) ≤
      (1 / (2396337233069 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2396337233069 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((467 / 3200 : ℝ) - Real.pi * Real.exp (233 / 400 : ℝ)) ≤
      (2 / (2396337233069 / 10000000000 : ℝ) : ℝ) := by
    rw [show (467 / 3200 : ℝ) - Real.pi * Real.exp (233 / 400 : ℝ) =
      -(Real.pi * Real.exp (233 / 400 : ℝ) - (467 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7040108257286923 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (7040108257286923 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell466_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (233 / 800 : ℝ) (467 / 1600 : ℝ)) :
    (480601857 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7789740937 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell466_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell466_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell467_leftExp :
    (8963743243 / 5000000000 : ℝ) ≤ Real.exp (467 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (467 / 800 : ℝ) (509204796299 / 500000000000 : ℝ)
    (8963743243 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell467_rightExp :
    Real.exp (117 / 200 : ℝ) ≤ (17949909857 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (117 / 200 : ℝ) (1629519 / 1600000 : ℝ)
    (17949909857 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell467_denomUpper :
    Real.exp (54931936157382201 / 10000000000000000 : ℝ) ≤ (2430321200213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (54931936157382201 / 10000000000000000 : ℝ)
    (1187276822709 / 1000000000000 : ℝ) (2430321200213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell467_denomLower :
    (2412502586719 / 10000000000 : ℝ) ≤ Real.exp (3428646757782857 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3428646757782857 / 625000000000000 : ℝ) (118700382483 /
    100000000000 : ℝ) (2412502586719 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell467_product_lower :
    (3520053007782857 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (467 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell467_leftExp
    (by norm_num : (0 : ℝ) ≤ (8963743243 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell467_product_upper :
    Real.pi * Real.exp (117 / 200 : ℝ) ≤ (56391311157382201 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell467_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell467_endpointLower :
    (1532126839 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (467 / 1600 : ℝ) (117 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3520053007782857 / 625000000000000 : ℝ) (Real.pi * Real.exp (467 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell467_product_lower
  have hD : Real.exp (Real.pi * Real.exp (117 / 200 : ℝ) - (467 / 3200 : ℝ)) ≤
      (2430321200213 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell467_denomUpper
    linarith [hpThetaJensenCell467_product_upper]
  have hi : (1 / (2430321200213 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (117 / 200 : ℝ) - (467 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2430321200213 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2430321200213 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((467 / 3200 : ℝ) - Real.pi * Real.exp (117 / 200 : ℝ)) := by
    rw [show (467 / 3200 : ℝ) - Real.pi * Real.exp (117 / 200 : ℝ) =
      -(Real.pi * Real.exp (117 / 200 : ℝ) - (467 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (467 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (467 / 800 : ℝ)) := by
    have h := hpThetaJensenCell467_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2430321200213 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell467_endpointUpper :
    hpThetaJensenKernelEndpointUpper (467 / 1600 : ℝ) (117 / 400 : ℝ) ≤ (1552086047 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (117 / 200 : ℝ)) (56391311157382201 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (117 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell467_product_upper
  have hD : (2412502586719 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (467 / 800 : ℝ) - (117 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell467_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell467_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (467 / 800 : ℝ) - (117 / 800 : ℝ)) ≤
      (1 / (2412502586719 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2412502586719 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((117 / 800 : ℝ) - Real.pi * Real.exp (467 / 800 : ℝ)) ≤
      (2 / (2412502586719 / 10000000000 : ℝ) : ℝ) := by
    rw [show (117 / 800 : ℝ) - Real.pi * Real.exp (467 / 800 : ℝ) =
      -(Real.pi * Real.exp (467 / 800 : ℝ) - (117 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56391311157382201 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (56391311157382201 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell467_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (467 / 1600 : ℝ) (117 / 400 : ℝ)) :
    (1532126839 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1552086047 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell467_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell467_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell468_leftExp :
    (3589981971 / 2000000000 : ℝ) ≤ Real.exp (117 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (117 / 200 : ℝ) (1018449374999 / 1000000000000 : ℝ)
    (3589981971 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell468_rightExp :
    Real.exp (469 / 800 : ℝ) ≤ (8986180637 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (469 / 800 : ℝ) (254622289739 / 250000000000 : ℝ)
    (8986180637 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell468_denomUpper :
    Real.exp (27499672185934741 / 5000000000000000 : ℝ) ≤ (2446758901029 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27499672185934741 / 5000000000000000 : ℝ) (1187526949711
    / 1000000000000 : ℝ) (2446758901029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell468_denomLower :
    (1214399181367 / 5000000000 : ℝ) ≤ Real.exp (1373141705029729 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1373141705029729 / 250000000000000 : ℝ) (1187253567313 /
    1000000000000 : ℝ) (1214399181367 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell468_product_lower :
    (1409782330029729 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (117 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell468_leftExp
    (by norm_num : (0 : ℝ) ≤ (3589981971 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell468_product_upper :
    Real.pi * Real.exp (469 / 800 : ℝ) ≤ (28230922185934741 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell468_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell468_endpointLower :
    (1526334973 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (117 / 400 : ℝ) (469 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1409782330029729 / 250000000000000 : ℝ) (Real.pi * Real.exp (117 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell468_product_lower
  have hD : Real.exp (Real.pi * Real.exp (469 / 800 : ℝ) - (117 / 800 : ℝ)) ≤
      (2446758901029 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell468_denomUpper
    linarith [hpThetaJensenCell468_product_upper]
  have hi : (1 / (2446758901029 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (469 / 800 : ℝ) - (117 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2446758901029 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2446758901029 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((117 / 800 : ℝ) - Real.pi * Real.exp (469 / 800 : ℝ)) := by
    rw [show (117 / 800 : ℝ) - Real.pi * Real.exp (469 / 800 : ℝ) =
      -(Real.pi * Real.exp (469 / 800 : ℝ) - (117 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (117 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (117 / 200 : ℝ)) := by
    have h := hpThetaJensenCell468_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2446758901029 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell468_endpointUpper :
    hpThetaJensenKernelEndpointUpper (117 / 400 : ℝ) (469 / 1600 : ℝ) ≤ (483197239 / 625000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (469 / 800 : ℝ)) (28230922185934741 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (469 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell468_product_upper
  have hD : (1214399181367 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (117 / 200 : ℝ) - (469 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell468_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell468_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (117 / 200 : ℝ) - (469 / 3200 : ℝ)) ≤
      (1 / (1214399181367 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1214399181367 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((469 / 3200 : ℝ) - Real.pi * Real.exp (117 / 200 : ℝ)) ≤
      (2 / (1214399181367 / 5000000000 : ℝ) : ℝ) := by
    rw [show (469 / 3200 : ℝ) - Real.pi * Real.exp (117 / 200 : ℝ) =
      -(Real.pi * Real.exp (117 / 200 : ℝ) - (469 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28230922185934741 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (28230922185934741 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell468_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (117 / 400 : ℝ) (469 / 1600 : ℝ)) :
    (1526334973 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (483197239 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell468_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell468_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell469_leftExp :
    (2246545159 / 1250000000 : ℝ) ≤ Real.exp (469 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (469 / 800 : ℝ) (203697831791 / 200000000000 : ℝ)
    (2246545159 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell469_rightExp :
    Real.exp (47 / 80 : ℝ) ≤ (4498710193 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 80 : ℝ) (509264472233 / 500000000000 : ℝ)
    (4498710193 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell469_denomUpper :
    Real.exp (13766710201357449 / 2500000000000000 : ℝ) ≤ (2463329510921 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13766710201357449 / 2500000000000000 : ℝ) (59388872843 /
    50000000000 : ℝ) (2463329510921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell469_denomLower :
    (305653219781 / 1250000000 : ℝ) ≤ Real.exp (859266818644141 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (859266818644141 / 156250000000000 : ℝ) (1187503689333 /
    1000000000000 : ℝ) (305653219781 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell469_product_lower :
    (882216037394141 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (469 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell469_leftExp
    (by norm_num : (0 : ℝ) ≤ (2246545159 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell469_product_upper :
    Real.pi * Real.exp (47 / 80 : ℝ) ≤ (14133116451357449 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell469_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell469_endpointLower :
    (3801376037 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (469 / 1600 : ℝ) (47 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (882216037394141 / 156250000000000 : ℝ) (Real.pi * Real.exp (469 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell469_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 80 : ℝ) - (469 / 3200 : ℝ)) ≤
      (2463329510921 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell469_denomUpper
    linarith [hpThetaJensenCell469_product_upper]
  have hi : (1 / (2463329510921 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 80 : ℝ) - (469 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2463329510921 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2463329510921 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((469 / 3200 : ℝ) - Real.pi * Real.exp (47 / 80 : ℝ)) := by
    rw [show (469 / 3200 : ℝ) - Real.pi * Real.exp (47 / 80 : ℝ) =
      -(Real.pi * Real.exp (47 / 80 : ℝ) - (469 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (469 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (469 / 800 : ℝ)) := by
    have h := hpThetaJensenCell469_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2463329510921 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell469_endpointUpper :
    hpThetaJensenKernelEndpointUpper (469 / 1600 : ℝ) (47 / 160 : ℝ) ≤ (240684939 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 80 : ℝ)) (14133116451357449 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell469_product_upper
  have hD : (305653219781 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (469 / 800 : ℝ) - (47 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell469_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell469_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (469 / 800 : ℝ) - (47 / 320 : ℝ)) ≤
      (1 / (305653219781 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (305653219781 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 320 : ℝ) - Real.pi * Real.exp (469 / 800 : ℝ)) ≤
      (2 / (305653219781 / 1250000000 : ℝ) : ℝ) := by
    rw [show (47 / 320 : ℝ) - Real.pi * Real.exp (469 / 800 : ℝ) =
      -(Real.pi * Real.exp (469 / 800 : ℝ) - (47 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14133116451357449 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14133116451357449 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell469_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (469 / 1600 : ℝ) (47 / 160 : ℝ)) :
    (3801376037 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (240684939 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell469_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell469_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell470_leftExp :
    (17994840771 / 10000000000 : ℝ) ≤ Real.exp (47 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 80 : ℝ) (203705788893 / 200000000000 : ℝ)
    (17994840771 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell470_rightExp :
    Real.exp (471 / 800 : ℝ) ≤ (18017348387 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (471 / 800 : ℝ) (101856873153 / 100000000000 : ℝ)
    (18017348387 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell470_denomUpper :
    Real.exp (55134425571160491 / 10000000000000000 : ℝ) ≤ (155002140713 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55134425571160491 / 10000000000000000 : ℝ) (594014172397
    / 500000000000 : ℝ) (155002140713 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell470_denomLower :
    (2461785980179 / 10000000000 : ℝ) ≤ Real.exp (6882571600930929 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6882571600930929 / 1250000000000000 : ℝ) (1187754191503
    / 1000000000000 : ℝ) (2461785980179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell470_product_lower :
    (7066555975930929 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell470_leftExp
    (by norm_num : (0 : ℝ) ≤ (17994840771 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell470_product_upper :
    Real.pi * Real.exp (471 / 800 : ℝ) ≤ (56603175571160491 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell470_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell470_endpointLower :
    (1893466541 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 160 : ℝ) (471 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7066555975930929 / 1250000000000000 : ℝ) (Real.pi * Real.exp (47 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell470_product_lower
  have hD : Real.exp (Real.pi * Real.exp (471 / 800 : ℝ) - (47 / 320 : ℝ)) ≤
      (155002140713 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell470_denomUpper
    linarith [hpThetaJensenCell470_product_upper]
  have hi : (1 / (155002140713 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (471 / 800 : ℝ) - (47 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (155002140713 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (155002140713 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 320 : ℝ) - Real.pi * Real.exp (471 / 800 : ℝ)) := by
    rw [show (47 / 320 : ℝ) - Real.pi * Real.exp (471 / 800 : ℝ) =
      -(Real.pi * Real.exp (471 / 800 : ℝ) - (47 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 80 : ℝ)) := by
    have h := hpThetaJensenCell470_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (155002140713 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell470_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 160 : ℝ) (471 / 1600 : ℝ) ≤ (383635863 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (471 / 800 : ℝ)) (56603175571160491 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (471 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell470_product_upper
  have hD : (2461785980179 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 80 : ℝ) - (471 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell470_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell470_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 80 : ℝ) - (471 / 3200 : ℝ)) ≤
      (1 / (2461785980179 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2461785980179 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((471 / 3200 : ℝ) - Real.pi * Real.exp (47 / 80 : ℝ)) ≤
      (2 / (2461785980179 / 10000000000 : ℝ) : ℝ) := by
    rw [show (471 / 3200 : ℝ) - Real.pi * Real.exp (47 / 80 : ℝ) =
      -(Real.pi * Real.exp (47 / 80 : ℝ) - (471 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56603175571160491 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (56603175571160491 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell470_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 160 : ℝ) (471 / 1600 : ℝ)) :
    (1893466541 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (383635863 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell470_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell470_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell471_leftExp :
    (9008674193 / 5000000000 : ℝ) ≤ Real.exp (471 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (471 / 800 : ℝ) (1018568731529 / 1000000000000 : ℝ)
    (9008674193 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell471_rightExp :
    Real.exp (59 / 100 : ℝ) ≤ (3607976831 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 100 : ℝ) (254652130037 / 250000000000 : ℝ)
    (3607976831 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell471_denomUpper :
    Real.exp (11040419756431783 / 2000000000000000 : ℝ) ≤ (499374871301 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11040419756431783 / 2000000000000000 : ℝ) (1188279614153
    / 1000000000000 : ℝ) (499374871301 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell471_denomLower :
    (619620061973 / 2500000000 : ℝ) ≤ Real.exp (3445509846916907 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3445509846916907 / 625000000000000 : ℝ) (29700126861 /
    25000000000 : ℝ) (619620061973 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell471_product_lower :
    (3537697346916907 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (471 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell471_leftExp
    (by norm_num : (0 : ℝ) ≤ (9008674193 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell471_product_upper :
    Real.pi * Real.exp (59 / 100 : ℝ) ≤ (11334794756431783 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell471_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell471_endpointLower :
    (3772508737 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (471 / 1600 : ℝ) (59 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3537697346916907 / 625000000000000 : ℝ) (Real.pi * Real.exp (471 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell471_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 100 : ℝ) - (471 / 3200 : ℝ)) ≤
      (499374871301 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell471_denomUpper
    linarith [hpThetaJensenCell471_product_upper]
  have hi : (1 / (499374871301 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 100 : ℝ) - (471 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (499374871301 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (499374871301 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((471 / 3200 : ℝ) - Real.pi * Real.exp (59 / 100 : ℝ)) := by
    rw [show (471 / 3200 : ℝ) - Real.pi * Real.exp (59 / 100 : ℝ) =
      -(Real.pi * Real.exp (59 / 100 : ℝ) - (471 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (471 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (471 / 800 : ℝ)) := by
    have h := hpThetaJensenCell471_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (499374871301 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell471_endpointUpper :
    hpThetaJensenKernelEndpointUpper (471 / 1600 : ℝ) (59 / 200 : ℝ) ≤ (764355381 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 100 : ℝ)) (11334794756431783 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell471_product_upper
  have hD : (619620061973 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (471 / 800 : ℝ) - (59 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell471_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell471_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (471 / 800 : ℝ) - (59 / 400 : ℝ)) ≤
      (1 / (619620061973 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (619620061973 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 400 : ℝ) - Real.pi * Real.exp (471 / 800 : ℝ)) ≤
      (2 / (619620061973 / 2500000000 : ℝ) : ℝ) := by
    rw [show (59 / 400 : ℝ) - Real.pi * Real.exp (471 / 800 : ℝ) =
      -(Real.pi * Real.exp (471 / 800 : ℝ) - (59 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11334794756431783 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (11334794756431783 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell471_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (471 / 1600 : ℝ) (59 / 200 : ℝ)) :
    (3772508737 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (764355381 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell471_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell471_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell472_leftExp :
    (18039884153 / 10000000000 : ℝ) ≤ Real.exp (59 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 100 : ℝ) (1018608520147 / 1000000000000 : ℝ)
    (18039884153 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell472_rightExp :
    Real.exp (473 / 800 : ℝ) ≤ (1806244811 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (473 / 800 : ℝ) (1018648310321 / 1000000000000 : ℝ)
    (1806244811 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell472_denomUpper :
    Real.exp (5526986054523923 / 1000000000000000 : ℝ) ≤ (314231383871 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5526986054523923 / 1000000000000000 : ℝ) (1188531265551
    / 1000000000000 : ℝ) (314231383871 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell472_denomLower :
    (623827448603 / 2500000000 : ℝ) ≤ Real.exp (6899478841998947 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6899478841998947 / 1250000000000000 : ℝ) (1188256338781
    / 1000000000000 : ℝ) (623827448603 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell472_product_lower :
    (7084244466998947 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell472_leftExp
    (by norm_num : (0 : ℝ) ≤ (18039884153 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell472_product_upper :
    Real.pi * Real.exp (473 / 800 : ℝ) ≤ (5674486054523923 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell472_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell472_endpointLower :
    (7516206349 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 200 : ℝ) (473 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7084244466998947 / 1250000000000000 : ℝ) (Real.pi * Real.exp (59 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell472_product_lower
  have hD : Real.exp (Real.pi * Real.exp (473 / 800 : ℝ) - (59 / 400 : ℝ)) ≤
      (314231383871 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell472_denomUpper
    linarith [hpThetaJensenCell472_product_upper]
  have hi : (1 / (314231383871 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (473 / 800 : ℝ) - (59 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (314231383871 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (314231383871 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 400 : ℝ) - Real.pi * Real.exp (473 / 800 : ℝ)) := by
    rw [show (59 / 400 : ℝ) - Real.pi * Real.exp (473 / 800 : ℝ) =
      -(Real.pi * Real.exp (473 / 800 : ℝ) - (59 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 100 : ℝ)) := by
    have h := hpThetaJensenCell472_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (314231383871 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell472_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 200 : ℝ) (473 / 1600 : ℝ) ≤ (7614428039 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (473 / 800 : ℝ)) (5674486054523923 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (473 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell472_product_upper
  have hD : (623827448603 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 100 : ℝ) - (473 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell472_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell472_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 100 : ℝ) - (473 / 3200 : ℝ)) ≤
      (1 / (623827448603 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (623827448603 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((473 / 3200 : ℝ) - Real.pi * Real.exp (59 / 100 : ℝ)) ≤
      (2 / (623827448603 / 2500000000 : ℝ) : ℝ) := by
    rw [show (473 / 3200 : ℝ) - Real.pi * Real.exp (59 / 100 : ℝ) =
      -(Real.pi * Real.exp (59 / 100 : ℝ) - (473 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5674486054523923 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5674486054523923 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell472_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 200 : ℝ) (473 / 1600 : ℝ)) :
    (7516206349 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7614428039 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell472_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell472_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell473_leftExp :
    (4515612027 / 2500000000 : ℝ) ≤ Real.exp (473 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (473 / 800 : ℝ) (12733103879 / 12500000000 : ℝ)
    (4515612027 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell473_rightExp :
    Real.exp (237 / 400 : ℝ) ≤ (18085040287 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (237 / 400 : ℝ) (1018688102047 / 1000000000000 : ℝ)
    (18085040287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell473_denomUpper :
    Real.exp (55337710970357191 / 10000000000000000 : ℝ) ≤ (316370706663 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55337710970357191 / 10000000000000000 : ℝ)
    (1188783299619 / 1000000000000 : ℝ) (316370706663 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell473_denomLower :
    (1256137932763 / 5000000000 : ℝ) ≤ Real.exp (1726987264890873 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1726987264890873 / 312500000000000 : ℝ) (1188507985167 /
    1000000000000 : ℝ) (1256137932763 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell473_product_lower :
    (1773276327390873 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (473 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell473_leftExp
    (by norm_num : (0 : ℝ) ≤ (4515612027 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell473_product_upper :
    Real.pi * Real.exp (237 / 400 : ℝ) ≤ (56815835970357191 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell473_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell473_endpointLower :
    (748743313 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (473 / 1600 : ℝ) (237 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1773276327390873 / 312500000000000 : ℝ) (Real.pi * Real.exp (473 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell473_product_lower
  have hD : Real.exp (Real.pi * Real.exp (237 / 400 : ℝ) - (473 / 3200 : ℝ)) ≤
      (316370706663 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell473_denomUpper
    linarith [hpThetaJensenCell473_product_upper]
  have hi : (1 / (316370706663 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (237 / 400 : ℝ) - (473 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (316370706663 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (316370706663 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((473 / 3200 : ℝ) - Real.pi * Real.exp (237 / 400 : ℝ)) := by
    rw [show (473 / 3200 : ℝ) - Real.pi * Real.exp (237 / 400 : ℝ) =
      -(Real.pi * Real.exp (237 / 400 : ℝ) - (473 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (473 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (473 / 800 : ℝ)) := by
    have h := hpThetaJensenCell473_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (316370706663 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell473_endpointUpper :
    hpThetaJensenKernelEndpointUpper (473 / 1600 : ℝ) (237 / 800 : ℝ) ≤ (7585340291 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (237 / 400 : ℝ)) (56815835970357191 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (237 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell473_product_upper
  have hD : (1256137932763 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (473 / 800 : ℝ) - (237 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell473_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell473_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (473 / 800 : ℝ) - (237 / 1600 : ℝ)) ≤
      (1 / (1256137932763 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1256137932763 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((237 / 1600 : ℝ) - Real.pi * Real.exp (473 / 800 : ℝ)) ≤
      (2 / (1256137932763 / 5000000000 : ℝ) : ℝ) := by
    rw [show (237 / 1600 : ℝ) - Real.pi * Real.exp (473 / 800 : ℝ) =
      -(Real.pi * Real.exp (473 / 800 : ℝ) - (237 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56815835970357191 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (56815835970357191 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell473_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (473 / 1600 : ℝ) (237 / 800 : ℝ)) :
    (748743313 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7585340291 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell473_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell473_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell474_leftExp :
    (3617008057 / 2000000000 : ℝ) ≤ Real.exp (237 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (237 / 400 : ℝ) (509344051023 / 500000000000 : ℝ)
    (3617008057 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell474_rightExp :
    Real.exp (19 / 32 : ℝ) ≤ (9053830361 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 32 : ℝ) (1018727895329 / 1000000000000 : ℝ)
    (9053830361 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell474_denomUpper :
    Real.exp (27702825085305073 / 5000000000000000 : ℝ) ≤ (1274109687699 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27702825085305073 / 5000000000000000 : ℝ) (1189035716997
    / 1000000000000 : ℝ) (1274109687699 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell474_denomLower :
    (2529379717947 / 10000000000 : ℝ) ≤ Real.exp (1383286071975843 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1383286071975843 / 250000000000000 : ℝ) (594380007107 /
    500000000000 : ℝ) (2529379717947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell474_product_lower :
    (1420395446975843 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (237 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell474_leftExp
    (by norm_num : (0 : ℝ) ≤ (3617008057 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell474_product_upper :
    Real.pi * Real.exp (19 / 32 : ℝ) ≤ (28443450085305073 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell474_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell474_endpointLower :
    (7458698151 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (237 / 800 : ℝ) (19 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1420395446975843 / 250000000000000 : ℝ) (Real.pi * Real.exp (237 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell474_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 32 : ℝ) - (237 / 1600 : ℝ)) ≤
      (1274109687699 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell474_denomUpper
    linarith [hpThetaJensenCell474_product_upper]
  have hi : (1 / (1274109687699 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 32 : ℝ) - (237 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1274109687699 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1274109687699 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((237 / 1600 : ℝ) - Real.pi * Real.exp (19 / 32 : ℝ)) := by
    rw [show (237 / 1600 : ℝ) - Real.pi * Real.exp (19 / 32 : ℝ) =
      -(Real.pi * Real.exp (19 / 32 : ℝ) - (237 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (237 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (237 / 400 : ℝ)) := by
    have h := hpThetaJensenCell474_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1274109687699 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell474_endpointUpper :
    hpThetaJensenKernelEndpointUpper (237 / 800 : ℝ) (19 / 64 : ℝ) ≤ (755629091 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 32 : ℝ)) (28443450085305073 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell474_product_upper
  have hD : (2529379717947 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (237 / 400 : ℝ) - (19 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell474_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell474_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (237 / 400 : ℝ) - (19 / 128 : ℝ)) ≤
      (1 / (2529379717947 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2529379717947 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 128 : ℝ) - Real.pi * Real.exp (237 / 400 : ℝ)) ≤
      (2 / (2529379717947 / 10000000000 : ℝ) : ℝ) := by
    rw [show (19 / 128 : ℝ) - Real.pi * Real.exp (237 / 400 : ℝ) =
      -(Real.pi * Real.exp (237 / 400 : ℝ) - (19 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28443450085305073 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (28443450085305073 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell474_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (237 / 800 : ℝ) (19 / 64 : ℝ)) :
    (7458698151 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (755629091 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell474_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell474_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell475_leftExp :
    (18107660721 / 10000000000 : ℝ) ≤ Real.exp (19 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 32 : ℝ) (31835246729 / 31250000000 : ℝ)
    (18107660721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell475_rightExp :
    Real.exp (119 / 200 : ℝ) ≤ (362606189 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (119 / 200 : ℝ) (254691922541 / 250000000000 : ℝ)
    (362606189 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell475_denomUpper :
    Real.exp (1109473565119077 / 200000000000000 : ℝ) ≤ (2565613521293 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1109473565119077 / 200000000000000 : ℝ) (594644259157 /
    500000000000 : ℝ) (2565613521293 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell475_denomLower :
    (2546622623653 / 10000000000 : ℝ) ≤ Real.exp (6924922757475979 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6924922757475979 / 1250000000000000 : ℝ) (47560497063 /
    40000000000 : ℝ) (2546622623653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell475_product_lower :
    (7110860257475979 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell475_leftExp
    (by norm_num : (0 : ℝ) ≤ (18107660721 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell475_product_upper :
    Real.pi * Real.exp (119 / 200 : ℝ) ≤ (1139161065119077 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell475_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell475_endpointLower :
    (7430001751 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 64 : ℝ) (119 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7110860257475979 / 1250000000000000 : ℝ) (Real.pi * Real.exp (19 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell475_product_lower
  have hD : Real.exp (Real.pi * Real.exp (119 / 200 : ℝ) - (19 / 128 : ℝ)) ≤
      (2565613521293 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell475_denomUpper
    linarith [hpThetaJensenCell475_product_upper]
  have hi : (1 / (2565613521293 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (119 / 200 : ℝ) - (19 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2565613521293 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2565613521293 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 128 : ℝ) - Real.pi * Real.exp (119 / 200 : ℝ)) := by
    rw [show (19 / 128 : ℝ) - Real.pi * Real.exp (119 / 200 : ℝ) =
      -(Real.pi * Real.exp (119 / 200 : ℝ) - (19 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 32 : ℝ)) := by
    have h := hpThetaJensenCell475_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2565613521293 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell475_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 64 : ℝ) (119 / 400 : ℝ) ≤ (940910029 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (119 / 200 : ℝ)) (1139161065119077 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (119 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell475_product_upper
  have hD : (2546622623653 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 32 : ℝ) - (119 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell475_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell475_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 32 : ℝ) - (119 / 800 : ℝ)) ≤
      (1 / (2546622623653 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2546622623653 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((119 / 800 : ℝ) - Real.pi * Real.exp (19 / 32 : ℝ)) ≤
      (2 / (2546622623653 / 10000000000 : ℝ) : ℝ) := by
    rw [show (119 / 800 : ℝ) - Real.pi * Real.exp (19 / 32 : ℝ) =
      -(Real.pi * Real.exp (19 / 32 : ℝ) - (119 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1139161065119077 / 200000000000000 : ℝ) ^ 2 - 6 *
      (1139161065119077 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell475_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 64 : ℝ) (119 / 400 : ℝ)) :
    (7430001751 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (940910029 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell475_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell475_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell476_leftExp :
    (18130309449 / 10000000000 : ℝ) ≤ Real.exp (119 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (119 / 200 : ℝ) (1018767690163 / 1000000000000 : ℝ)
    (18130309449 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell476_rightExp :
    Real.exp (477 / 800 : ℝ) ≤ (18152986507 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (477 / 800 : ℝ) (509403743277 / 500000000000 : ℝ)
    (18152986507 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell476_denomUpper :
    Real.exp (55541795339485651 / 10000000000000000 : ℝ) ≤ (2583149389181 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55541795339485651 / 10000000000000000 : ℝ) (237908340843
    / 200000000000 : ℝ) (2583149389181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell476_denomLower :
    (2564005864379 / 10000000000 : ℝ) ≤ Real.exp (6933426265312851 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6933426265312851 / 1250000000000000 : ℝ) (1189265222857
    / 1000000000000 : ℝ) (2564005864379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell476_product_lower :
    (7119754390312851 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (119 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell476_leftExp
    (by norm_num : (0 : ℝ) ≤ (18130309449 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell476_product_upper :
    Real.pi * Real.exp (477 / 800 : ℝ) ≤ (57029295339485651 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell476_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell476_endpointLower :
    (370067213 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (119 / 400 : ℝ) (477 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7119754390312851 / 1250000000000000 : ℝ) (Real.pi * Real.exp (119 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell476_product_lower
  have hD : Real.exp (Real.pi * Real.exp (477 / 800 : ℝ) - (119 / 800 : ℝ)) ≤
      (2583149389181 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell476_denomUpper
    linarith [hpThetaJensenCell476_product_upper]
  have hi : (1 / (2583149389181 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (477 / 800 : ℝ) - (119 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2583149389181 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2583149389181 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((119 / 800 : ℝ) - Real.pi * Real.exp (477 / 800 : ℝ)) := by
    rw [show (119 / 800 : ℝ) - Real.pi * Real.exp (477 / 800 : ℝ) =
      -(Real.pi * Real.exp (477 / 800 : ℝ) - (119 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (119 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (119 / 200 : ℝ)) := by
    have h := hpThetaJensenCell476_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2583149389181 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell476_endpointUpper :
    hpThetaJensenKernelEndpointUpper (119 / 400 : ℝ) (477 / 1600 : ℝ) ≤ (7498308601 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (477 / 800 : ℝ)) (57029295339485651 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (477 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell476_product_upper
  have hD : (2564005864379 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (119 / 200 : ℝ) - (477 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell476_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell476_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (119 / 200 : ℝ) - (477 / 3200 : ℝ)) ≤
      (1 / (2564005864379 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2564005864379 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((477 / 3200 : ℝ) - Real.pi * Real.exp (119 / 200 : ℝ)) ≤
      (2 / (2564005864379 / 10000000000 : ℝ) : ℝ) := by
    rw [show (477 / 3200 : ℝ) - Real.pi * Real.exp (119 / 200 : ℝ) =
      -(Real.pi * Real.exp (119 / 200 : ℝ) - (477 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57029295339485651 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (57029295339485651 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell476_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (119 / 400 : ℝ) (477 / 1600 : ℝ)) :
    (370067213 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7498308601 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell476_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell476_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell477_leftExp :
    (9076493253 / 5000000000 : ℝ) ≤ Real.exp (477 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (477 / 800 : ℝ) (1018807486553 / 1000000000000 : ℝ)
    (9076493253 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell477_rightExp :
    Real.exp (239 / 400 : ℝ) ≤ (2271961491 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (239 / 400 : ℝ) (1018847284499 / 1000000000000 : ℝ)
    (2271961491 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell477_denomUpper :
    Real.exp (6951250191395163 / 1250000000000000 : ℝ) ≤ (1300414144709 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6951250191395163 / 1250000000000000 : ℝ) (118979527533 /
    100000000000 : ℝ) (1300414144709 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell477_denomLower :
    (645382684529 / 2500000000 : ℝ) ≤ Real.exp (3470970448959847 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3470970448959847 / 625000000000000 : ℝ) (594759201857 /
    500000000000 : ℝ) (645382684529 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell477_product_lower :
    (3564329823959847 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (477 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell477_leftExp
    (by norm_num : (0 : ℝ) ≤ (9076493253 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell477_product_upper :
    Real.pi * Real.exp (239 / 400 : ℝ) ≤ (7137578316395163 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell477_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell477_endpointLower :
    (7372726013 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (477 / 1600 : ℝ) (239 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3564329823959847 / 625000000000000 : ℝ) (Real.pi * Real.exp (477 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell477_product_lower
  have hD : Real.exp (Real.pi * Real.exp (239 / 400 : ℝ) - (477 / 3200 : ℝ)) ≤
      (1300414144709 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell477_denomUpper
    linarith [hpThetaJensenCell477_product_upper]
  have hi : (1 / (1300414144709 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (239 / 400 : ℝ) - (477 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1300414144709 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1300414144709 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((477 / 3200 : ℝ) - Real.pi * Real.exp (239 / 400 : ℝ)) := by
    rw [show (477 / 3200 : ℝ) - Real.pi * Real.exp (239 / 400 : ℝ) =
      -(Real.pi * Real.exp (239 / 400 : ℝ) - (477 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (477 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (477 / 800 : ℝ)) := by
    have h := hpThetaJensenCell477_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1300414144709 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell477_endpointUpper :
    hpThetaJensenKernelEndpointUpper (477 / 1600 : ℝ) (239 / 800 : ℝ) ≤ (7469376351 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (239 / 400 : ℝ)) (7137578316395163 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (239 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell477_product_upper
  have hD : (645382684529 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (477 / 800 : ℝ) - (239 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell477_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell477_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (477 / 800 : ℝ) - (239 / 1600 : ℝ)) ≤
      (1 / (645382684529 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (645382684529 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((239 / 1600 : ℝ) - Real.pi * Real.exp (477 / 800 : ℝ)) ≤
      (2 / (645382684529 / 2500000000 : ℝ) : ℝ) := by
    rw [show (239 / 1600 : ℝ) - Real.pi * Real.exp (477 / 800 : ℝ) =
      -(Real.pi * Real.exp (477 / 800 : ℝ) - (239 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7137578316395163 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (7137578316395163 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell477_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (477 / 1600 : ℝ) (239 / 800 : ℝ)) :
    (7372726013 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7469376351 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell477_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell477_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell478_leftExp :
    (18175691927 / 10000000000 : ℝ) ≤ Real.exp (239 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (239 / 400 : ℝ) (509423642249 / 500000000000 : ℝ)
    (18175691927 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell478_rightExp :
    Real.exp (479 / 800 : ℝ) ≤ (18198425749 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (479 / 800 : ℝ) (509443541999 / 500000000000 : ℝ)
    (18198425749 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell478_denomUpper :
    Real.exp (55678296944078157 / 10000000000000000 : ℝ) ≤ (2618651546673 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55678296944078157 / 10000000000000000 : ℝ)
    (1190049232303 / 1000000000000 : ℝ) (2618651546673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell478_denomLower :
    (519839710893 / 2000000000 : ℝ) ≤ Real.exp (6950466669040973 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6950466669040973 / 1250000000000000 : ℝ) (1189771969777
    / 1000000000000 : ℝ) (519839710893 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell478_product_lower :
    (7137576044040973 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (239 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell478_leftExp
    (by norm_num : (0 : ℝ) ≤ (18175691927 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell478_product_upper :
    Real.pi * Real.exp (479 / 800 : ℝ) ≤ (57172046944078157 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell478_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell478_endpointLower :
    (367207367 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (239 / 800 : ℝ) (479 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7137576044040973 / 1250000000000000 : ℝ) (Real.pi * Real.exp (239 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell478_product_lower
  have hD : Real.exp (Real.pi * Real.exp (479 / 800 : ℝ) - (239 / 1600 : ℝ)) ≤
      (2618651546673 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell478_denomUpper
    linarith [hpThetaJensenCell478_product_upper]
  have hi : (1 / (2618651546673 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (479 / 800 : ℝ) - (239 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2618651546673 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2618651546673 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((239 / 1600 : ℝ) - Real.pi * Real.exp (479 / 800 : ℝ)) := by
    rw [show (239 / 1600 : ℝ) - Real.pi * Real.exp (479 / 800 : ℝ) =
      -(Real.pi * Real.exp (479 / 800 : ℝ) - (239 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (239 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (239 / 400 : ℝ)) := by
    have h := hpThetaJensenCell478_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2618651546673 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell478_endpointUpper :
    hpThetaJensenKernelEndpointUpper (239 / 800 : ℝ) (479 / 1600 : ℝ) ≤ (3720241909 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (479 / 800 : ℝ)) (57172046944078157 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (479 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell478_product_upper
  have hD : (519839710893 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (239 / 400 : ℝ) - (479 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell478_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell478_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (239 / 400 : ℝ) - (479 / 3200 : ℝ)) ≤
      (1 / (519839710893 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (519839710893 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((479 / 3200 : ℝ) - Real.pi * Real.exp (239 / 400 : ℝ)) ≤
      (2 / (519839710893 / 2000000000 : ℝ) : ℝ) := by
    rw [show (479 / 3200 : ℝ) - Real.pi * Real.exp (239 / 400 : ℝ) =
      -(Real.pi * Real.exp (239 / 400 : ℝ) - (479 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57172046944078157 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (57172046944078157 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell478_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (239 / 800 : ℝ) (479 / 1600 : ℝ)) :
    (367207367 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3720241909 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell478_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell478_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell479_leftExp :
    (18198425747 / 10000000000 : ℝ) ≤ Real.exp (479 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (479 / 800 : ℝ) (1018887083997 / 1000000000000 : ℝ)
    (18198425747 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell479_rightExp :
    Real.exp (3 / 5 : ℝ) ≤ (3644237601 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 5 : ℝ) (1018926885053 / 1000000000000 : ℝ)
    (3644237601 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell479_denomUpper :
    Real.exp (11149336337638393 / 2000000000000000 : ℝ) ≤ (2636620498339 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11149336337638393 / 2000000000000000 : ℝ) (1190303575767
    / 1000000000000 : ℝ) (2636620498339 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell479_denomLower :
    (2617010636491 / 10000000000 : ℝ) ≤ Real.exp (6959003592421153 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6959003592421153 / 1250000000000000 : ℝ) (1190025921679
    / 1000000000000 : ℝ) (2617010636491 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell479_product_lower :
    (7146503592421153 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (479 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell479_leftExp
    (by norm_num : (0 : ℝ) ≤ (18198425747 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell479_product_upper :
    Real.pi * Real.exp (3 / 5 : ℝ) ≤ (11448711337638393 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell479_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell479_endpointLower :
    (7315608569 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (479 / 1600 : ℝ) (3 / 10 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7146503592421153 / 1250000000000000 : ℝ) (Real.pi * Real.exp (479 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell479_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 5 : ℝ) - (479 / 3200 : ℝ)) ≤
      (2636620498339 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell479_denomUpper
    linarith [hpThetaJensenCell479_product_upper]
  have hi : (1 / (2636620498339 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 5 : ℝ) - (479 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2636620498339 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2636620498339 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((479 / 3200 : ℝ) - Real.pi * Real.exp (3 / 5 : ℝ)) := by
    rw [show (479 / 3200 : ℝ) - Real.pi * Real.exp (3 / 5 : ℝ) =
      -(Real.pi * Real.exp (3 / 5 : ℝ) - (479 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (479 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (479 / 800 : ℝ)) := by
    have h := hpThetaJensenCell479_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2636620498339 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell479_endpointUpper :
    hpThetaJensenKernelEndpointUpper (479 / 1600 : ℝ) (3 / 10 : ℝ) ≤ (1482326267 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 5 : ℝ)) (11448711337638393 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 10 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell479_product_upper
  have hD : (2617010636491 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (479 / 800 : ℝ) - (3 / 20 : ℝ)) := by
    apply le_trans hpThetaJensenCell479_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell479_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (479 / 800 : ℝ) - (3 / 20 : ℝ)) ≤
      (1 / (2617010636491 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2617010636491 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 20 : ℝ) - Real.pi * Real.exp (479 / 800 : ℝ)) ≤
      (2 / (2617010636491 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 20 : ℝ) - Real.pi * Real.exp (479 / 800 : ℝ) =
      -(Real.pi * Real.exp (479 / 800 : ℝ) - (3 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11448711337638393 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (11448711337638393 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell479_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (479 / 1600 : ℝ) (3 / 10 : ℝ)) :
    (7315608569 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1482326267 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell479_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell479_endpointUpper

def hpThetaJensenCellsBatch023Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3932171609 / 5000000000 : ℝ)
  | 1 => (313405517 / 400000000 : ℝ)
  | 2 => (7805966703 / 10000000000 : ℝ)
  | 3 => (3888414961 / 5000000000 : ℝ)
  | 4 => (7747727927 / 10000000000 : ℝ)
  | 5 => (3859330537 / 5000000000 : ℝ)
  | 6 => (480601857 / 625000000 : ℝ)
  | 7 => (1532126839 / 2000000000 : ℝ)
  | 8 => (1526334973 / 2000000000 : ℝ)
  | 9 => (3801376037 / 5000000000 : ℝ)
  | 10 => (1893466541 / 2500000000 : ℝ)
  | 11 => (3772508737 / 5000000000 : ℝ)
  | 12 => (7516206349 / 10000000000 : ℝ)
  | 13 => (748743313 / 1000000000 : ℝ)
  | 14 => (7458698151 / 10000000000 : ℝ)
  | 15 => (7430001751 / 10000000000 : ℝ)
  | 16 => (370067213 / 500000000 : ℝ)
  | 17 => (7372726013 / 10000000000 : ℝ)
  | 18 => (367207367 / 500000000 : ℝ)
  | 19 => (7315608569 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch023Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (796634737 / 1000000000 : ℝ)
  | 1 => (7936826389 / 10000000000 : ℝ)
  | 2 => (7907339563 / 10000000000 : ℝ)
  | 3 => (1969471811 / 2500000000 : ℝ)
  | 4 => (1962117449 / 2500000000 : ℝ)
  | 5 => (977385947 / 1250000000 : ℝ)
  | 6 => (7789740937 / 10000000000 : ℝ)
  | 7 => (1552086047 / 2000000000 : ℝ)
  | 8 => (483197239 / 625000000 : ℝ)
  | 9 => (240684939 / 312500000 : ℝ)
  | 10 => (383635863 / 500000000 : ℝ)
  | 11 => (764355381 / 1000000000 : ℝ)
  | 12 => (7614428039 / 10000000000 : ℝ)
  | 13 => (7585340291 / 10000000000 : ℝ)
  | 14 => (755629091 / 1000000000 : ℝ)
  | 15 => (940910029 / 1250000000 : ℝ)
  | 16 => (7498308601 / 10000000000 : ℝ)
  | 17 => (7469376351 / 10000000000 : ℝ)
  | 18 => (3720241909 / 5000000000 : ℝ)
  | 19 => (1482326267 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch023_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch023Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch023Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell460_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell461_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell462_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell463_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell464_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell465_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell466_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell467_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell468_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell469_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell470_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell471_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell472_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell473_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell474_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell475_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell476_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell477_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell478_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell479_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper] at h ⊢
    exact h

end HodgeProofHP
