import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell380_leftExp :
    (8040070987 / 5000000000 : ℝ) ≤ Real.exp (19 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 40 : ℝ) (101495446559 / 100000000000 : ℝ)
    (8040070987 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell380_rightExp :
    Real.exp (381 / 800 : ℝ) ≤ (16100254721 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (381 / 800 : ℝ) (1982410377 / 1953125000 : ℝ)
    (16100254721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell380_denomUpper :
    Real.exp (49392947529710553 / 10000000000000000 : ℝ) ≤ (698358558791 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49392947529710553 / 10000000000000000 : ℝ) (583451342637
    / 500000000000 : ℝ) (698358558791 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell380_denomLower :
    (346870936657 / 2500000000 : ℝ) ≤ Real.exp (3082913774023913 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3082913774023913 / 625000000000000 : ℝ) (11666608437 /
    10000000000 : ℝ) (346870936657 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell380_product_lower :
    (3157327836523913 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell380_leftExp
    (by norm_num : (0 : ℝ) ≤ (8040070987 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell380_product_upper :
    Real.pi * Real.exp (381 / 800 : ℝ) ≤ (50580447529710553 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell380_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell380_endpointLower :
    (10276860663 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 80 : ℝ) (381 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3157327836523913 / 625000000000000 : ℝ) (Real.pi * Real.exp (19 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell380_product_lower
  have hD : Real.exp (Real.pi * Real.exp (381 / 800 : ℝ) - (19 / 160 : ℝ)) ≤
      (698358558791 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell380_denomUpper
    linarith [hpThetaJensenCell380_product_upper]
  have hi : (1 / (698358558791 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (381 / 800 : ℝ) - (19 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (698358558791 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (698358558791 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 160 : ℝ) - Real.pi * Real.exp (381 / 800 : ℝ)) := by
    rw [show (19 / 160 : ℝ) - Real.pi * Real.exp (381 / 800 : ℝ) =
      -(Real.pi * Real.exp (381 / 800 : ℝ) - (19 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 40 : ℝ)) := by
    have h := hpThetaJensenCell380_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (698358558791 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell380_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 80 : ℝ) (381 / 1600 : ℝ) ≤ (32512353 / 31250000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (381 / 800 : ℝ)) (50580447529710553 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (381 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell380_product_upper
  have hD : (346870936657 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 40 : ℝ) - (381 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell380_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell380_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 40 : ℝ) - (381 / 3200 : ℝ)) ≤
      (1 / (346870936657 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (346870936657 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((381 / 3200 : ℝ) - Real.pi * Real.exp (19 / 40 : ℝ)) ≤
      (2 / (346870936657 / 2500000000 : ℝ) : ℝ) := by
    rw [show (381 / 3200 : ℝ) - Real.pi * Real.exp (19 / 40 : ℝ) =
      -(Real.pi * Real.exp (19 / 40 : ℝ) - (381 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50580447529710553 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50580447529710553 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell380_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 80 : ℝ) (381 / 1600 : ℝ)) :
    (10276860663 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32512353 / 31250000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell380_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell380_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell381_leftExp :
    (16100254719 / 10000000000 : ℝ) ≤ Real.exp (381 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (381 / 800 : ℝ) (1014994113023 / 1000000000000 : ℝ)
    (16100254719 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell381_rightExp :
    Real.exp (191 / 400 : ℝ) ≤ (16120392623 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (191 / 400 : ℝ) (507516881003 / 500000000000 : ℝ)
    (16120392623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell381_denomUpper :
    Real.exp (49453087621668439 / 10000000000000000 : ℝ) ≤ (351285574083 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49453087621668439 / 10000000000000000 : ℝ) (72945125687
    / 62500000000 : ℝ) (351285574083 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell381_denomLower :
    (1395842193863 / 10000000000 : ℝ) ≤ Real.exp (6173335177896581 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6173335177896581 / 1250000000000000 : ℝ) (233375967139 /
    200000000000 : ℝ) (1395842193863 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell381_product_lower :
    (6322553927896581 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (381 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell381_leftExp
    (by norm_num : (0 : ℝ) ≤ (16100254719 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell381_product_upper :
    Real.pi * Real.exp (191 / 400 : ℝ) ≤ (50643712621668439 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell381_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell381_endpointLower :
    (10246213931 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (381 / 1600 : ℝ) (191 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6322553927896581 / 1250000000000000 : ℝ) (Real.pi * Real.exp (381 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell381_product_lower
  have hD : Real.exp (Real.pi * Real.exp (191 / 400 : ℝ) - (381 / 3200 : ℝ)) ≤
      (351285574083 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell381_denomUpper
    linarith [hpThetaJensenCell381_product_upper]
  have hi : (1 / (351285574083 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (191 / 400 : ℝ) - (381 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (351285574083 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (351285574083 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((381 / 3200 : ℝ) - Real.pi * Real.exp (191 / 400 : ℝ)) := by
    rw [show (381 / 3200 : ℝ) - Real.pi * Real.exp (191 / 400 : ℝ) =
      -(Real.pi * Real.exp (191 / 400 : ℝ) - (381 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (381 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (381 / 800 : ℝ)) := by
    have h := hpThetaJensenCell381_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (351285574083 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell381_endpointUpper :
    hpThetaJensenKernelEndpointUpper (381 / 1600 : ℝ) (191 / 800 : ℝ) ≤ (10372999511 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (191 / 400 : ℝ)) (50643712621668439 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (191 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell381_product_upper
  have hD : (1395842193863 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (381 / 800 : ℝ) - (191 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell381_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell381_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (381 / 800 : ℝ) - (191 / 1600 : ℝ)) ≤
      (1 / (1395842193863 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1395842193863 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((191 / 1600 : ℝ) - Real.pi * Real.exp (381 / 800 : ℝ)) ≤
      (2 / (1395842193863 / 10000000000 : ℝ) : ℝ) := by
    rw [show (191 / 1600 : ℝ) - Real.pi * Real.exp (381 / 800 : ℝ) =
      -(Real.pi * Real.exp (381 / 800 : ℝ) - (191 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50643712621668439 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50643712621668439 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell381_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (381 / 1600 : ℝ) (191 / 800 : ℝ)) :
    (10246213931 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10372999511 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell381_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell381_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell382_leftExp :
    (16120392621 / 10000000000 : ℝ) ≤ Real.exp (191 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (191 / 400 : ℝ) (203006752401 / 200000000000 : ℝ)
    (16120392621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell382_rightExp :
    Real.exp (383 / 800 : ℝ) ≤ (16140555713 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (383 / 800 : ℝ) (1015073412537 / 1000000000000 : ℝ)
    (16140555713 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell382_denomUpper :
    Real.exp (49513306844070809 / 10000000000000000 : ℝ) ≤ (353407370733 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49513306844070809 / 10000000000000000 : ℝ)
    (1167341666597 / 1000000000000 : ℝ) (353407370733 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell382_denomLower :
    (702131046069 / 5000000000 : ℝ) ≤ Real.exp (6180852686874079 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6180852686874079 / 1250000000000000 : ℝ) (233419831409 /
    200000000000 : ℝ) (702131046069 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell382_product_lower :
    (6330462061874079 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (191 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell382_leftExp
    (by norm_num : (0 : ℝ) ≤ (16120392621 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell382_product_upper :
    Real.pi * Real.exp (383 / 800 : ℝ) ≤ (50707056844070809 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell382_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell382_endpointLower :
    (10215568189 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (191 / 800 : ℝ) (383 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6330462061874079 / 1250000000000000 : ℝ) (Real.pi * Real.exp (191 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell382_product_lower
  have hD : Real.exp (Real.pi * Real.exp (383 / 800 : ℝ) - (191 / 1600 : ℝ)) ≤
      (353407370733 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell382_denomUpper
    linarith [hpThetaJensenCell382_product_upper]
  have hi : (1 / (353407370733 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (383 / 800 : ℝ) - (191 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (353407370733 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (353407370733 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((191 / 1600 : ℝ) - Real.pi * Real.exp (383 / 800 : ℝ)) := by
    rw [show (191 / 1600 : ℝ) - Real.pi * Real.exp (383 / 800 : ℝ) =
      -(Real.pi * Real.exp (383 / 800 : ℝ) - (191 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (191 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (191 / 400 : ℝ)) := by
    have h := hpThetaJensenCell382_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (353407370733 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell382_endpointUpper :
    hpThetaJensenKernelEndpointUpper (191 / 800 : ℝ) (383 / 1600 : ℝ) ≤ (2068409351 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (383 / 800 : ℝ)) (50707056844070809 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (383 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell382_product_upper
  have hD : (702131046069 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (191 / 400 : ℝ) - (383 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell382_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell382_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (191 / 400 : ℝ) - (383 / 3200 : ℝ)) ≤
      (1 / (702131046069 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (702131046069 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((383 / 3200 : ℝ) - Real.pi * Real.exp (191 / 400 : ℝ)) ≤
      (2 / (702131046069 / 5000000000 : ℝ) : ℝ) := by
    rw [show (383 / 3200 : ℝ) - Real.pi * Real.exp (191 / 400 : ℝ) =
      -(Real.pi * Real.exp (191 / 400 : ℝ) - (383 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50707056844070809 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50707056844070809 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell382_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (191 / 800 : ℝ) (383 / 1600 : ℝ)) :
    (10215568189 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2068409351 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell382_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell382_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell383_leftExp :
    (252196183 / 156250000 : ℝ) ≤ Real.exp (383 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (383 / 800 : ℝ) (126884176567 / 125000000000 : ℝ)
    (252196183 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell383_rightExp :
    Real.exp (12 / 25 : ℝ) ≤ (16160744023 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12 / 25 : ℝ) (126889133077 / 125000000000 : ℝ)
    (16160744023 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell383_denomUpper :
    Real.exp (49573605297448639 / 10000000000000000 : ℝ) ≤ (284435840183 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49573605297448639 / 10000000000000000 : ℝ) (583780826313
    / 500000000000 : ℝ) (284435840183 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell383_denomLower :
    (1412743959791 / 10000000000 : ℝ) ≤ Real.exp (96693438867917 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (96693438867917 / 19531250000000 : ℝ) (583659404143 /
    500000000000 : ℝ) (1412743959791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell383_product_lower :
    (99037188867917 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (383 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell383_leftExp
    (by norm_num : (0 : ℝ) ≤ (252196183 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell383_product_upper :
    Real.pi * Real.exp (12 / 25 : ℝ) ≤ (50770480297448639 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell383_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell383_endpointLower :
    (1273115487 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (383 / 1600 : ℝ) (6 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (99037188867917 / 19531250000000 : ℝ) (Real.pi * Real.exp (383 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell383_product_lower
  have hD : Real.exp (Real.pi * Real.exp (12 / 25 : ℝ) - (383 / 3200 : ℝ)) ≤
      (284435840183 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell383_denomUpper
    linarith [hpThetaJensenCell383_product_upper]
  have hi : (1 / (284435840183 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (12 / 25 : ℝ) - (383 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (284435840183 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (284435840183 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((383 / 3200 : ℝ) - Real.pi * Real.exp (12 / 25 : ℝ)) := by
    rw [show (383 / 3200 : ℝ) - Real.pi * Real.exp (12 / 25 : ℝ) =
      -(Real.pi * Real.exp (12 / 25 : ℝ) - (383 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (383 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (383 / 800 : ℝ)) := by
    have h := hpThetaJensenCell383_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (284435840183 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell383_endpointUpper :
    hpThetaJensenKernelEndpointUpper (383 / 1600 : ℝ) (6 / 25 : ℝ) ≤ (5155547577 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (12 / 25 : ℝ)) (50770480297448639 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (6 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell383_product_upper
  have hD : (1412743959791 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (383 / 800 : ℝ) - (3 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell383_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell383_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (383 / 800 : ℝ) - (3 / 25 : ℝ)) ≤
      (1 / (1412743959791 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1412743959791 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 25 : ℝ) - Real.pi * Real.exp (383 / 800 : ℝ)) ≤
      (2 / (1412743959791 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 25 : ℝ) - Real.pi * Real.exp (383 / 800 : ℝ) =
      -(Real.pi * Real.exp (383 / 800 : ℝ) - (3 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50770480297448639 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50770480297448639 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell383_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (383 / 1600 : ℝ) (6 / 25 : ℝ)) :
    (1273115487 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5155547577 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell383_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell383_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell384_leftExp :
    (16160744021 / 10000000000 : ℝ) ≤ Real.exp (12 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12 / 25 : ℝ) (203022612923 / 200000000000 : ℝ)
    (16160744021 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell384_rightExp :
    Real.exp (77 / 160 : ℝ) ≤ (1011309849 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 160 : ℝ) (203030543649 / 200000000000 : ℝ)
    (1011309849 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell384_denomUpper :
    Real.exp (3102123942449457 / 625000000000000 : ℝ) ≤ (286158395663 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3102123942449457 / 625000000000000 : ℝ) (583890984803 /
    500000000000 : ℝ) (286158395663 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell384_denomLower :
    (1421288318791 / 10000000000 : ℝ) ≤ Real.exp (6195917391302679 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6195917391302679 / 1250000000000000 : ℝ) (1167538789923
    / 1000000000000 : ℝ) (1421288318791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell384_product_lower :
    (6346308016302679 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (12 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell384_leftExp
    (by norm_num : (0 : ℝ) ≤ (16160744021 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell384_product_upper :
    Real.pi * Real.exp (77 / 160 : ℝ) ≤ (3177123942449457 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell384_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell384_endpointLower :
    (2538570377 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (6 / 25 : ℝ) (77 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6346308016302679 / 1250000000000000 : ℝ) (Real.pi * Real.exp (12 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell384_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 160 : ℝ) - (3 / 25 : ℝ)) ≤
      (286158395663 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell384_denomUpper
    linarith [hpThetaJensenCell384_product_upper]
  have hi : (1 / (286158395663 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 160 : ℝ) - (3 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (286158395663 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (286158395663 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 25 : ℝ) - Real.pi * Real.exp (77 / 160 : ℝ)) := by
    rw [show (3 / 25 : ℝ) - Real.pi * Real.exp (77 / 160 : ℝ) =
      -(Real.pi * Real.exp (77 / 160 : ℝ) - (3 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (12 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (12 / 25 : ℝ)) := by
    have h := hpThetaJensenCell384_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (286158395663 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell384_endpointUpper :
    hpThetaJensenKernelEndpointUpper (6 / 25 : ℝ) (77 / 320 : ℝ) ≤ (514007259 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 160 : ℝ)) (3177123942449457 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell384_product_upper
  have hD : (1421288318791 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (12 / 25 : ℝ) - (77 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell384_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell384_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (12 / 25 : ℝ) - (77 / 640 : ℝ)) ≤
      (1 / (1421288318791 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1421288318791 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 640 : ℝ) - Real.pi * Real.exp (12 / 25 : ℝ)) ≤
      (2 / (1421288318791 / 10000000000 : ℝ) : ℝ) := by
    rw [show (77 / 640 : ℝ) - Real.pi * Real.exp (12 / 25 : ℝ) =
      -(Real.pi * Real.exp (12 / 25 : ℝ) - (77 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3177123942449457 / 625000000000000 : ℝ) ^ 2 - 6 *
      (3177123942449457 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell384_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (6 / 25 : ℝ) (77 / 320 : ℝ)) :
    (2538570377 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (514007259 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell384_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell384_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell385_leftExp :
    (8090478791 / 5000000000 : ℝ) ≤ Real.exp (77 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 160 : ℝ) (253788179561 / 250000000000 : ℝ)
    (8090478791 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell385_rightExp :
    Real.exp (193 / 400 : ℝ) ≤ (16201196427 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (193 / 400 : ℝ) (507596186711 / 500000000000 : ℝ)
    (16201196427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell385_denomUpper :
    Real.exp (49694440286688211 / 10000000000000000 : ℝ) ≤ (719734174049 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49694440286688211 / 10000000000000000 : ℝ) (73000163629
    / 62500000000 : ℝ) (719734174049 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell385_denomLower :
    (714947849039 / 5000000000 : ℝ) ≤ Real.exp (3101732305746909 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3101732305746909 / 625000000000000 : ℝ) (233551820503 /
    200000000000 : ℝ) (714947849039 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell385_product_lower :
    (3177122930746909 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell385_leftExp
    (by norm_num : (0 : ℝ) ≤ (8090478791 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell385_product_upper :
    Real.pi * Real.exp (193 / 400 : ℝ) ≤ (50897565286688211 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell385_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell385_endpointLower :
    (1012364149 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 320 : ℝ) (193 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3177122930746909 / 625000000000000 : ℝ) (Real.pi * Real.exp (77 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell385_product_lower
  have hD : Real.exp (Real.pi * Real.exp (193 / 400 : ℝ) - (77 / 640 : ℝ)) ≤
      (719734174049 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell385_denomUpper
    linarith [hpThetaJensenCell385_product_upper]
  have hi : (1 / (719734174049 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (193 / 400 : ℝ) - (77 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (719734174049 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (719734174049 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 640 : ℝ) - Real.pi * Real.exp (193 / 400 : ℝ)) := by
    rw [show (77 / 640 : ℝ) - Real.pi * Real.exp (193 / 400 : ℝ) =
      -(Real.pi * Real.exp (193 / 400 : ℝ) - (77 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 160 : ℝ)) := by
    have h := hpThetaJensenCell385_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (719734174049 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell385_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 320 : ℝ) (193 / 800 : ℝ) ≤ (10249197287 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (193 / 400 : ℝ)) (50897565286688211 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (193 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell385_product_upper
  have hD : (714947849039 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 160 : ℝ) - (193 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell385_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell385_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 160 : ℝ) - (193 / 1600 : ℝ)) ≤
      (1 / (714947849039 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (714947849039 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((193 / 1600 : ℝ) - Real.pi * Real.exp (77 / 160 : ℝ)) ≤
      (2 / (714947849039 / 5000000000 : ℝ) : ℝ) := by
    rw [show (193 / 1600 : ℝ) - Real.pi * Real.exp (77 / 160 : ℝ) =
      -(Real.pi * Real.exp (77 / 160 : ℝ) - (193 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50897565286688211 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50897565286688211 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell385_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 320 : ℝ) (193 / 800 : ℝ)) :
    (1012364149 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10249197287 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell385_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell385_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell386_leftExp :
    (648047857 / 400000000 : ℝ) ≤ Real.exp (193 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (193 / 400 : ℝ) (1015192373421 / 1000000000000 : ℝ)
    (648047857 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell386_rightExp :
    Real.exp (387 / 800 : ℝ) ≤ (3244292117 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (387 / 800 : ℝ) (1015232030149 / 1000000000000 : ℝ)
    (3244292117 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell386_denomUpper :
    Real.exp (9950995404722381 / 2000000000000000 : ℝ) ≤ (9051305307 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9950995404722381 / 2000000000000000 : ℝ) (23364471971 /
    20000000000 : ℝ) (9051305307 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell386_denomLower :
    (1438566629857 / 10000000000 : ℝ) ≤ Real.exp (248440870396043 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (248440870396043 / 50000000000000 : ℝ) (583989873289 /
    500000000000 : ℝ) (1438566629857 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell386_product_lower :
    (254487745396043 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (193 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell386_leftExp
    (by norm_num : (0 : ℝ) ≤ (648047857 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell386_product_upper :
    Real.pi * Real.exp (387 / 800 : ℝ) ≤ (10192245404722381 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell386_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell386_endpointLower :
    (10093004291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (193 / 800 : ℝ) (387 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (254487745396043 / 50000000000000 : ℝ) (Real.pi * Real.exp (193 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell386_product_lower
  have hD : Real.exp (Real.pi * Real.exp (387 / 800 : ℝ) - (193 / 1600 : ℝ)) ≤
      (9051305307 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell386_denomUpper
    linarith [hpThetaJensenCell386_product_upper]
  have hi : (1 / (9051305307 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (387 / 800 : ℝ) - (193 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9051305307 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9051305307 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((193 / 1600 : ℝ) - Real.pi * Real.exp (387 / 800 : ℝ)) := by
    rw [show (193 / 1600 : ℝ) - Real.pi * Real.exp (387 / 800 : ℝ) =
      -(Real.pi * Real.exp (387 / 800 : ℝ) - (193 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (193 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (193 / 400 : ℝ)) := by
    have h := hpThetaJensenCell386_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9051305307 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell386_endpointUpper :
    hpThetaJensenKernelEndpointUpper (193 / 800 : ℝ) (387 / 1600 : ℝ) ≤ (10218251943 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (387 / 800 : ℝ)) (10192245404722381 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (387 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell386_product_upper
  have hD : (1438566629857 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (193 / 400 : ℝ) - (387 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell386_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell386_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (193 / 400 : ℝ) - (387 / 3200 : ℝ)) ≤
      (1 / (1438566629857 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1438566629857 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((387 / 3200 : ℝ) - Real.pi * Real.exp (193 / 400 : ℝ)) ≤
      (2 / (1438566629857 / 10000000000 : ℝ) : ℝ) := by
    rw [show (387 / 3200 : ℝ) - Real.pi * Real.exp (193 / 400 : ℝ) =
      -(Real.pi * Real.exp (193 / 400 : ℝ) - (387 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10192245404722381 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (10192245404722381 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell386_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (193 / 800 : ℝ) (387 / 1600 : ℝ)) :
    (10093004291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10218251943 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell386_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell386_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell387_leftExp :
    (2027682573 / 1250000000 : ℝ) ≤ Real.exp (387 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (387 / 800 : ℝ) (253808007537 / 250000000000 : ℝ)
    (2027682573 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell387_rightExp :
    Real.exp (97 / 200 : ℝ) ≤ (16241750089 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97 / 200 : ℝ) (40610867537 / 40000000000 : ℝ)
    (16241750089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell387_denomUpper :
    Real.exp (49815593387351777 / 10000000000000000 : ℝ) ≤ (91063376531 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49815593387351777 / 10000000000000000 : ℝ) (584222455797
    / 500000000000 : ℝ) (91063376531 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell387_denomLower :
    (361825413291 / 2500000000 : ℝ) ≤ Real.exp (777323606234527 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (777323606234527 / 156250000000000 : ℝ) (46728028907 /
    40000000000 : ℝ) (361825413291 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell387_product_lower :
    (796268918734527 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (387 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell387_leftExp
    (by norm_num : (0 : ℝ) ≤ (2027682573 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell387_product_upper :
    Real.pi * Real.exp (97 / 200 : ℝ) ≤ (51024968387351777 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell387_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell387_endpointLower :
    (2515592593 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (387 / 1600 : ℝ) (97 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (796268918734527 / 156250000000000 : ℝ) (Real.pi * Real.exp (387 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell387_product_lower
  have hD : Real.exp (Real.pi * Real.exp (97 / 200 : ℝ) - (387 / 3200 : ℝ)) ≤
      (91063376531 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell387_denomUpper
    linarith [hpThetaJensenCell387_product_upper]
  have hi : (1 / (91063376531 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (97 / 200 : ℝ) - (387 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (91063376531 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (91063376531 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((387 / 3200 : ℝ) - Real.pi * Real.exp (97 / 200 : ℝ)) := by
    rw [show (387 / 3200 : ℝ) - Real.pi * Real.exp (97 / 200 : ℝ) =
      -(Real.pi * Real.exp (97 / 200 : ℝ) - (387 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (387 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (387 / 800 : ℝ)) := by
    have h := hpThetaJensenCell387_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (91063376531 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell387_endpointUpper :
    hpThetaJensenKernelEndpointUpper (387 / 1600 : ℝ) (97 / 400 : ℝ) ≤ (12734137 / 12500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (97 / 200 : ℝ)) (51024968387351777 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (97 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell387_product_upper
  have hD : (361825413291 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (387 / 800 : ℝ) - (97 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell387_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell387_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (387 / 800 : ℝ) - (97 / 800 : ℝ)) ≤
      (1 / (361825413291 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (361825413291 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((97 / 800 : ℝ) - Real.pi * Real.exp (387 / 800 : ℝ)) ≤
      (2 / (361825413291 / 2500000000 : ℝ) : ℝ) := by
    rw [show (97 / 800 : ℝ) - Real.pi * Real.exp (387 / 800 : ℝ) =
      -(Real.pi * Real.exp (387 / 800 : ℝ) - (97 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51024968387351777 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (51024968387351777 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell387_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (387 / 1600 : ℝ) (97 / 400 : ℝ)) :
    (2515592593 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12734137 / 12500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell387_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell387_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell388_leftExp :
    (2030218761 / 1250000000 : ℝ) ≤ Real.exp (97 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (97 / 200 : ℝ) (126908961053 / 125000000000 : ℝ)
    (2030218761 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell388_rightExp :
    Real.exp (389 / 800 : ℝ) ≤ (16262064971 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (389 / 800 : ℝ) (4061245393 / 4000000000 : ℝ)
    (16262064971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell388_denomUpper :
    Real.exp (49876289478438803 / 10000000000000000 : ℝ) ≤ (732942211393 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49876289478438803 / 10000000000000000 : ℝ) (233733311547
    / 200000000000 : ℝ) (732942211393 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell388_denomLower :
    (291220261957 / 2000000000 : ℝ) ≤ Real.exp (778270736600939 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (778270736600939 / 156250000000000 : ℝ) (1168422031311 /
    1000000000000 : ℝ) (291220261957 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell388_product_lower :
    (797264877225939 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (97 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell388_leftExp
    (by norm_num : (0 : ℝ) ≤ (2030218761 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell388_product_upper :
    Real.pi * Real.exp (389 / 800 : ℝ) ≤ (51088789478438803 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell388_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell388_endpointLower :
    (2006348037 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 400 : ℝ) (389 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (797264877225939 / 156250000000000 : ℝ) (Real.pi * Real.exp (97 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell388_product_lower
  have hD : Real.exp (Real.pi * Real.exp (389 / 800 : ℝ) - (97 / 800 : ℝ)) ≤
      (732942211393 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell388_denomUpper
    linarith [hpThetaJensenCell388_product_upper]
  have hi : (1 / (732942211393 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (389 / 800 : ℝ) - (97 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (732942211393 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (732942211393 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((97 / 800 : ℝ) - Real.pi * Real.exp (389 / 800 : ℝ)) := by
    rw [show (97 / 800 : ℝ) - Real.pi * Real.exp (389 / 800 : ℝ) =
      -(Real.pi * Real.exp (389 / 800 : ℝ) - (97 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (97 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (97 / 200 : ℝ)) := by
    have h := hpThetaJensenCell388_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (732942211393 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell388_endpointUpper :
    hpThetaJensenKernelEndpointUpper (97 / 400 : ℝ) (389 / 1600 : ℝ) ≤ (10156370727 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (389 / 800 : ℝ)) (51088789478438803 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (389 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell388_product_upper
  have hD : (291220261957 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (97 / 200 : ℝ) - (389 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell388_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell388_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (97 / 200 : ℝ) - (389 / 3200 : ℝ)) ≤
      (1 / (291220261957 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (291220261957 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((389 / 3200 : ℝ) - Real.pi * Real.exp (97 / 200 : ℝ)) ≤
      (2 / (291220261957 / 2000000000 : ℝ) : ℝ) := by
    rw [show (389 / 3200 : ℝ) - Real.pi * Real.exp (97 / 200 : ℝ) =
      -(Real.pi * Real.exp (97 / 200 : ℝ) - (389 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51088789478438803 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (51088789478438803 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell388_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (97 / 400 : ℝ) (389 / 1600 : ℝ)) :
    (2006348037 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10156370727 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell388_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell388_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell389_leftExp :
    (1626206497 / 1000000000 : ℝ) ≤ Real.exp (389 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (389 / 800 : ℝ) (1015311348249 / 1000000000000 : ℝ)
    (1626206497 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell389_rightExp :
    Real.exp (39 / 80 : ℝ) ≤ (8141202631 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 80 : ℝ) (126918876203 / 125000000000 : ℝ)
    (8141202631 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell389_denomUpper :
    Real.exp (24968532697131183 / 5000000000000000 : ℝ) ≤ (1474820597293 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (24968532697131183 / 5000000000000000 : ℝ) (584444268751
    / 500000000000 : ℝ) (1474820597293 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell389_denomLower :
    (183120768551 / 1250000000 : ℝ) ≤ Real.exp (623375290165403 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (623375290165403 / 125000000000000 : ℝ) (1168643673037 /
    1000000000000 : ℝ) (183120768551 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell389_product_lower :
    (638609665165403 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (389 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell389_leftExp
    (by norm_num : (0 : ℝ) ≤ (1626206497 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell389_product_upper :
    Real.pi * Real.exp (39 / 80 : ℝ) ≤ (25576345197131183 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell389_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell389_endpointLower :
    (10001114189 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (389 / 1600 : ℝ) (39 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (638609665165403 / 125000000000000 : ℝ) (Real.pi * Real.exp (389 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell389_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 80 : ℝ) - (389 / 3200 : ℝ)) ≤
      (1474820597293 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell389_denomUpper
    linarith [hpThetaJensenCell389_product_upper]
  have hi : (1 / (1474820597293 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 80 : ℝ) - (389 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1474820597293 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1474820597293 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((389 / 3200 : ℝ) - Real.pi * Real.exp (39 / 80 : ℝ)) := by
    rw [show (389 / 3200 : ℝ) - Real.pi * Real.exp (39 / 80 : ℝ) =
      -(Real.pi * Real.exp (39 / 80 : ℝ) - (389 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (389 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (389 / 800 : ℝ)) := by
    have h := hpThetaJensenCell389_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1474820597293 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell389_endpointUpper :
    hpThetaJensenKernelEndpointUpper (389 / 1600 : ℝ) (39 / 160 : ℝ) ≤ (10125435779 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 80 : ℝ)) (25576345197131183 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell389_product_upper
  have hD : (183120768551 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (389 / 800 : ℝ) - (39 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell389_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell389_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (389 / 800 : ℝ) - (39 / 320 : ℝ)) ≤
      (1 / (183120768551 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (183120768551 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 320 : ℝ) - Real.pi * Real.exp (389 / 800 : ℝ)) ≤
      (2 / (183120768551 / 1250000000 : ℝ) : ℝ) := by
    rw [show (39 / 320 : ℝ) - Real.pi * Real.exp (389 / 800 : ℝ) =
      -(Real.pi * Real.exp (389 / 800 : ℝ) - (39 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25576345197131183 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (25576345197131183 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell389_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (389 / 1600 : ℝ) (39 / 160 : ℝ)) :
    (10001114189 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10125435779 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell389_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell389_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell390_leftExp :
    (16282405261 / 10000000000 : ℝ) ≤ Real.exp (39 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 80 : ℝ) (1015351009623 / 1000000000000 : ℝ)
    (16282405261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell390_rightExp :
    Real.exp (391 / 800 : ℝ) ≤ (3260554199 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (391 / 800 : ℝ) (1015390672547 / 1000000000000 : ℝ)
    (3260554199 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell390_denomUpper :
    Real.exp (9999584247699007 / 2000000000000000 : ℝ) ≤ (296764621513 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9999584247699007 / 2000000000000000 : ℝ) (23382217029 /
    20000000000 : ℝ) (296764621513 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell390_denomLower :
    (1473896722071 / 10000000000 : ℝ) ≤ Real.exp (6241349888589439 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6241349888589439 / 1250000000000000 : ℝ) (4565881439 /
    3906250000 : ℝ) (1473896722071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell390_product_lower :
    (6394084263589439 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell390_leftExp
    (by norm_num : (0 : ℝ) ≤ (16282405261 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell390_product_upper :
    Real.pi * Real.exp (391 / 800 : ℝ) ≤ (10243334247699007 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell390_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell390_endpointLower :
    (9970492829 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 160 : ℝ) (391 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6394084263589439 / 1250000000000000 : ℝ) (Real.pi * Real.exp (39 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell390_product_lower
  have hD : Real.exp (Real.pi * Real.exp (391 / 800 : ℝ) - (39 / 320 : ℝ)) ≤
      (296764621513 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell390_denomUpper
    linarith [hpThetaJensenCell390_product_upper]
  have hi : (1 / (296764621513 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (391 / 800 : ℝ) - (39 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (296764621513 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (296764621513 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 320 : ℝ) - Real.pi * Real.exp (391 / 800 : ℝ)) := by
    rw [show (39 / 320 : ℝ) - Real.pi * Real.exp (391 / 800 : ℝ) =
      -(Real.pi * Real.exp (391 / 800 : ℝ) - (39 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 80 : ℝ)) := by
    have h := hpThetaJensenCell390_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (296764621513 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell390_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 160 : ℝ) (391 / 1600 : ℝ) ≤ (39431661 / 39062500 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (391 / 800 : ℝ)) (10243334247699007 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (391 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell390_product_upper
  have hD : (1473896722071 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 80 : ℝ) - (391 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell390_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell390_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 80 : ℝ) - (391 / 3200 : ℝ)) ≤
      (1 / (1473896722071 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1473896722071 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((391 / 3200 : ℝ) - Real.pi * Real.exp (39 / 80 : ℝ)) ≤
      (2 / (1473896722071 / 10000000000 : ℝ) : ℝ) := by
    rw [show (391 / 3200 : ℝ) - Real.pi * Real.exp (39 / 80 : ℝ) =
      -(Real.pi * Real.exp (39 / 80 : ℝ) - (391 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10243334247699007 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (10243334247699007 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell390_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 160 : ℝ) (391 / 1600 : ℝ)) :
    (9970492829 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (39431661 / 39062500 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell390_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell390_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell391_leftExp :
    (16302770993 / 10000000000 : ℝ) ≤ Real.exp (391 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (391 / 800 : ℝ) (507695336273 / 500000000000 : ℝ)
    (16302770993 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell391_rightExp :
    Real.exp (49 / 100 : ℝ) ≤ (81615811 / 50000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 100 : ℝ) (50771516851 / 50000000000 : ℝ)
    (81615811 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell391_denomUpper :
    Real.exp (250294285526923 / 50000000000000 : ℝ) ≤ (746446258411 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (250294285526923 / 50000000000000 : ℝ) (233866700019 /
    200000000000 : ℝ) (746446258411 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell391_denomLower :
    (741446794681 / 5000000000 : ℝ) ≤ Real.exp (6248956866180107 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6248956866180107 / 1250000000000000 : ℝ) (292271989473 /
    250000000000 : ℝ) (741446794681 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell391_product_lower :
    (6402081866180107 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (391 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell391_leftExp
    (by norm_num : (0 : ℝ) ≤ (16302770993 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell391_product_upper :
    Real.pi * Real.exp (49 / 100 : ℝ) ≤ (256403660526923 / 50000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell391_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell391_endpointLower :
    (9939876567 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (391 / 1600 : ℝ) (49 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6402081866180107 / 1250000000000000 : ℝ) (Real.pi * Real.exp (391 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell391_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 100 : ℝ) - (391 / 3200 : ℝ)) ≤
      (746446258411 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell391_denomUpper
    linarith [hpThetaJensenCell391_product_upper]
  have hi : (1 / (746446258411 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 100 : ℝ) - (391 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (746446258411 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (746446258411 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((391 / 3200 : ℝ) - Real.pi * Real.exp (49 / 100 : ℝ)) := by
    rw [show (391 / 3200 : ℝ) - Real.pi * Real.exp (49 / 100 : ℝ) =
      -(Real.pi * Real.exp (49 / 100 : ℝ) - (391 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (391 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (391 / 800 : ℝ)) := by
    have h := hpThetaJensenCell391_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (746446258411 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell391_endpointUpper :
    hpThetaJensenKernelEndpointUpper (391 / 1600 : ℝ) (49 / 200 : ℝ) ≤ (2515894873 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 100 : ℝ)) (256403660526923 / 50000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell391_product_upper
  have hD : (741446794681 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (391 / 800 : ℝ) - (49 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell391_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell391_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (391 / 800 : ℝ) - (49 / 400 : ℝ)) ≤
      (1 / (741446794681 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (741446794681 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 400 : ℝ) - Real.pi * Real.exp (391 / 800 : ℝ)) ≤
      (2 / (741446794681 / 5000000000 : ℝ) : ℝ) := by
    rw [show (49 / 400 : ℝ) - Real.pi * Real.exp (391 / 800 : ℝ) =
      -(Real.pi * Real.exp (391 / 800 : ℝ) - (49 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (256403660526923 / 50000000000000 : ℝ) ^ 2 - 6 *
      (256403660526923 / 50000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell391_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (391 / 1600 : ℝ) (49 / 200 : ℝ)) :
    (9939876567 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2515894873 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell391_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell391_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell392_leftExp :
    (16323162199 / 10000000000 : ℝ) ≤ Real.exp (49 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 100 : ℝ) (1015430337019 / 1000000000000 : ℝ)
    (16323162199 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell392_rightExp :
    Real.exp (393 / 800 : ℝ) ≤ (16343578911 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (393 / 800 : ℝ) (507735001521 / 500000000000 : ℝ)
    (16343578911 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell392_denomUpper :
    Real.exp (50119873101745223 / 10000000000000000 : ℝ) ≤ (751014697853 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (50119873101745223 / 10000000000000000 : ℝ) (233911296801
    / 200000000000 : ℝ) (751014697853 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell392_denomLower :
    (372989328673 / 2500000000 : ℝ) ≤ Real.exp (6256573847385101 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6256573847385101 / 1250000000000000 : ℝ) (233862120423 /
    200000000000 : ℝ) (372989328673 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell392_product_lower :
    (6410089472385101 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell392_leftExp
    (by norm_num : (0 : ℝ) ≤ (16323162199 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell392_product_upper :
    Real.pi * Real.exp (393 / 800 : ℝ) ≤ (51344873101745223 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell392_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell392_endpointLower :
    (9909265847 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 200 : ℝ) (393 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6410089472385101 / 1250000000000000 : ℝ) (Real.pi * Real.exp (49 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell392_product_lower
  have hD : Real.exp (Real.pi * Real.exp (393 / 800 : ℝ) - (49 / 400 : ℝ)) ≤
      (751014697853 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell392_denomUpper
    linarith [hpThetaJensenCell392_product_upper]
  have hi : (1 / (751014697853 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (393 / 800 : ℝ) - (49 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (751014697853 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (751014697853 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 400 : ℝ) - Real.pi * Real.exp (393 / 800 : ℝ)) := by
    rw [show (49 / 400 : ℝ) - Real.pi * Real.exp (393 / 800 : ℝ) =
      -(Real.pi * Real.exp (393 / 800 : ℝ) - (49 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 100 : ℝ)) := by
    have h := hpThetaJensenCell392_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (751014697853 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell392_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 200 : ℝ) (393 / 1600 : ℝ) ≤ (1254082383 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (393 / 800 : ℝ)) (51344873101745223 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (393 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell392_product_upper
  have hD : (372989328673 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 100 : ℝ) - (393 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell392_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell392_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 100 : ℝ) - (393 / 3200 : ℝ)) ≤
      (1 / (372989328673 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (372989328673 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((393 / 3200 : ℝ) - Real.pi * Real.exp (49 / 100 : ℝ)) ≤
      (2 / (372989328673 / 2500000000 : ℝ) : ℝ) := by
    rw [show (393 / 3200 : ℝ) - Real.pi * Real.exp (49 / 100 : ℝ) =
      -(Real.pi * Real.exp (49 / 100 : ℝ) - (393 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51344873101745223 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (51344873101745223 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell392_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 200 : ℝ) (393 / 1600 : ℝ)) :
    (9909265847 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1254082383 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell392_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell392_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell393_leftExp :
    (16343578909 / 10000000000 : ℝ) ≤ Real.exp (393 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (393 / 800 : ℝ) (1015470003041 / 1000000000000 : ℝ)
    (16343578909 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell393_rightExp :
    Real.exp (197 / 400 : ℝ) ≤ (8182010579 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (197 / 400 : ℝ) (507754835307 / 500000000000 : ℝ)
    (8182010579 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell393_denomUpper :
    Real.exp (25090484660912347 / 5000000000000000 : ℝ) ≤ (1511234318219 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25090484660912347 / 5000000000000000 : ℝ) (1169779803699
    / 1000000000000 : ℝ) (1511234318219 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell393_denomLower :
    (1501088466349 / 10000000000 : ℝ) ≤ Real.exp (6264200843985391 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6264200843985391 / 1250000000000000 : ℝ) (292383395393 /
    250000000000 : ℝ) (1501088466349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell393_product_lower :
    (6418107093985391 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (393 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell393_leftExp
    (by norm_num : (0 : ℝ) ≤ (16343578909 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell393_product_upper :
    Real.pi * Real.exp (197 / 400 : ℝ) ≤ (25704547160912347 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell393_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell393_endpointLower :
    (2469665281 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (393 / 1600 : ℝ) (197 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6418107093985391 / 1250000000000000 : ℝ) (Real.pi * Real.exp (393 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell393_product_lower
  have hD : Real.exp (Real.pi * Real.exp (197 / 400 : ℝ) - (393 / 3200 : ℝ)) ≤
      (1511234318219 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell393_denomUpper
    linarith [hpThetaJensenCell393_product_upper]
  have hi : (1 / (1511234318219 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (197 / 400 : ℝ) - (393 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1511234318219 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1511234318219 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((393 / 3200 : ℝ) - Real.pi * Real.exp (197 / 400 : ℝ)) := by
    rw [show (393 / 3200 : ℝ) - Real.pi * Real.exp (197 / 400 : ℝ) =
      -(Real.pi * Real.exp (197 / 400 : ℝ) - (393 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (393 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (393 / 800 : ℝ)) := by
    have h := hpThetaJensenCell393_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1511234318219 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell393_endpointUpper :
    hpThetaJensenKernelEndpointUpper (393 / 1600 : ℝ) (197 / 800 : ℝ) ≤ (2500436097 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (197 / 400 : ℝ)) (25704547160912347 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (197 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell393_product_upper
  have hD : (1501088466349 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (393 / 800 : ℝ) - (197 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell393_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell393_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (393 / 800 : ℝ) - (197 / 1600 : ℝ)) ≤
      (1 / (1501088466349 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1501088466349 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((197 / 1600 : ℝ) - Real.pi * Real.exp (393 / 800 : ℝ)) ≤
      (2 / (1501088466349 / 10000000000 : ℝ) : ℝ) := by
    rw [show (197 / 1600 : ℝ) - Real.pi * Real.exp (393 / 800 : ℝ) =
      -(Real.pi * Real.exp (393 / 800 : ℝ) - (197 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25704547160912347 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (25704547160912347 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell393_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (393 / 1600 : ℝ) (197 / 800 : ℝ)) :
    (2469665281 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2500436097 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell393_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell393_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell394_leftExp :
    (16364021157 / 10000000000 : ℝ) ≤ Real.exp (197 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (197 / 400 : ℝ) (1015509670613 / 1000000000000 : ℝ)
    (16364021157 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell394_rightExp :
    Real.exp (79 / 160 : ℝ) ≤ (8192244487 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 160 : ℝ) (203109867947 / 200000000000 : ℝ)
    (8192244487 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell394_denomUpper :
    Real.exp (25121072934647791 / 5000000000000000 : ℝ) ≤ (1520507865297 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25121072934647791 / 5000000000000000 : ℝ) (1170003459733
    / 1000000000000 : ℝ) (1520507865297 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell394_denomLower :
    (1510287619943 / 10000000000 : ℝ) ≤ Real.exp (6271837869332743 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6271837869332743 / 1250000000000000 : ℝ) (116975689683 /
    100000000000 : ℝ) (1510287619943 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell394_product_lower :
    (6426134744332743 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (197 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell394_leftExp
    (by norm_num : (0 : ℝ) ≤ (16364021157 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell394_product_upper :
    Real.pi * Real.exp (79 / 160 : ℝ) ≤ (25736697934647791 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell394_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell394_endpointLower :
    (1969612569 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (197 / 800 : ℝ) (79 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6426134744332743 / 1250000000000000 : ℝ) (Real.pi * Real.exp (197 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell394_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 160 : ℝ) - (197 / 1600 : ℝ)) ≤
      (1520507865297 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell394_denomUpper
    linarith [hpThetaJensenCell394_product_upper]
  have hi : (1 / (1520507865297 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 160 : ℝ) - (197 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1520507865297 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1520507865297 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((197 / 1600 : ℝ) - Real.pi * Real.exp (79 / 160 : ℝ)) := by
    rw [show (197 / 1600 : ℝ) - Real.pi * Real.exp (79 / 160 : ℝ) =
      -(Real.pi * Real.exp (79 / 160 : ℝ) - (197 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (197 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (197 / 400 : ℝ)) := by
    have h := hpThetaJensenCell394_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1520507865297 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell394_endpointUpper :
    hpThetaJensenKernelEndpointUpper (197 / 800 : ℝ) (79 / 320 : ℝ) ≤ (4985417957 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 160 : ℝ)) (25736697934647791 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell394_product_upper
  have hD : (1510287619943 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (197 / 400 : ℝ) - (79 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell394_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell394_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (197 / 400 : ℝ) - (79 / 640 : ℝ)) ≤
      (1 / (1510287619943 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1510287619943 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 640 : ℝ) - Real.pi * Real.exp (197 / 400 : ℝ)) ≤
      (2 / (1510287619943 / 10000000000 : ℝ) : ℝ) := by
    rw [show (79 / 640 : ℝ) - Real.pi * Real.exp (197 / 400 : ℝ) =
      -(Real.pi * Real.exp (197 / 400 : ℝ) - (79 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25736697934647791 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (25736697934647791 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell394_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (197 / 800 : ℝ) (79 / 320 : ℝ)) :
    (1969612569 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4985417957 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell394_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell394_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell395_leftExp :
    (16384488973 / 10000000000 : ℝ) ≤ Real.exp (79 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 160 : ℝ) (507774669867 / 500000000000 : ℝ)
    (16384488973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell395_rightExp :
    Real.exp (99 / 200 : ℝ) ≤ (16404982391 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (99 / 200 : ℝ) (507794505203 / 500000000000 : ℝ)
    (16404982391 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell395_denomUpper :
    Real.exp (50303402844688863 / 10000000000000000 : ℝ) ≤ (764925311409 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (50303402844688863 / 10000000000000000 : ℝ) (23404549053
    / 20000000000 : ℝ) (764925311409 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell395_denomLower :
    (759777677283 / 5000000000 : ℝ) ≤ Real.exp (6279484935208127 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6279484935208127 / 1250000000000000 : ℝ) (1169980548409
    / 1000000000000 : ℝ) (759777677283 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell395_product_lower :
    (6434172435208127 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell395_leftExp
    (by norm_num : (0 : ℝ) ≤ (16384488973 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell395_product_upper :
    Real.pi * Real.exp (99 / 200 : ℝ) ≤ (51537777844688863 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell395_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell395_endpointLower :
    (9817471457 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 320 : ℝ) (99 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6434172435208127 / 1250000000000000 : ℝ) (Real.pi * Real.exp (79 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell395_product_lower
  have hD : Real.exp (Real.pi * Real.exp (99 / 200 : ℝ) - (79 / 640 : ℝ)) ≤
      (764925311409 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell395_denomUpper
    linarith [hpThetaJensenCell395_product_upper]
  have hi : (1 / (764925311409 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (99 / 200 : ℝ) - (79 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (764925311409 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (764925311409 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 640 : ℝ) - Real.pi * Real.exp (99 / 200 : ℝ)) := by
    rw [show (79 / 640 : ℝ) - Real.pi * Real.exp (99 / 200 : ℝ) =
      -(Real.pi * Real.exp (99 / 200 : ℝ) - (79 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 160 : ℝ)) := by
    have h := hpThetaJensenCell395_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (764925311409 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell395_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 320 : ℝ) (99 / 400 : ℝ) ≤ (9939934101 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (99 / 200 : ℝ)) (51537777844688863 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (99 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell395_product_upper
  have hD : (759777677283 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 160 : ℝ) - (99 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell395_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell395_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 160 : ℝ) - (99 / 800 : ℝ)) ≤
      (1 / (759777677283 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (759777677283 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((99 / 800 : ℝ) - Real.pi * Real.exp (79 / 160 : ℝ)) ≤
      (2 / (759777677283 / 5000000000 : ℝ) : ℝ) := by
    rw [show (99 / 800 : ℝ) - Real.pi * Real.exp (79 / 160 : ℝ) =
      -(Real.pi * Real.exp (79 / 160 : ℝ) - (99 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51537777844688863 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (51537777844688863 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell395_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 320 : ℝ) (99 / 400 : ℝ)) :
    (9817471457 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9939934101 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell395_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell395_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell396_leftExp :
    (1640498239 / 1000000000 : ℝ) ≤ Real.exp (99 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (99 / 200 : ℝ) (203117802081 / 200000000000 : ℝ)
    (1640498239 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell396_rightExp :
    Real.exp (397 / 800 : ℝ) ≤ (16425501441 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (397 / 800 : ℝ) (1015628682627 / 1000000000000 : ℝ)
    (16425501441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell396_denomUpper :
    Real.exp (50364740348535513 / 10000000000000000 : ℝ) ≤ (384815795579 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (50364740348535513 / 10000000000000000 : ℝ) (292612945749
    / 250000000000 : ℝ) (384815795579 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell396_denomLower :
    (1528892256263 / 10000000000 : ℝ) ≤ Real.exp (628714205457061 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (628714205457061 / 125000000000000 : ℝ) (234040907373 /
    200000000000 : ℝ) (1528892256263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell396_product_lower :
    (644222017957061 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (99 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell396_leftExp
    (by norm_num : (0 : ℝ) ≤ (1640498239 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell396_product_upper :
    Real.pi * Real.exp (397 / 800 : ℝ) ≤ (51602240348535513 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell396_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell396_endpointLower :
    (9786887409 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 400 : ℝ) (397 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (644222017957061 / 125000000000000 : ℝ) (Real.pi * Real.exp (99 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell396_product_lower
  have hD : Real.exp (Real.pi * Real.exp (397 / 800 : ℝ) - (99 / 800 : ℝ)) ≤
      (384815795579 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell396_denomUpper
    linarith [hpThetaJensenCell396_product_upper]
  have hi : (1 / (384815795579 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (397 / 800 : ℝ) - (99 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (384815795579 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (384815795579 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((99 / 800 : ℝ) - Real.pi * Real.exp (397 / 800 : ℝ)) := by
    rw [show (99 / 800 : ℝ) - Real.pi * Real.exp (397 / 800 : ℝ) =
      -(Real.pi * Real.exp (397 / 800 : ℝ) - (99 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (99 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (99 / 200 : ℝ)) := by
    have h := hpThetaJensenCell396_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (384815795579 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell396_endpointUpper :
    hpThetaJensenKernelEndpointUpper (99 / 400 : ℝ) (397 / 1600 : ℝ) ≤ (9909039397 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (397 / 800 : ℝ)) (51602240348535513 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (397 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell396_product_upper
  have hD : (1528892256263 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (99 / 200 : ℝ) - (397 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell396_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell396_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (99 / 200 : ℝ) - (397 / 3200 : ℝ)) ≤
      (1 / (1528892256263 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1528892256263 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((397 / 3200 : ℝ) - Real.pi * Real.exp (99 / 200 : ℝ)) ≤
      (2 / (1528892256263 / 10000000000 : ℝ) : ℝ) := by
    rw [show (397 / 3200 : ℝ) - Real.pi * Real.exp (99 / 200 : ℝ) =
      -(Real.pi * Real.exp (99 / 200 : ℝ) - (397 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51602240348535513 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (51602240348535513 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell396_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (99 / 400 : ℝ) (397 / 1600 : ℝ)) :
    (9786887409 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9909039397 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell396_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell396_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell397_leftExp :
    (12832423 / 7812500 : ℝ) ≤ Real.exp (397 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (397 / 800 : ℝ) (507814341313 / 500000000000 : ℝ)
    (12832423 / 7812500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell397_rightExp :
    Real.exp (199 / 400 : ℝ) ≤ (4111511539 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (199 / 400 : ℝ) (1015668356397 / 1000000000000 : ℝ)
    (4111511539 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell397_denomUpper :
    Real.exp (12606539620341627 / 2500000000000000 : ℝ) ≤ (387186535207 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12606539620341627 / 2500000000000000 : ℝ) (234135290263
    / 200000000000 : ℝ) (387186535207 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell397_denomLower :
    (769149458057 / 5000000000 : ℝ) ≤ Real.exp (9835639437479 / 1953125000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9835639437479 / 1953125000000 : ℝ) (585214431371 /
    500000000000 : ℝ) (769149458057 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell397_product_lower :
    (5039279679677 / 976562500000 : ℝ) ≤ Real.pi * Real.exp (397 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell397_leftExp
    (by norm_num : (0 : ℝ) ≤ (12832423 / 7812500 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell397_product_upper :
    Real.pi * Real.exp (199 / 400 : ℝ) ≤ (12916695870341627 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell397_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell397_endpointLower :
    (4878155573 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (397 / 1600 : ℝ) (199 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5039279679677 / 976562500000 : ℝ) (Real.pi * Real.exp (397 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell397_product_lower
  have hD : Real.exp (Real.pi * Real.exp (199 / 400 : ℝ) - (397 / 3200 : ℝ)) ≤
      (387186535207 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell397_denomUpper
    linarith [hpThetaJensenCell397_product_upper]
  have hi : (1 / (387186535207 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (199 / 400 : ℝ) - (397 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (387186535207 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (387186535207 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((397 / 3200 : ℝ) - Real.pi * Real.exp (199 / 400 : ℝ)) := by
    rw [show (397 / 3200 : ℝ) - Real.pi * Real.exp (199 / 400 : ℝ) =
      -(Real.pi * Real.exp (199 / 400 : ℝ) - (397 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (397 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (397 / 800 : ℝ)) := by
    have h := hpThetaJensenCell397_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (387186535207 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell397_endpointUpper :
    hpThetaJensenKernelEndpointUpper (397 / 1600 : ℝ) (199 / 800 : ℝ) ≤ (9878152253 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (199 / 400 : ℝ)) (12916695870341627 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (199 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell397_product_upper
  have hD : (769149458057 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (397 / 800 : ℝ) - (199 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell397_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell397_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (397 / 800 : ℝ) - (199 / 1600 : ℝ)) ≤
      (1 / (769149458057 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (769149458057 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((199 / 1600 : ℝ) - Real.pi * Real.exp (397 / 800 : ℝ)) ≤
      (2 / (769149458057 / 5000000000 : ℝ) : ℝ) := by
    rw [show (199 / 1600 : ℝ) - Real.pi * Real.exp (397 / 800 : ℝ) =
      -(Real.pi * Real.exp (397 / 800 : ℝ) - (199 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12916695870341627 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (12916695870341627 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell397_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (397 / 1600 : ℝ) (199 / 800 : ℝ)) :
    (4878155573 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9878152253 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell397_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell397_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell398_leftExp :
    (8223023077 / 5000000000 : ℝ) ≤ Real.exp (199 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (199 / 400 : ℝ) (253917089099 / 250000000000 : ℝ)
    (8223023077 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell398_rightExp :
    Real.exp (399 / 800 : ℝ) ≤ (16466616567 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (399 / 800 : ℝ) (1015708031717 / 1000000000000 : ℝ)
    (16466616567 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell398_denomUpper :
    Real.exp (50487657340571231 / 10000000000000000 : ℝ) ≤ (1558300100697 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (50487657340571231 / 10000000000000000 : ℝ)
    (1170901458143 / 1000000000000 : ℝ) (1558300100697 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell398_denomLower :
    (386943982611 / 2500000000 : ℝ) ≤ Real.exp (3151243251814823 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3151243251814823 / 625000000000000 : ℝ) (73165845411 /
    62500000000 : ℝ) (386943982611 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell398_product_lower :
    (3229172939314823 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (199 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell398_leftExp
    (by norm_num : (0 : ℝ) ≤ (8223023077 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell398_product_upper :
    Real.pi * Real.exp (399 / 800 : ℝ) ≤ (51731407340571231 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell398_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell398_endpointLower :
    (2431435779 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (199 / 800 : ℝ) (399 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3229172939314823 / 625000000000000 : ℝ) (Real.pi * Real.exp (199 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell398_product_lower
  have hD : Real.exp (Real.pi * Real.exp (399 / 800 : ℝ) - (199 / 1600 : ℝ)) ≤
      (1558300100697 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell398_denomUpper
    linarith [hpThetaJensenCell398_product_upper]
  have hi : (1 / (1558300100697 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (399 / 800 : ℝ) - (199 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1558300100697 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1558300100697 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((199 / 1600 : ℝ) - Real.pi * Real.exp (399 / 800 : ℝ)) := by
    rw [show (199 / 1600 : ℝ) - Real.pi * Real.exp (399 / 800 : ℝ) =
      -(Real.pi * Real.exp (399 / 800 : ℝ) - (199 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (199 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (199 / 400 : ℝ)) := by
    have h := hpThetaJensenCell398_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1558300100697 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell398_endpointUpper :
    hpThetaJensenKernelEndpointUpper (199 / 800 : ℝ) (399 / 1600 : ℝ) ≤ (9847273121 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (399 / 800 : ℝ)) (51731407340571231 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (399 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell398_product_upper
  have hD : (386943982611 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (199 / 400 : ℝ) - (399 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell398_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell398_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (199 / 400 : ℝ) - (399 / 3200 : ℝ)) ≤
      (1 / (386943982611 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (386943982611 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((399 / 3200 : ℝ) - Real.pi * Real.exp (199 / 400 : ℝ)) ≤
      (2 / (386943982611 / 2500000000 : ℝ) : ℝ) := by
    rw [show (399 / 3200 : ℝ) - Real.pi * Real.exp (199 / 400 : ℝ) =
      -(Real.pi * Real.exp (199 / 400 : ℝ) - (399 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51731407340571231 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (51731407340571231 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell398_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (199 / 800 : ℝ) (399 / 1600 : ℝ)) :
    (2431435779 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9847273121 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell398_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell398_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell399_leftExp :
    (3293323313 / 2000000000 : ℝ) ≤ Real.exp (399 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (399 / 800 : ℝ) (253927007929 / 250000000000 : ℝ)
    (3293323313 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell399_rightExp :
    Real.exp (1 / 2 : ℝ) ≤ (4121803177 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 2 : ℝ) (1015747708587 / 1000000000000 : ℝ)
    (4121803177 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell399_denomUpper :
    Real.exp (12637309258240961 / 2500000000000000 : ℝ) ≤ (48997677229 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12637309258240961 / 2500000000000000 : ℝ) (73195425253 /
    62500000000 : ℝ) (48997677229 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell399_denomLower :
    (778661951009 / 5000000000 : ℝ) ≤ Real.exp (1262034771691787 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1262034771691787 / 250000000000000 : ℝ) (585439264461 /
    500000000000 : ℝ) (778661951009 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell399_product_lower :
    (1293284771691787 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (399 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell399_leftExp
    (by norm_num : (0 : ℝ) ≤ (3293323313 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell399_product_upper :
    Real.pi * Real.exp (1 / 2 : ℝ) ≤ (12949028008240961 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell399_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell399_endpointLower :
    (9695183759 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (399 / 1600 : ℝ) (1 / 4 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1293284771691787 / 250000000000000 : ℝ) (Real.pi * Real.exp (399 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell399_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 2 : ℝ) - (399 / 3200 : ℝ)) ≤
      (48997677229 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell399_denomUpper
    linarith [hpThetaJensenCell399_product_upper]
  have hi : (1 / (48997677229 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 2 : ℝ) - (399 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (48997677229 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (48997677229 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((399 / 3200 : ℝ) - Real.pi * Real.exp (1 / 2 : ℝ)) := by
    rw [show (399 / 3200 : ℝ) - Real.pi * Real.exp (1 / 2 : ℝ) =
      -(Real.pi * Real.exp (1 / 2 : ℝ) - (399 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (399 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (399 / 800 : ℝ)) := by
    have h := hpThetaJensenCell399_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (48997677229 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell399_endpointUpper :
    hpThetaJensenKernelEndpointUpper (399 / 1600 : ℝ) (1 / 4 : ℝ) ≤ (196328049 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 2 : ℝ)) (12949028008240961 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 4 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell399_product_upper
  have hD : (778661951009 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (399 / 800 : ℝ) - (1 / 8 : ℝ)) := by
    apply le_trans hpThetaJensenCell399_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell399_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (399 / 800 : ℝ) - (1 / 8 : ℝ)) ≤
      (1 / (778661951009 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (778661951009 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 8 : ℝ) - Real.pi * Real.exp (399 / 800 : ℝ)) ≤
      (2 / (778661951009 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 8 : ℝ) - Real.pi * Real.exp (399 / 800 : ℝ) =
      -(Real.pi * Real.exp (399 / 800 : ℝ) - (1 / 8 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12949028008240961 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (12949028008240961 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell399_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (399 / 1600 : ℝ) (1 / 4 : ℝ)) :
    (9695183759 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (196328049 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell399_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell399_endpointUpper

def hpThetaJensenCellsBatch019Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10276860663 / 10000000000 : ℝ)
  | 1 => (10246213931 / 10000000000 : ℝ)
  | 2 => (10215568189 / 10000000000 : ℝ)
  | 3 => (1273115487 / 1250000000 : ℝ)
  | 4 => (2538570377 / 2500000000 : ℝ)
  | 5 => (1012364149 / 1000000000 : ℝ)
  | 6 => (10093004291 / 10000000000 : ℝ)
  | 7 => (2515592593 / 2500000000 : ℝ)
  | 8 => (2006348037 / 2000000000 : ℝ)
  | 9 => (10001114189 / 10000000000 : ℝ)
  | 10 => (9970492829 / 10000000000 : ℝ)
  | 11 => (9939876567 / 10000000000 : ℝ)
  | 12 => (9909265847 / 10000000000 : ℝ)
  | 13 => (2469665281 / 2500000000 : ℝ)
  | 14 => (1969612569 / 2000000000 : ℝ)
  | 15 => (9817471457 / 10000000000 : ℝ)
  | 16 => (9786887409 / 10000000000 : ℝ)
  | 17 => (4878155573 / 5000000000 : ℝ)
  | 18 => (2431435779 / 2500000000 : ℝ)
  | 19 => (9695183759 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch019Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (32512353 / 31250000 : ℝ)
  | 1 => (10372999511 / 10000000000 : ℝ)
  | 2 => (2068409351 / 2000000000 : ℝ)
  | 3 => (5155547577 / 5000000000 : ℝ)
  | 4 => (514007259 / 500000000 : ℝ)
  | 5 => (10249197287 / 10000000000 : ℝ)
  | 6 => (10218251943 / 10000000000 : ℝ)
  | 7 => (12734137 / 12500000 : ℝ)
  | 8 => (10156370727 / 10000000000 : ℝ)
  | 9 => (10125435779 / 10000000000 : ℝ)
  | 10 => (39431661 / 39062500 : ℝ)
  | 11 => (2515894873 / 2500000000 : ℝ)
  | 12 => (1254082383 / 1250000000 : ℝ)
  | 13 => (2500436097 / 2500000000 : ℝ)
  | 14 => (4985417957 / 5000000000 : ℝ)
  | 15 => (9939934101 / 10000000000 : ℝ)
  | 16 => (9909039397 / 10000000000 : ℝ)
  | 17 => (9878152253 / 10000000000 : ℝ)
  | 18 => (9847273121 / 10000000000 : ℝ)
  | 19 => (196328049 / 200000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch019_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch019Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch019Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell380_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell381_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell382_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell383_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell384_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell385_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell386_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell387_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell388_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell389_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell390_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell391_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell392_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell393_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell394_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell395_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell396_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell397_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell398_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell399_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper] at h ⊢
    exact h

end HodgeProofHP
