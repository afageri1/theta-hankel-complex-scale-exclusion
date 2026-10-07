import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell40_leftExp :
    (10512710963 / 10000000000 : ℝ) ≤ Real.exp (1 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 20 : ℝ) (1001563721339 / 1000000000000 : ℝ)
    (10512710963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell40_rightExp :
    Real.exp (41 / 800 : ℝ) ≤ (1052586007 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 800 : ℝ) (1001602845687 / 1000000000000 : ℝ)
    (1052586007 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell40_denomUpper :
    Real.exp (3294296831489151 / 1000000000000000 : ℝ) ≤ (269584510701 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3294296831489151 / 1000000000000000 : ℝ) (554216206141 /
    500000000000 : ℝ) (269584510701 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell40_denomLower :
    (10735560411 / 400000000 : ℝ) ≤ Real.exp (4112315457459137 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4112315457459137 / 1250000000000000 : ℝ) (221655694659 /
    200000000000 : ℝ) (10735560411 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell40_product_lower :
    (4128331082459137 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell40_leftExp
    (by norm_num : (0 : ℝ) ≤ (10512710963 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell40_product_upper :
    Real.pi * Real.exp (41 / 800 : ℝ) ≤ (3306796831489151 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell40_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell40_endpointLower :
    (1104217357 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 40 : ℝ) (41 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4128331082459137 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell40_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 800 : ℝ) - (1 / 80 : ℝ)) ≤
      (269584510701 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell40_denomUpper
    linarith [hpThetaJensenCell40_product_upper]
  have hi : (1 / (269584510701 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 800 : ℝ) - (1 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (269584510701 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (269584510701 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 80 : ℝ) - Real.pi * Real.exp (41 / 800 : ℝ)) := by
    rw [show (1 / 80 : ℝ) - Real.pi * Real.exp (41 / 800 : ℝ) =
      -(Real.pi * Real.exp (41 / 800 : ℝ) - (1 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 20 : ℝ)) := by
    have h := hpThetaJensenCell40_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (269584510701 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell40_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 40 : ℝ) (41 / 1600 : ℝ) ≤ (17856005649 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 800 : ℝ)) (3306796831489151 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell40_product_upper
  have hD : (10735560411 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 20 : ℝ) - (41 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell40_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell40_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 20 : ℝ) - (41 / 3200 : ℝ)) ≤
      (1 / (10735560411 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10735560411 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 3200 : ℝ) - Real.pi * Real.exp (1 / 20 : ℝ)) ≤
      (2 / (10735560411 / 400000000 : ℝ) : ℝ) := by
    rw [show (41 / 3200 : ℝ) - Real.pi * Real.exp (1 / 20 : ℝ) =
      -(Real.pi * Real.exp (1 / 20 : ℝ) - (41 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3306796831489151 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3306796831489151 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell40_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 40 : ℝ) (41 / 1600 : ℝ)) :
    (1104217357 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17856005649 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell40_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell40_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell41_leftExp :
    (2631465017 / 2500000000 : ℝ) ≤ Real.exp (41 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 800 : ℝ) (500801422843 / 500000000000 : ℝ)
    (2631465017 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell41_rightExp :
    Real.exp (21 / 400 : ℝ) ≤ (10539025621 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 400 : ℝ) (500820985781 / 500000000000 : ℝ)
    (10539025621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell41_denomUpper :
    Real.exp (32981204117754253 / 10000000000000000 : ℝ) ≤ (270617261867 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32981204117754253 / 10000000000000000 : ℝ) (110856486333
    / 100000000000 : ℝ) (270617261867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell41_denomLower :
    (16838486829 / 625000000 : ℝ) ≤ Real.exp (1029272118210883 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1029272118210883 / 312500000000000 : ℝ) (1108410726941 /
    1000000000000 : ℝ) (16838486829 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell41_product_lower :
    (1033373680710883 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell41_leftExp
    (by norm_num : (0 : ℝ) ≤ (2631465017 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell41_product_upper :
    Real.pi * Real.exp (21 / 400 : ℝ) ≤ (33109329117754253 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell41_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell41_endpointLower :
    (17662449499 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 1600 : ℝ) (21 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1033373680710883 / 312500000000000 : ℝ) (Real.pi * Real.exp (41 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell41_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 400 : ℝ) - (41 / 3200 : ℝ)) ≤
      (270617261867 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell41_denomUpper
    linarith [hpThetaJensenCell41_product_upper]
  have hi : (1 / (270617261867 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 400 : ℝ) - (41 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (270617261867 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (270617261867 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 3200 : ℝ) - Real.pi * Real.exp (21 / 400 : ℝ)) := by
    rw [show (41 / 3200 : ℝ) - Real.pi * Real.exp (21 / 400 : ℝ) =
      -(Real.pi * Real.exp (21 / 400 : ℝ) - (41 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 800 : ℝ)) := by
    have h := hpThetaJensenCell41_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (270617261867 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell41_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 1600 : ℝ) (21 / 800 : ℝ) ≤ (446274341 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 400 : ℝ)) (33109329117754253 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell41_product_upper
  have hD : (16838486829 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 800 : ℝ) - (21 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell41_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell41_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 800 : ℝ) - (21 / 1600 : ℝ)) ≤
      (1 / (16838486829 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16838486829 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 1600 : ℝ) - Real.pi * Real.exp (41 / 800 : ℝ)) ≤
      (2 / (16838486829 / 625000000 : ℝ) : ℝ) := by
    rw [show (21 / 1600 : ℝ) - Real.pi * Real.exp (41 / 800 : ℝ) =
      -(Real.pi * Real.exp (41 / 800 : ℝ) - (21 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33109329117754253 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33109329117754253 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell41_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 1600 : ℝ) (21 / 800 : ℝ)) :
    (17662449499 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (446274341 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell41_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell41_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell42_leftExp :
    (526951281 / 500000000 : ℝ) ≤ Real.exp (21 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 400 : ℝ) (1001641971561 / 1000000000000 : ℝ)
    (526951281 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell42_rightExp :
    Real.exp (43 / 800 : ℝ) ≤ (10552207641 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 800 : ℝ) (500840549483 / 500000000000 : ℝ)
    (10552207641 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell42_denomUpper :
    Real.exp (33019491659512113 / 10000000000000000 : ℝ) ≤ (4244615233 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33019491659512113 / 10000000000000000 : ℝ) (138587188683
    / 125000000000 : ℝ) (4244615233 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell42_denomLower :
    (67611973451 / 2500000000 : ℝ) ≤ Real.exp (206093397347419 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (206093397347419 / 62500000000000 : ℝ) (1108543175363 /
    1000000000000 : ℝ) (67611973451 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell42_product_lower :
    (206933241097419 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell42_leftExp
    (by norm_num : (0 : ℝ) ≤ (526951281 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell42_product_upper :
    Real.pi * Real.exp (43 / 800 : ℝ) ≤ (33150741659512113 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell42_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell42_endpointLower :
    (17657289441 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 800 : ℝ) (43 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (206933241097419 / 62500000000000 : ℝ) (Real.pi * Real.exp (21 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell42_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 800 : ℝ) - (21 / 1600 : ℝ)) ≤
      (4244615233 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell42_denomUpper
    linarith [hpThetaJensenCell42_product_upper]
  have hi : (1 / (4244615233 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 800 : ℝ) - (21 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4244615233 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4244615233 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 1600 : ℝ) - Real.pi * Real.exp (43 / 800 : ℝ)) := by
    rw [show (21 / 1600 : ℝ) - Real.pi * Real.exp (43 / 800 : ℝ) =
      -(Real.pi * Real.exp (43 / 800 : ℝ) - (21 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 400 : ℝ)) := by
    have h := hpThetaJensenCell42_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4244615233 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell42_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 800 : ℝ) (43 / 1600 : ℝ) ≤ (17845808621 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 800 : ℝ)) (33150741659512113 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell42_product_upper
  have hD : (67611973451 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 400 : ℝ) - (43 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell42_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell42_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 400 : ℝ) - (43 / 3200 : ℝ)) ≤
      (1 / (67611973451 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (67611973451 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 3200 : ℝ) - Real.pi * Real.exp (21 / 400 : ℝ)) ≤
      (2 / (67611973451 / 2500000000 : ℝ) : ℝ) := by
    rw [show (43 / 3200 : ℝ) - Real.pi * Real.exp (21 / 400 : ℝ) =
      -(Real.pi * Real.exp (21 / 400 : ℝ) - (43 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33150741659512113 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33150741659512113 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell42_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 800 : ℝ) (43 / 1600 : ℝ)) :
    (17657289441 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17845808621 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell42_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell42_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell43_leftExp :
    (10552207639 / 10000000000 : ℝ) ≤ Real.exp (43 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 800 : ℝ) (200336219793 / 200000000000 : ℝ)
    (10552207639 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell43_rightExp :
    Real.exp (11 / 200 : ℝ) ≤ (10565406147 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 200 : ℝ) (500860113949 / 500000000000 : ℝ)
    (10565406147 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell43_denomUpper :
    Real.exp (33057830993572171 / 10000000000000000 : ℝ) ≤ (136349441311 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33057830993572171 / 10000000000000000 : ℝ) (221766070187
    / 200000000000 : ℝ) (136349441311 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell43_denomLower :
    (67871339173 / 2500000000 : ℝ) ≤ Real.exp (4126653887627661 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4126653887627661 / 1250000000000000 : ℝ) (221735163769 /
    200000000000 : ℝ) (67871339173 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell43_product_lower :
    (4143841387627661 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell43_leftExp
    (by norm_num : (0 : ℝ) ≤ (10552207639 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell43_product_upper :
    Real.pi * Real.exp (11 / 200 : ℝ) ≤ (33192205993572171 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell43_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell43_endpointLower :
    (17651997697 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 1600 : ℝ) (11 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4143841387627661 / 1250000000000000 : ℝ) (Real.pi * Real.exp (43 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell43_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 200 : ℝ) - (43 / 3200 : ℝ)) ≤
      (136349441311 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell43_denomUpper
    linarith [hpThetaJensenCell43_product_upper]
  have hi : (1 / (136349441311 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 200 : ℝ) - (43 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (136349441311 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (136349441311 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 3200 : ℝ) - Real.pi * Real.exp (11 / 200 : ℝ)) := by
    rw [show (43 / 3200 : ℝ) - Real.pi * Real.exp (11 / 200 : ℝ) =
      -(Real.pi * Real.exp (11 / 200 : ℝ) - (43 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 800 : ℝ)) := by
    have h := hpThetaJensenCell43_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (136349441311 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell43_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 1600 : ℝ) (11 / 400 : ℝ) ≤ (8920255359 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 200 : ℝ)) (33192205993572171 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell43_product_upper
  have hD : (67871339173 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 800 : ℝ) - (11 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell43_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell43_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 800 : ℝ) - (11 / 800 : ℝ)) ≤
      (1 / (67871339173 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (67871339173 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 800 : ℝ) - Real.pi * Real.exp (43 / 800 : ℝ)) ≤
      (2 / (67871339173 / 2500000000 : ℝ) : ℝ) := by
    rw [show (11 / 800 : ℝ) - Real.pi * Real.exp (43 / 800 : ℝ) =
      -(Real.pi * Real.exp (43 / 800 : ℝ) - (11 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33192205993572171 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33192205993572171 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell43_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 1600 : ℝ) (11 / 400 : ℝ)) :
    (17651997697 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8920255359 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell43_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell43_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell44_leftExp :
    (5282703073 / 5000000000 : ℝ) ≤ Real.exp (11 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 200 : ℝ) (1001720227897 / 1000000000000 : ℝ)
    (5282703073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell44_rightExp :
    Real.exp (9 / 160 : ℝ) ≤ (10578621163 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 160 : ℝ) (1001759358359 / 1000000000000 : ℝ)
    (10578621163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell44_denomUpper :
    Real.exp (33096222195332659 / 10000000000000000 : ℝ) ≤ (136873909303 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33096222195332659 / 10000000000000000 : ℝ) (110896338807
    / 100000000000 : ℝ) (136873909303 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell44_denomLower :
    (68132052759 / 2500000000 : ℝ) ≤ Real.exp (2065723151564027 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2065723151564027 / 625000000000000 : ℝ) (554404328841 /
    500000000000 : ℝ) (68132052759 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell44_product_lower :
    (2074512214064027 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell44_leftExp
    (by norm_num : (0 : ℝ) ≤ (5282703073 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell44_product_upper :
    Real.pi * Real.exp (9 / 160 : ℝ) ≤ (33233722195332659 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell44_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell44_endpointLower :
    (17646574393 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 400 : ℝ) (9 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2074512214064027 / 625000000000000 : ℝ) (Real.pi * Real.exp (11 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell44_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 160 : ℝ) - (11 / 800 : ℝ)) ≤
      (136873909303 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell44_denomUpper
    linarith [hpThetaJensenCell44_product_upper]
  have hi : (1 / (136873909303 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 160 : ℝ) - (11 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (136873909303 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (136873909303 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 800 : ℝ) - Real.pi * Real.exp (9 / 160 : ℝ)) := by
    rw [show (11 / 800 : ℝ) - Real.pi * Real.exp (9 / 160 : ℝ) =
      -(Real.pi * Real.exp (9 / 160 : ℝ) - (11 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 200 : ℝ)) := by
    have h := hpThetaJensenCell44_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (136873909303 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell44_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 400 : ℝ) (9 / 320 : ℝ) ≤ (1783508009 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 160 : ℝ)) (33233722195332659 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell44_product_upper
  have hD : (68132052759 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 200 : ℝ) - (9 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell44_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell44_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 200 : ℝ) - (9 / 640 : ℝ)) ≤
      (1 / (68132052759 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (68132052759 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 640 : ℝ) - Real.pi * Real.exp (11 / 200 : ℝ)) ≤
      (2 / (68132052759 / 2500000000 : ℝ) : ℝ) := by
    rw [show (9 / 640 : ℝ) - Real.pi * Real.exp (11 / 200 : ℝ) =
      -(Real.pi * Real.exp (11 / 200 : ℝ) - (9 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33233722195332659 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33233722195332659 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell44_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 400 : ℝ) (9 / 320 : ℝ)) :
    (17646574393 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1783508009 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell44_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell44_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell45_leftExp :
    (5289310581 / 5000000000 : ℝ) ≤ Real.exp (9 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 160 : ℝ) (500879679179 / 500000000000 : ℝ)
    (5289310581 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell45_rightExp :
    Real.exp (23 / 400 : ℝ) ≤ (10591852707 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 400 : ℝ) (250449622587 / 250000000000 : ℝ)
    (10591852707 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell45_denomUpper :
    Real.exp (33134665321342251 / 10000000000000000 : ℝ) ≤ (274802216213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33134665321342251 / 10000000000000000 : ℝ)
    (1109096621133 / 1000000000000 : ℝ) (274802216213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell45_denomLower :
    (10943059607 / 400000000 : ℝ) ≤ Real.exp (2068122600848119 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2068122600848119 / 625000000000000 : ℝ) (1108941692169 /
    1000000000000 : ℝ) (10943059607 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell45_product_lower :
    (2077106975848119 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell45_leftExp
    (by norm_num : (0 : ℝ) ≤ (5289310581 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell45_product_upper :
    Real.pi * Real.exp (23 / 400 : ℝ) ≤ (33275290321342251 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell45_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell45_endpointLower :
    (1764101969 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 320 : ℝ) (23 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2077106975848119 / 625000000000000 : ℝ) (Real.pi * Real.exp (9 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell45_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 400 : ℝ) - (9 / 640 : ℝ)) ≤
      (274802216213 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell45_denomUpper
    linarith [hpThetaJensenCell45_product_upper]
  have hi : (1 / (274802216213 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 400 : ℝ) - (9 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (274802216213 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (274802216213 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 640 : ℝ) - Real.pi * Real.exp (23 / 400 : ℝ)) := by
    rw [show (9 / 640 : ℝ) - Real.pi * Real.exp (23 / 400 : ℝ) =
      -(Real.pi * Real.exp (23 / 400 : ℝ) - (9 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 160 : ℝ)) := by
    have h := hpThetaJensenCell45_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (274802216213 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell45_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 320 : ℝ) (23 / 800 : ℝ) ≤ (3565903373 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 400 : ℝ)) (33275290321342251 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell45_product_upper
  have hD : (10943059607 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 160 : ℝ) - (23 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell45_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell45_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 160 : ℝ) - (23 / 1600 : ℝ)) ≤
      (1 / (10943059607 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10943059607 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 1600 : ℝ) - Real.pi * Real.exp (9 / 160 : ℝ)) ≤
      (2 / (10943059607 / 400000000 : ℝ) : ℝ) := by
    rw [show (23 / 1600 : ℝ) - Real.pi * Real.exp (9 / 160 : ℝ) =
      -(Real.pi * Real.exp (9 / 160 : ℝ) - (23 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33275290321342251 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33275290321342251 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell45_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 320 : ℝ) (23 / 800 : ℝ)) :
    (1764101969 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3565903373 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell45_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell45_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell46_leftExp :
    (5295926353 / 5000000000 : ℝ) ≤ Real.exp (23 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 400 : ℝ) (1001798490347 / 1000000000000 : ℝ)
    (5295926353 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell46_rightExp :
    Real.exp (47 / 800 : ℝ) ≤ (5302550401 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 800 : ℝ) (500918811933 / 500000000000 : ℝ)
    (5302550401 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell46_denomUpper :
    Real.exp (16586580221928793 / 5000000000000000 : ℝ) ≤ (275862109441 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16586580221928793 / 5000000000000000 : ℝ) (1109230050441
    / 1000000000000 : ℝ) (275862109441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell46_denomLower :
    (137315113757 / 5000000000 : ℝ) ≤ Real.exp (2070525295396747 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2070525295396747 / 625000000000000 : ℝ) (55453746129 /
    50000000000 : ℝ) (137315113757 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell46_product_lower :
    (2079704982896747 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell46_leftExp
    (by norm_num : (0 : ℝ) ≤ (5295926353 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell46_product_upper :
    Real.pi * Real.exp (47 / 800 : ℝ) ≤ (16658455221928793 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell46_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell46_endpointLower :
    (4408833429 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 800 : ℝ) (47 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2079704982896747 / 625000000000000 : ℝ) (Real.pi * Real.exp (23 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell46_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 800 : ℝ) - (23 / 1600 : ℝ)) ≤
      (275862109441 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell46_denomUpper
    linarith [hpThetaJensenCell46_product_upper]
  have hi : (1 / (275862109441 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 800 : ℝ) - (23 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (275862109441 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (275862109441 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 1600 : ℝ) - Real.pi * Real.exp (47 / 800 : ℝ)) := by
    rw [show (23 / 1600 : ℝ) - Real.pi * Real.exp (47 / 800 : ℝ) =
      -(Real.pi * Real.exp (47 / 800 : ℝ) - (23 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 400 : ℝ)) := by
    have h := hpThetaJensenCell46_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (275862109441 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell46_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 800 : ℝ) (47 / 1600 : ℝ) ≤ (17823821211 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 800 : ℝ)) (16658455221928793 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell46_product_upper
  have hD : (137315113757 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 400 : ℝ) - (47 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell46_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell46_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 400 : ℝ) - (47 / 3200 : ℝ)) ≤
      (1 / (137315113757 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (137315113757 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 3200 : ℝ) - Real.pi * Real.exp (23 / 400 : ℝ)) ≤
      (2 / (137315113757 / 5000000000 : ℝ) : ℝ) := by
    rw [show (47 / 3200 : ℝ) - Real.pi * Real.exp (23 / 400 : ℝ) =
      -(Real.pi * Real.exp (23 / 400 : ℝ) - (47 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16658455221928793 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16658455221928793 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell46_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 800 : ℝ) (47 / 1600 : ℝ)) :
    (4408833429 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17823821211 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell46_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell46_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell47_leftExp :
    (1657047 / 1562500 : ℝ) ≤ Real.exp (47 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 800 : ℝ) (200367524773 / 200000000000 : ℝ) (1657047
    / 1562500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell47_rightExp :
    Real.exp (3 / 50 : ℝ) ≤ (5309182733 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 50 : ℝ) (7827162179 / 7812500000 : ℝ)
    (5309182733 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell47_denomUpper :
    Real.exp (16605853809713669 / 5000000000000000 : ℝ) ≤ (34615941511 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16605853809713669 / 5000000000000000 : ℝ) (34667614883 /
    31250000000 : ℝ) (34615941511 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell47_denomLower :
    (34461182117 / 1250000000 : ℝ) ≤ Real.exp (647791012353 / 195312500000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (647791012353 / 195312500000 : ℝ) (55460417461 /
    50000000000 : ℝ) (34461182117 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell47_product_lower :
    (650720699853 / 195312500000 : ℝ) ≤ Real.pi * Real.exp (47 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell47_leftExp
    (by norm_num : (0 : ℝ) ≤ (1657047 / 1562500 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell47_product_upper :
    Real.pi * Real.exp (3 / 50 : ℝ) ≤ (16679291309713669 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell47_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell47_endpointLower :
    (8814758321 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 1600 : ℝ) (3 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (650720699853 / 195312500000 : ℝ) (Real.pi * Real.exp (47 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell47_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 50 : ℝ) - (47 / 3200 : ℝ)) ≤
      (34615941511 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell47_denomUpper
    linarith [hpThetaJensenCell47_product_upper]
  have hi : (1 / (34615941511 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 50 : ℝ) - (47 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (34615941511 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (34615941511 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 3200 : ℝ) - Real.pi * Real.exp (3 / 50 : ℝ)) := by
    rw [show (47 / 3200 : ℝ) - Real.pi * Real.exp (3 / 50 : ℝ) =
      -(Real.pi * Real.exp (3 / 50 : ℝ) - (47 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 800 : ℝ)) := by
    have h := hpThetaJensenCell47_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (34615941511 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell47_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 1600 : ℝ) (3 / 100 : ℝ) ≤ (8908996629 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 50 : ℝ)) (16679291309713669 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell47_product_upper
  have hD : (34461182117 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 800 : ℝ) - (3 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell47_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell47_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 800 : ℝ) - (3 / 200 : ℝ)) ≤
      (1 / (34461182117 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (34461182117 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 200 : ℝ) - Real.pi * Real.exp (47 / 800 : ℝ)) ≤
      (2 / (34461182117 / 1250000000 : ℝ) : ℝ) := by
    rw [show (3 / 200 : ℝ) - Real.pi * Real.exp (47 / 800 : ℝ) =
      -(Real.pi * Real.exp (47 / 800 : ℝ) - (3 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16679291309713669 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16679291309713669 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell47_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 1600 : ℝ) (3 / 100 : ℝ)) :
    (8814758321 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8908996629 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell47_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell47_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell48_leftExp :
    (2123673093 / 2000000000 : ℝ) ≤ Real.exp (3 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 50 : ℝ) (1001876758911 / 1000000000000 : ℝ)
    (2123673093 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell48_rightExp :
    Real.exp (49 / 800 : ℝ) ≤ (5315823361 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 800 : ℝ) (1001915895487 / 1000000000000 : ℝ)
    (5315823361 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell48_denomUpper :
    Real.exp (16625153460154073 / 5000000000000000 : ℝ) ≤ (277998518641 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16625153460154073 / 5000000000000000 : ℝ) (1109497498897
    / 1000000000000 : ℝ) (277998518641 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell48_denomLower :
    (138377106247 / 5000000000 : ℝ) ≤ Real.exp (830136174948007 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (830136174948007 / 250000000000000 : ℝ) (554670986193 /
    500000000000 : ℝ) (138377106247 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell48_product_lower :
    (833964299948007 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell48_leftExp
    (by norm_num : (0 : ℝ) ≤ (2123673093 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell48_product_upper :
    Real.pi * Real.exp (49 / 800 : ℝ) ≤ (16700153460154073 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell48_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell48_endpointLower :
    (17623568607 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 100 : ℝ) (49 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (833964299948007 / 250000000000000 : ℝ) (Real.pi * Real.exp (3 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell48_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 800 : ℝ) - (3 / 200 : ℝ)) ≤
      (277998518641 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell48_denomUpper
    linarith [hpThetaJensenCell48_product_upper]
  have hi : (1 / (277998518641 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 800 : ℝ) - (3 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (277998518641 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (277998518641 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 200 : ℝ) - Real.pi * Real.exp (49 / 800 : ℝ)) := by
    rw [show (3 / 200 : ℝ) - Real.pi * Real.exp (49 / 800 : ℝ) =
      -(Real.pi * Real.exp (49 / 800 : ℝ) - (3 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 50 : ℝ)) := by
    have h := hpThetaJensenCell48_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (277998518641 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell48_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 100 : ℝ) (49 / 1600 : ℝ) ≤ (8906016583 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 800 : ℝ)) (16700153460154073 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell48_product_upper
  have hD : (138377106247 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 50 : ℝ) - (49 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell48_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell48_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 50 : ℝ) - (49 / 3200 : ℝ)) ≤
      (1 / (138377106247 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (138377106247 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 3200 : ℝ) - Real.pi * Real.exp (3 / 50 : ℝ)) ≤
      (2 / (138377106247 / 5000000000 : ℝ) : ℝ) := by
    rw [show (49 / 3200 : ℝ) - Real.pi * Real.exp (3 / 50 : ℝ) =
      -(Real.pi * Real.exp (3 / 50 : ℝ) - (49 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16700153460154073 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16700153460154073 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell48_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 100 : ℝ) (49 / 1600 : ℝ)) :
    (17623568607 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8906016583 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell48_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell48_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell49_leftExp :
    (10631646721 / 10000000000 : ℝ) ≤ Real.exp (49 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 800 : ℝ) (500957947743 / 500000000000 : ℝ)
    (10631646721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell49_rightExp :
    Real.exp (1 / 16 : ℝ) ≤ (1064494459 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 16 : ℝ) (125244379199 / 125000000000 : ℝ)
    (1064494459 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell49_denomUpper :
    Real.exp (3328895840933187 / 1000000000000000 : ℝ) ≤ (279075103549 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3328895840933187 / 1000000000000000 : ℝ) (138703939831 /
    125000000000 : ℝ) (279075103549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell49_denomLower :
    (138912264189 / 5000000000 : ℝ) ≤ Real.exp (4155505785689979 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4155505785689979 / 1250000000000000 : ℝ) (554737896181 /
    500000000000 : ℝ) (138912264189 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell49_product_lower :
    (4175037035689979 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell49_leftExp
    (by norm_num : (0 : ℝ) ≤ (10631646721 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell49_product_upper :
    Real.pi * Real.exp (1 / 16 : ℝ) ≤ (3344208340933187 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell49_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell49_endpointLower :
    (2202186221 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 1600 : ℝ) (1 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4175037035689979 / 1250000000000000 : ℝ) (Real.pi * Real.exp (49 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell49_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 16 : ℝ) - (49 / 3200 : ℝ)) ≤
      (279075103549 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell49_denomUpper
    linarith [hpThetaJensenCell49_product_upper]
  have hi : (1 / (279075103549 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 16 : ℝ) - (49 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (279075103549 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (279075103549 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 3200 : ℝ) - Real.pi * Real.exp (1 / 16 : ℝ)) := by
    rw [show (49 / 3200 : ℝ) - Real.pi * Real.exp (1 / 16 : ℝ) =
      -(Real.pi * Real.exp (1 / 16 : ℝ) - (49 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 800 : ℝ)) := by
    have h := hpThetaJensenCell49_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (279075103549 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell49_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 1600 : ℝ) (1 / 32 : ℝ) ≤ (1780594109 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 16 : ℝ)) (3344208340933187 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell49_product_upper
  have hD : (138912264189 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 800 : ℝ) - (1 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell49_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell49_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 800 : ℝ) - (1 / 64 : ℝ)) ≤
      (1 / (138912264189 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (138912264189 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 64 : ℝ) - Real.pi * Real.exp (49 / 800 : ℝ)) ≤
      (2 / (138912264189 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 64 : ℝ) - Real.pi * Real.exp (49 / 800 : ℝ) =
      -(Real.pi * Real.exp (49 / 800 : ℝ) - (1 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3344208340933187 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3344208340933187 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell49_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 1600 : ℝ) (1 / 32 : ℝ)) :
    (2202186221 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1780594109 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell49_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell49_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell50_leftExp :
    (10644944589 / 10000000000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 16 : ℝ) (1001955033591 / 1000000000000 : ℝ)
    (10644944589 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell50_rightExp :
    Real.exp (51 / 800 : ℝ) ≤ (1065825909 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 800 : ℝ) (125249271653 / 125000000000 : ℝ)
    (1065825909 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell50_denomUpper :
    Real.exp (3332766214933037 / 1000000000000000 : ℝ) ≤ (56031464303 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3332766214933037 / 1000000000000000 : ℝ) (221953147159 /
    200000000000 : ℝ) (56031464303 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell50_denomLower :
    (69725109779 / 2500000000 : ℝ) ≤ Real.exp (4160337220155711 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4160337220155711 / 1250000000000000 : ℝ) (221921961889 /
    200000000000 : ℝ) (69725109779 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell50_product_lower :
    (4180259095155711 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell50_leftExp
    (by norm_num : (0 : ℝ) ≤ (10644944589 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell50_product_upper :
    Real.pi * Real.exp (51 / 800 : ℝ) ≤ (3348391214933037 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell50_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell50_endpointLower :
    (3522256057 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 32 : ℝ) (51 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4180259095155711 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell50_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 800 : ℝ) - (1 / 64 : ℝ)) ≤
      (56031464303 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell50_denomUpper
    linarith [hpThetaJensenCell50_product_upper]
  have hi : (1 / (56031464303 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 800 : ℝ) - (1 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (56031464303 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (56031464303 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 64 : ℝ) - Real.pi * Real.exp (51 / 800 : ℝ)) := by
    rw [show (1 / 64 : ℝ) - Real.pi * Real.exp (51 / 800 : ℝ) =
      -(Real.pi * Real.exp (51 / 800 : ℝ) - (1 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 16 : ℝ)) := by
    have h := hpThetaJensenCell50_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (56031464303 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell50_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 32 : ℝ) (51 / 1600 : ℝ) ≤ (889985859 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 800 : ℝ)) (3348391214933037 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell50_product_upper
  have hD : (69725109779 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 16 : ℝ) - (51 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell50_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell50_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 16 : ℝ) - (51 / 3200 : ℝ)) ≤
      (1 / (69725109779 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (69725109779 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 3200 : ℝ) - Real.pi * Real.exp (1 / 16 : ℝ)) ≤
      (2 / (69725109779 / 2500000000 : ℝ) : ℝ) := by
    rw [show (51 / 3200 : ℝ) - Real.pi * Real.exp (1 / 16 : ℝ) =
      -(Real.pi * Real.exp (1 / 16 : ℝ) - (51 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3348391214933037 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3348391214933037 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell50_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 32 : ℝ) (51 / 1600 : ℝ)) :
    (3522256057 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (889985859 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell50_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell50_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell51_leftExp :
    (10658259089 / 10000000000 : ℝ) ≤ Real.exp (51 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 800 : ℝ) (1001994173223 / 1000000000000 : ℝ)
    (10658259089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell51_rightExp :
    Real.exp (13 / 200 : ℝ) ≤ (2667897561 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 200 : ℝ) (501016657193 / 500000000000 : ℝ)
    (2667897561 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell51_denomUpper :
    Real.exp (8341604552354673 / 2500000000000000 : ℝ) ≤ (56249041533 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8341604552354673 / 2500000000000000 : ℝ) (554950075323 /
    500000000000 : ℝ) (56249041533 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell51_denomLower :
    (1093679607 / 39062500 : ℝ) ≤ Real.exp (4165175185991211 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4165175185991211 / 1250000000000000 : ℝ) (1109744023921
    / 1000000000000 : ℝ) (1093679607 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell51_product_lower :
    (4185487685991211 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell51_leftExp
    (by norm_num : (0 : ℝ) ≤ (10658259089 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell51_product_upper :
    Real.pi * Real.exp (13 / 200 : ℝ) ≤ (8381448302354673 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell51_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell51_endpointLower :
    (3520988061 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 1600 : ℝ) (13 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4185487685991211 / 1250000000000000 : ℝ) (Real.pi * Real.exp (51 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell51_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 200 : ℝ) - (51 / 3200 : ℝ)) ≤
      (56249041533 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell51_denomUpper
    linarith [hpThetaJensenCell51_product_upper]
  have hi : (1 / (56249041533 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 200 : ℝ) - (51 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (56249041533 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (56249041533 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 3200 : ℝ) - Real.pi * Real.exp (13 / 200 : ℝ)) := by
    rw [show (51 / 3200 : ℝ) - Real.pi * Real.exp (13 / 200 : ℝ) =
      -(Real.pi * Real.exp (13 / 200 : ℝ) - (51 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 800 : ℝ)) := by
    have h := hpThetaJensenCell51_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (56249041533 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell51_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 1600 : ℝ) (13 / 400 : ℝ) ≤ (17793361603 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 200 : ℝ)) (8381448302354673 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell51_product_upper
  have hD : (1093679607 / 39062500 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 800 : ℝ) - (13 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell51_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell51_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 800 : ℝ) - (13 / 800 : ℝ)) ≤
      (1 / (1093679607 / 39062500 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1093679607 / 39062500 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 800 : ℝ) - Real.pi * Real.exp (51 / 800 : ℝ)) ≤
      (2 / (1093679607 / 39062500 : ℝ) : ℝ) := by
    rw [show (13 / 800 : ℝ) - Real.pi * Real.exp (51 / 800 : ℝ) =
      -(Real.pi * Real.exp (51 / 800 : ℝ) - (13 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8381448302354673 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8381448302354673 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell51_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 1600 : ℝ) (13 / 400 : ℝ)) :
    (3520988061 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17793361603 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell51_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell51_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell52_leftExp :
    (10671590243 / 10000000000 : ℝ) ≤ Real.exp (13 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 200 : ℝ) (200406662877 / 200000000000 : ℝ)
    (10671590243 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell52_rightExp :
    Real.exp (53 / 800 : ℝ) ≤ (10684938073 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 800 : ℝ) (1002072457077 / 1000000000000 : ℝ)
    (10684938073 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell52_denomUpper :
    Real.exp (33405226655570289 / 10000000000000000 : ℝ) ≤ (141169398631 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33405226655570289 / 10000000000000000 : ℝ) (138754345437
    / 125000000000 : ℝ) (141169398631 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell52_denomLower :
    (281069184283 / 10000000000 : ℝ) ≤ Real.exp (4170019691835857 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4170019691835857 / 1250000000000000 : ℝ) (221975687219 /
    200000000000 : ℝ) (281069184283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell52_product_lower :
    (4190722816835857 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell52_leftExp
    (by norm_num : (0 : ℝ) ≤ (10671590243 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell52_product_upper :
    Real.pi * Real.exp (53 / 800 : ℝ) ≤ (33567726655570289 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell52_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell52_endpointLower :
    (4399617499 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 400 : ℝ) (53 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4190722816835857 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell52_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 800 : ℝ) - (13 / 800 : ℝ)) ≤
      (141169398631 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell52_denomUpper
    linarith [hpThetaJensenCell52_product_upper]
  have hi : (1 / (141169398631 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 800 : ℝ) - (13 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (141169398631 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (141169398631 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 800 : ℝ) - Real.pi * Real.exp (53 / 800 : ℝ)) := by
    rw [show (13 / 800 : ℝ) - Real.pi * Real.exp (53 / 800 : ℝ) =
      -(Real.pi * Real.exp (53 / 800 : ℝ) - (13 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 200 : ℝ)) := by
    have h := hpThetaJensenCell52_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (141169398631 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell52_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 400 : ℝ) (53 / 1600 : ℝ) ≤ (3557374903 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 800 : ℝ)) (33567726655570289 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell52_product_upper
  have hD : (281069184283 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 200 : ℝ) - (53 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell52_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell52_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 200 : ℝ) - (53 / 3200 : ℝ)) ≤
      (1 / (281069184283 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (281069184283 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 3200 : ℝ) - Real.pi * Real.exp (13 / 200 : ℝ)) ≤
      (2 / (281069184283 / 10000000000 : ℝ) : ℝ) := by
    rw [show (53 / 3200 : ℝ) - Real.pi * Real.exp (13 / 200 : ℝ) =
      -(Real.pi * Real.exp (13 / 200 : ℝ) - (53 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33567726655570289 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33567726655570289 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell52_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 400 : ℝ) (53 / 1600 : ℝ)) :
    (4399617499 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3557374903 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell52_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell52_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell53_leftExp :
    (1335617259 / 1250000000 : ℝ) ≤ Real.exp (53 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 800 : ℝ) (250518114269 / 250000000000 : ℝ)
    (1335617259 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell53_rightExp :
    Real.exp (27 / 400 : ℝ) ≤ (10698302597 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 400 : ℝ) (1002111601297 / 1000000000000 : ℝ)
    (10698302597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell53_denomUpper :
    Real.exp (33444087550617021 / 10000000000000000 : ℝ) ≤ (885744143 / 31250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33444087550617021 / 10000000000000000 : ℝ)
    (1110169574633 / 1000000000000 : ℝ) (885744143 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell53_denomLower :
    (35270261133 / 1250000000 : ℝ) ≤ Real.exp (521858843242041 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (521858843242041 / 156250000000000 : ℝ) (555006523133 /
    500000000000 : ℝ) (35270261133 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell53_product_lower :
    (524495561992041 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell53_leftExp
    (by norm_num : (0 : ℝ) ≤ (1335617259 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell53_product_upper :
    Real.pi * Real.exp (27 / 400 : ℝ) ≤ (33609712550617021 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell53_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell53_endpointLower :
    (8795934761 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 1600 : ℝ) (27 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (524495561992041 / 156250000000000 : ℝ) (Real.pi * Real.exp (53 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell53_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 400 : ℝ) - (53 / 3200 : ℝ)) ≤
      (885744143 / 31250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell53_denomUpper
    linarith [hpThetaJensenCell53_product_upper]
  have hi : (1 / (885744143 / 31250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 400 : ℝ) - (53 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (885744143 / 31250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (885744143 / 31250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 3200 : ℝ) - Real.pi * Real.exp (27 / 400 : ℝ)) := by
    rw [show (53 / 3200 : ℝ) - Real.pi * Real.exp (27 / 400 : ℝ) =
      -(Real.pi * Real.exp (27 / 400 : ℝ) - (53 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 800 : ℝ)) := by
    have h := hpThetaJensenCell53_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (885744143 / 31250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell53_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 1600 : ℝ) (27 / 800 : ℝ) ≤ (17780256071 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 400 : ℝ)) (33609712550617021 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell53_product_upper
  have hD : (35270261133 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 800 : ℝ) - (27 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell53_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell53_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 800 : ℝ) - (27 / 1600 : ℝ)) ≤
      (1 / (35270261133 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35270261133 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 1600 : ℝ) - Real.pi * Real.exp (53 / 800 : ℝ)) ≤
      (2 / (35270261133 / 1250000000 : ℝ) : ℝ) := by
    rw [show (27 / 1600 : ℝ) - Real.pi * Real.exp (53 / 800 : ℝ) =
      -(Real.pi * Real.exp (53 / 800 : ℝ) - (27 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33609712550617021 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33609712550617021 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell53_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 1600 : ℝ) (27 / 800 : ℝ)) :
    (8795934761 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17780256071 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell53_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell53_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell54_leftExp :
    (2139660519 / 2000000000 : ℝ) ≤ Real.exp (27 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 400 : ℝ) (62631975081 / 62500000000 : ℝ)
    (2139660519 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell54_rightExp :
    Real.exp (11 / 160 : ℝ) ≤ (2677920959 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 160 : ℝ) (501075373523 / 500000000000 : ℝ)
    (2677920959 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell54_denomUpper :
    Real.exp (8370750239347687 / 2500000000000000 : ℝ) ≤ (71135807211 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8370750239347687 / 2500000000000000 : ℝ) (1110304584343
    / 1000000000000 : ℝ) (71135807211 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell54_denomLower :
    (70815182263 / 2500000000 : ℝ) ≤ Real.exp (835945671150781 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (835945671150781 / 250000000000000 : ℝ) (277536963677 /
    250000000000 : ℝ) (70815182263 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell54_product_lower :
    (840242546150781 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell54_leftExp
    (by norm_num : (0 : ℝ) ≤ (2139660519 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell54_product_upper :
    Real.pi * Real.exp (11 / 160 : ℝ) ≤ (8412937739347687 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell54_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell54_endpointLower :
    (8792569523 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 800 : ℝ) (11 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (840242546150781 / 250000000000000 : ℝ) (Real.pi * Real.exp (27 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell54_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 160 : ℝ) - (27 / 1600 : ℝ)) ≤
      (71135807211 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell54_denomUpper
    linarith [hpThetaJensenCell54_product_upper]
  have hi : (1 / (71135807211 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 160 : ℝ) - (27 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71135807211 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71135807211 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 1600 : ℝ) - Real.pi * Real.exp (11 / 160 : ℝ)) := by
    rw [show (27 / 1600 : ℝ) - Real.pi * Real.exp (11 / 160 : ℝ) =
      -(Real.pi * Real.exp (11 / 160 : ℝ) - (27 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 400 : ℝ)) := by
    have h := hpThetaJensenCell54_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71135807211 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell54_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 800 : ℝ) (11 / 320 : ℝ) ≤ (4443376611 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 160 : ℝ)) (8412937739347687 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell54_product_upper
  have hD : (70815182263 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 400 : ℝ) - (11 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell54_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell54_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 400 : ℝ) - (11 / 640 : ℝ)) ≤
      (1 / (70815182263 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (70815182263 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 640 : ℝ) - Real.pi * Real.exp (27 / 400 : ℝ)) ≤
      (2 / (70815182263 / 2500000000 : ℝ) : ℝ) := by
    rw [show (11 / 640 : ℝ) - Real.pi * Real.exp (27 / 400 : ℝ) =
      -(Real.pi * Real.exp (27 / 400 : ℝ) - (11 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8412937739347687 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8412937739347687 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell54_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 800 : ℝ) (11 / 320 : ℝ)) :
    (8792569523 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4443376611 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell54_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell54_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell55_leftExp :
    (2142336767 / 2000000000 : ℝ) ≤ Real.exp (11 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 160 : ℝ) (200430149409 / 200000000000 : ℝ)
    (2142336767 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell55_rightExp :
    Real.exp (7 / 100 : ℝ) ≤ (10725081813 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 100 : ℝ) (250547473581 / 250000000000 : ℝ)
    (10725081813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell55_denomUpper :
    Real.exp (33521966948148109 / 10000000000000000 : ℝ) ≤ (35706767839 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33521966948148109 / 10000000000000000 : ℝ) (69402487059
    / 62500000000 : ℝ) (35706767839 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell55_denomLower :
    (284365140189 / 10000000000 : ℝ) ≤ Real.exp (836918506064133 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (836918506064133 / 250000000000000 : ℝ) (1110282861741 /
    1000000000000 : ℝ) (284365140189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell55_product_lower :
    (841293506064133 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell55_leftExp
    (by norm_num : (0 : ℝ) ≤ (2142336767 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell55_product_upper :
    Real.pi * Real.exp (7 / 100 : ℝ) ≤ (33693841948148109 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell55_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell55_endpointLower :
    (4394569683 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 320 : ℝ) (7 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (841293506064133 / 250000000000000 : ℝ) (Real.pi * Real.exp (11 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell55_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 100 : ℝ) - (11 / 640 : ℝ)) ≤
      (35706767839 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell55_denomUpper
    linarith [hpThetaJensenCell55_product_upper]
  have hi : (1 / (35706767839 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 100 : ℝ) - (11 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (35706767839 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (35706767839 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 640 : ℝ) - Real.pi * Real.exp (7 / 100 : ℝ)) := by
    rw [show (11 / 640 : ℝ) - Real.pi * Real.exp (7 / 100 : ℝ) =
      -(Real.pi * Real.exp (7 / 100 : ℝ) - (11 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 160 : ℝ)) := by
    have h := hpThetaJensenCell55_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (35706767839 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell55_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 320 : ℝ) (7 / 200 : ℝ) ≤ (4441656449 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 100 : ℝ)) (33693841948148109 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell55_product_upper
  have hD : (284365140189 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 160 : ℝ) - (7 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell55_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell55_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 160 : ℝ) - (7 / 400 : ℝ)) ≤
      (1 / (284365140189 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (284365140189 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 400 : ℝ) - Real.pi * Real.exp (11 / 160 : ℝ)) ≤
      (2 / (284365140189 / 10000000000 : ℝ) : ℝ) := by
    rw [show (7 / 400 : ℝ) - Real.pi * Real.exp (11 / 160 : ℝ) =
      -(Real.pi * Real.exp (11 / 160 : ℝ) - (7 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33693841948148109 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33693841948148109 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell55_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 320 : ℝ) (7 / 200 : ℝ)) :
    (4394569683 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4441656449 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell55_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell55_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell56_leftExp :
    (2681270453 / 2500000000 : ℝ) ≤ Real.exp (7 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 100 : ℝ) (1002189894323 / 1000000000000 : ℝ)
    (2681270453 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell56_rightExp :
    Real.exp (57 / 800 : ℝ) ≤ (2684624137 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 800 : ℝ) (250557260783 / 250000000000 : ℝ)
    (2684624137 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell56_denomUpper :
    Real.exp (8390246396430241 / 2500000000000000 : ℝ) ≤ (286770903569 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8390246396430241 / 2500000000000000 : ℝ) (277643800181 /
    250000000000 : ℝ) (286770903569 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell56_denomLower :
    (285475358379 / 10000000000 : ℝ) ≤ Real.exp (1047365819372647 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1047365819372647 / 312500000000000 : ℝ) (22208361353 /
    20000000000 : ℝ) (285475358379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell56_product_lower :
    (1052932225622647 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell56_leftExp
    (by norm_num : (0 : ℝ) ≤ (2681270453 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell56_product_upper :
    Real.pi * Real.exp (57 / 800 : ℝ) ≤ (8433996396430241 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell56_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell56_endpointLower :
    (14057031 / 8000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 200 : ℝ) (57 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1052932225622647 / 312500000000000 : ℝ) (Real.pi * Real.exp (7 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell56_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 800 : ℝ) - (7 / 400 : ℝ)) ≤
      (286770903569 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell56_denomUpper
    linarith [hpThetaJensenCell56_product_upper]
  have hi : (1 / (286770903569 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 800 : ℝ) - (7 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (286770903569 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (286770903569 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 400 : ℝ) - Real.pi * Real.exp (57 / 800 : ℝ)) := by
    rw [show (7 / 400 : ℝ) - Real.pi * Real.exp (57 / 800 : ℝ) =
      -(Real.pi * Real.exp (57 / 800 : ℝ) - (7 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 100 : ℝ)) := by
    have h := hpThetaJensenCell56_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (286770903569 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell56_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 200 : ℝ) (57 / 1600 : ℝ) ≤ (8879807149 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 800 : ℝ)) (8433996396430241 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell56_product_upper
  have hD : (285475358379 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 100 : ℝ) - (57 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell56_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell56_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 100 : ℝ) - (57 / 3200 : ℝ)) ≤
      (1 / (285475358379 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (285475358379 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 3200 : ℝ) - Real.pi * Real.exp (7 / 100 : ℝ)) ≤
      (2 / (285475358379 / 10000000000 : ℝ) : ℝ) := by
    rw [show (57 / 3200 : ℝ) - Real.pi * Real.exp (7 / 100 : ℝ) =
      -(Real.pi * Real.exp (7 / 100 : ℝ) - (57 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8433996396430241 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8433996396430241 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell56_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 200 : ℝ) (57 / 1600 : ℝ)) :
    (14057031 / 8000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8879807149 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell56_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell56_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell57_leftExp :
    (10738496547 / 10000000000 : ℝ) ≤ Real.exp (57 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 800 : ℝ) (1002229043131 / 1000000000000 : ℝ)
    (10738496547 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell57_rightExp :
    Real.exp (29 / 400 : ℝ) ≤ (5375964031 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 400 : ℝ) (250567048367 / 250000000000 : ℝ)
    (5375964031 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell57_denomUpper :
    Real.exp (16800028468041383 / 5000000000000000 : ℝ) ≤ (71973386987 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16800028468041383 / 5000000000000000 : ℝ) (55535540399 /
    50000000000 : ℝ) (71973386987 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell57_denomLower :
    (57318283979 / 2000000000 : ℝ) ≤ Real.exp (4194340605510353 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4194340605510353 / 1250000000000000 : ℝ) (555276736367 /
    500000000000 : ℝ) (57318283979 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell57_product_lower :
    (4216996855510353 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell57_leftExp
    (by norm_num : (0 : ℝ) ≤ (10738496547 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell57_product_upper :
    Real.pi * Real.exp (29 / 400 : ℝ) ≤ (16889090968041383 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell57_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell57_endpointLower :
    (1756416927 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 1600 : ℝ) (29 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4216996855510353 / 1250000000000000 : ℝ) (Real.pi * Real.exp (57 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell57_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 400 : ℝ) - (57 / 3200 : ℝ)) ≤
      (71973386987 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell57_denomUpper
    linarith [hpThetaJensenCell57_product_upper]
  have hi : (1 / (71973386987 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 400 : ℝ) - (57 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71973386987 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71973386987 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 3200 : ℝ) - Real.pi * Real.exp (29 / 400 : ℝ)) := by
    rw [show (57 / 3200 : ℝ) - Real.pi * Real.exp (29 / 400 : ℝ) =
      -(Real.pi * Real.exp (29 / 400 : ℝ) - (57 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 800 : ℝ)) := by
    have h := hpThetaJensenCell57_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71973386987 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell57_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 1600 : ℝ) (29 / 800 : ℝ) ≤ (17752472119 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 400 : ℝ)) (16889090968041383 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell57_product_upper
  have hD : (57318283979 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 800 : ℝ) - (29 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell57_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell57_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 800 : ℝ) - (29 / 1600 : ℝ)) ≤
      (1 / (57318283979 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57318283979 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 1600 : ℝ) - Real.pi * Real.exp (57 / 800 : ℝ)) ≤
      (2 / (57318283979 / 2000000000 : ℝ) : ℝ) := by
    rw [show (29 / 1600 : ℝ) - Real.pi * Real.exp (57 / 800 : ℝ) =
      -(Real.pi * Real.exp (57 / 800 : ℝ) - (29 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16889090968041383 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16889090968041383 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell57_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 1600 : ℝ) (29 / 800 : ℝ)) :
    (1756416927 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17752472119 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell57_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell57_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell58_leftExp :
    (537596403 / 500000000 : ℝ) ≤ Real.exp (29 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 400 : ℝ) (1002268193467 / 1000000000000 : ℝ)
    (537596403 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell58_rightExp :
    Real.exp (59 / 800 : ℝ) ≤ (86123011 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 800 : ℝ) (501153672667 / 500000000000 : ℝ)
    (86123011 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell58_denomUpper :
    Real.exp (269113448496523 / 80000000000000 : ℝ) ≤ (57804422511 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (269113448496523 / 80000000000000 : ℝ) (1110846614999 /
    1000000000000 : ℝ) (57804422511 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell58_denomLower :
    (57542672231 / 2000000000 : ℝ) ≤ Real.exp (209961226111697 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (209961226111697 / 62500000000000 : ℝ) (1110689077279 /
    1000000000000 : ℝ) (57542672231 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell58_product_lower :
    (211113569861697 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell58_leftExp
    (by norm_num : (0 : ℝ) ≤ (537596403 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell58_product_upper :
    Real.pi * Real.exp (59 / 800 : ℝ) ≤ (270563448496523 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell58_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell58_endpointLower :
    (4389230117 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 800 : ℝ) (59 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (211113569861697 / 62500000000000 : ℝ) (Real.pi * Real.exp (29 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell58_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 800 : ℝ) - (29 / 1600 : ℝ)) ≤
      (57804422511 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell58_denomUpper
    linarith [hpThetaJensenCell58_product_upper]
  have hi : (1 / (57804422511 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 800 : ℝ) - (29 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (57804422511 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (57804422511 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 1600 : ℝ) - Real.pi * Real.exp (59 / 800 : ℝ)) := by
    rw [show (29 / 1600 : ℝ) - Real.pi * Real.exp (59 / 800 : ℝ) =
      -(Real.pi * Real.exp (59 / 800 : ℝ) - (29 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 400 : ℝ)) := by
    have h := hpThetaJensenCell58_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (57804422511 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell58_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 800 : ℝ) (59 / 1600 : ℝ) ≤ (8872599717 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 800 : ℝ)) (270563448496523 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell58_product_upper
  have hD : (57542672231 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 400 : ℝ) - (59 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell58_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell58_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 400 : ℝ) - (59 / 3200 : ℝ)) ≤
      (1 / (57542672231 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57542672231 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 3200 : ℝ) - Real.pi * Real.exp (29 / 400 : ℝ)) ≤
      (2 / (57542672231 / 2000000000 : ℝ) : ℝ) := by
    rw [show (59 / 3200 : ℝ) - Real.pi * Real.exp (29 / 400 : ℝ) =
      -(Real.pi * Real.exp (29 / 400 : ℝ) - (59 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (270563448496523 / 80000000000000 : ℝ) ^ 2 - 6 *
      (270563448496523 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell58_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 800 : ℝ) (59 / 1600 : ℝ)) :
    (4389230117 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8872599717 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell58_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell58_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell59_leftExp :
    (5382688187 / 5000000000 : ℝ) ≤ Real.exp (59 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 800 : ℝ) (1002307345333 / 1000000000000 : ℝ)
    (5382688187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell59_rightExp :
    Real.exp (3 / 40 : ℝ) ≤ (1077884151 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 40 : ℝ) (100234649873 / 100000000000 : ℝ)
    (1077884151 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell59_denomUpper :
    Real.exp (3367835803592543 / 1000000000000000 : ℝ) ≤ (290156634637 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3367835803592543 / 1000000000000000 : ℝ) (555491311051 /
    500000000000 : ℝ) (290156634637 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell59_denomLower :
    (2310729753 / 80000000 : ℝ) ≤ Real.exp (2102057518346713 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2102057518346713 / 625000000000000 : ℝ) (555412440803 /
    500000000000 : ℝ) (2310729753 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell59_product_lower :
    (2113776268346713 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell59_leftExp
    (by norm_num : (0 : ℝ) ≤ (5382688187 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell59_product_upper :
    Real.pi * Real.exp (3 / 40 : ℝ) ≤ (3386273303592543 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell59_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell59_endpointLower :
    (8774771257 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 1600 : ℝ) (3 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2113776268346713 / 625000000000000 : ℝ) (Real.pi * Real.exp (59 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell59_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 40 : ℝ) - (59 / 3200 : ℝ)) ≤
      (290156634637 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell59_denomUpper
    linarith [hpThetaJensenCell59_product_upper]
  have hi : (1 / (290156634637 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 40 : ℝ) - (59 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (290156634637 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (290156634637 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 3200 : ℝ) - Real.pi * Real.exp (3 / 40 : ℝ)) := by
    rw [show (59 / 3200 : ℝ) - Real.pi * Real.exp (3 / 40 : ℝ) =
      -(Real.pi * Real.exp (3 / 40 : ℝ) - (59 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 800 : ℝ)) := by
    have h := hpThetaJensenCell59_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (290156634637 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell59_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 1600 : ℝ) (3 / 80 : ℝ) ≤ (8868898207 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 40 : ℝ)) (3386273303592543 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell59_product_upper
  have hD : (2310729753 / 80000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 800 : ℝ) - (3 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell59_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell59_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 800 : ℝ) - (3 / 160 : ℝ)) ≤
      (1 / (2310729753 / 80000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2310729753 / 80000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 160 : ℝ) - Real.pi * Real.exp (59 / 800 : ℝ)) ≤
      (2 / (2310729753 / 80000000 : ℝ) : ℝ) := by
    rw [show (3 / 160 : ℝ) - Real.pi * Real.exp (59 / 800 : ℝ) =
      -(Real.pi * Real.exp (59 / 800 : ℝ) - (3 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3386273303592543 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3386273303592543 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell59_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 1600 : ℝ) (3 / 80 : ℝ)) :
    (8774771257 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8868898207 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell59_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell59_endpointUpper

def hpThetaJensenCellsBatch002Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1104217357 / 625000000 : ℝ)
  | 1 => (17662449499 / 10000000000 : ℝ)
  | 2 => (17657289441 / 10000000000 : ℝ)
  | 3 => (17651997697 / 10000000000 : ℝ)
  | 4 => (17646574393 / 10000000000 : ℝ)
  | 5 => (1764101969 / 1000000000 : ℝ)
  | 6 => (4408833429 / 2500000000 : ℝ)
  | 7 => (8814758321 / 5000000000 : ℝ)
  | 8 => (17623568607 / 10000000000 : ℝ)
  | 9 => (2202186221 / 1250000000 : ℝ)
  | 10 => (3522256057 / 2000000000 : ℝ)
  | 11 => (3520988061 / 2000000000 : ℝ)
  | 12 => (4399617499 / 2500000000 : ℝ)
  | 13 => (8795934761 / 5000000000 : ℝ)
  | 14 => (8792569523 / 5000000000 : ℝ)
  | 15 => (4394569683 / 2500000000 : ℝ)
  | 16 => (14057031 / 8000000 : ℝ)
  | 17 => (1756416927 / 1000000000 : ℝ)
  | 18 => (4389230117 / 2500000000 : ℝ)
  | 19 => (8774771257 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch002Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17856005649 / 10000000000 : ℝ)
  | 1 => (446274341 / 250000000 : ℝ)
  | 2 => (17845808621 / 10000000000 : ℝ)
  | 3 => (8920255359 / 5000000000 : ℝ)
  | 4 => (1783508009 / 1000000000 : ℝ)
  | 5 => (3565903373 / 2000000000 : ℝ)
  | 6 => (17823821211 / 10000000000 : ℝ)
  | 7 => (8908996629 / 5000000000 : ℝ)
  | 8 => (8906016583 / 5000000000 : ℝ)
  | 9 => (1780594109 / 1000000000 : ℝ)
  | 10 => (889985859 / 500000000 : ℝ)
  | 11 => (17793361603 / 10000000000 : ℝ)
  | 12 => (3557374903 / 2000000000 : ℝ)
  | 13 => (17780256071 / 10000000000 : ℝ)
  | 14 => (4443376611 / 2500000000 : ℝ)
  | 15 => (4441656449 / 2500000000 : ℝ)
  | 16 => (8879807149 / 5000000000 : ℝ)
  | 17 => (17752472119 / 10000000000 : ℝ)
  | 18 => (8872599717 / 5000000000 : ℝ)
  | 19 => (8868898207 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch002_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch002Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch002Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell40_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell41_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell42_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell43_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell44_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell45_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell46_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell47_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell48_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell49_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell50_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell51_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell52_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell53_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell54_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell55_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell56_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell57_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell58_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell59_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper] at h ⊢
    exact h

end HodgeProofHP
