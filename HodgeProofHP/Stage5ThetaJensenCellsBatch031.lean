import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell620_leftExp :
    (21705921271 / 10000000000 : ℝ) ≤ Real.exp (31 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 40 : ℝ) (512257202953 / 500000000000 : ℝ)
    (21705921271 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell620_rightExp :
    Real.exp (621 / 800 : ℝ) ≤ (21733070639 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (621 / 800 : ℝ) (1024554426783 / 1000000000000 : ℝ)
    (21733070639 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell620_denomUpper :
    Real.exp (66338962587987927 / 10000000000000000 : ℝ) ≤ (7604392742999 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (66338962587987927 / 10000000000000000 : ℝ)
    (1230363012663 / 1000000000000 : ℝ) (7604392742999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell620_denomLower :
    (471089799281 / 625000000 : ℝ) ≤ Real.exp (8281315452200429 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8281315452200429 / 1250000000000000 : ℝ) (1230023022027
    / 1000000000000 : ℝ) (471089799281 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell620_product_lower :
    (8523893577200429 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell620_leftExp
    (by norm_num : (0 : ℝ) ≤ (21705921271 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell620_product_upper :
    Real.pi * Real.exp (621 / 800 : ℝ) ≤ (68276462587987927 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell620_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell620_endpointLower :
    (953965857 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 80 : ℝ) (621 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8523893577200429 / 1250000000000000 : ℝ) (Real.pi * Real.exp (31 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell620_product_lower
  have hD : Real.exp (Real.pi * Real.exp (621 / 800 : ℝ) - (31 / 160 : ℝ)) ≤
      (7604392742999 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell620_denomUpper
    linarith [hpThetaJensenCell620_product_upper]
  have hi : (1 / (7604392742999 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (621 / 800 : ℝ) - (31 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7604392742999 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7604392742999 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 160 : ℝ) - Real.pi * Real.exp (621 / 800 : ℝ)) := by
    rw [show (31 / 160 : ℝ) - Real.pi * Real.exp (621 / 800 : ℝ) =
      -(Real.pi * Real.exp (621 / 800 : ℝ) - (31 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 40 : ℝ)) := by
    have h := hpThetaJensenCell620_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7604392742999 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell620_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 80 : ℝ) (621 / 1600 : ℝ) ≤ (193546323 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (621 / 800 : ℝ)) (68276462587987927 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (621 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell620_product_upper
  have hD : (471089799281 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 40 : ℝ) - (621 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell620_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell620_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 40 : ℝ) - (621 / 3200 : ℝ)) ≤
      (1 / (471089799281 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (471089799281 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((621 / 3200 : ℝ) - Real.pi * Real.exp (31 / 40 : ℝ)) ≤
      (2 / (471089799281 / 625000000 : ℝ) : ℝ) := by
    rw [show (621 / 3200 : ℝ) - Real.pi * Real.exp (31 / 40 : ℝ) =
      -(Real.pi * Real.exp (31 / 40 : ℝ) - (621 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68276462587987927 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (68276462587987927 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell620_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 80 : ℝ) (621 / 1600 : ℝ)) :
    (953965857 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (193546323 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell620_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell620_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell621_leftExp :
    (10866535319 / 5000000000 : ℝ) ≤ Real.exp (621 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (621 / 800 : ℝ) (512277213391 / 500000000000 : ℝ)
    (10866535319 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell621_rightExp :
    Real.exp (311 / 400 : ℝ) ≤ (5440063491 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (311 / 400 : ℝ) (512297224611 / 500000000000 : ℝ)
    (5440063491 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell621_denomUpper :
    Real.exp (16605309132881163 / 2500000000000000 : ℝ) ≤ (7667215159063 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16605309132881163 / 2500000000000000 : ℝ) (1201835339 /
    976562500 : ℝ) (7667215159063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell621_denomLower :
    (1899906240909 / 2500000000 : ℝ) ≤ Real.exp (4145793178235981 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4145793178235981 / 625000000000000 : ℝ) (615169449399 /
    500000000000 : ℝ) (1899906240909 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell621_product_lower :
    (4267277553235981 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (621 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell621_leftExp
    (by norm_num : (0 : ℝ) ≤ (10866535319 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell621_product_upper :
    Real.pi * Real.exp (311 / 400 : ℝ) ≤ (17090465382881163 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell621_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell621_endpointLower :
    (3795407523 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (621 / 1600 : ℝ) (311 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4267277553235981 / 625000000000000 : ℝ) (Real.pi * Real.exp (621 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell621_product_lower
  have hD : Real.exp (Real.pi * Real.exp (311 / 400 : ℝ) - (621 / 3200 : ℝ)) ≤
      (7667215159063 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell621_denomUpper
    linarith [hpThetaJensenCell621_product_upper]
  have hi : (1 / (7667215159063 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (311 / 400 : ℝ) - (621 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7667215159063 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7667215159063 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((621 / 3200 : ℝ) - Real.pi * Real.exp (311 / 400 : ℝ)) := by
    rw [show (621 / 3200 : ℝ) - Real.pi * Real.exp (311 / 400 : ℝ) =
      -(Real.pi * Real.exp (311 / 400 : ℝ) - (621 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (621 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (621 / 800 : ℝ)) := by
    have h := hpThetaJensenCell621_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7667215159063 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell621_endpointUpper :
    hpThetaJensenKernelEndpointUpper (621 / 1600 : ℝ) (311 / 800 : ℝ) ≤ (385021429 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (311 / 400 : ℝ)) (17090465382881163 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (311 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell621_product_upper
  have hD : (1899906240909 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (621 / 800 : ℝ) - (311 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell621_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell621_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (621 / 800 : ℝ) - (311 / 1600 : ℝ)) ≤
      (1 / (1899906240909 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1899906240909 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((311 / 1600 : ℝ) - Real.pi * Real.exp (621 / 800 : ℝ)) ≤
      (2 / (1899906240909 / 2500000000 : ℝ) : ℝ) := by
    rw [show (311 / 1600 : ℝ) - Real.pi * Real.exp (621 / 800 : ℝ) =
      -(Real.pi * Real.exp (621 / 800 : ℝ) - (311 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17090465382881163 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (17090465382881163 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell621_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (621 / 1600 : ℝ) (311 / 800 : ℝ)) :
    (3795407523 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (385021429 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell621_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell621_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell622_leftExp :
    (10880126981 / 5000000000 : ℝ) ≤ Real.exp (311 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (311 / 400 : ℝ) (1024594449221 / 1000000000000 : ℝ)
    (10880126981 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell622_rightExp :
    Real.exp (623 / 800 : ℝ) ≤ (2723433911 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (623 / 800 : ℝ) (128079309153 / 125000000000 : ℝ)
    (2723433911 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell622_denomUpper :
    Real.exp (8312952160760223 / 1250000000000000 : ℝ) ≤ (309225565727 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8312952160760223 / 1250000000000000 : ℝ) (153874531731 /
    125000000000 : ℝ) (309225565727 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell622_denomLower :
    (3831203984051 / 5000000000 : ℝ) ≤ Real.exp (4150935297811719 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4150935297811719 / 625000000000000 : ℝ) (1230655266953 /
    1000000000000 : ℝ) (3831203984051 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell622_product_lower :
    (4272614985311719 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (311 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell622_leftExp
    (by norm_num : (0 : ℝ) ≤ (10880126981 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell622_product_upper :
    Real.pi * Real.exp (623 / 800 : ℝ) ≤ (8555920910760223 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell622_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell622_endpointLower :
    (3775018827 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (311 / 800 : ℝ) (623 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4272614985311719 / 625000000000000 : ℝ) (Real.pi * Real.exp (311 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell622_product_lower
  have hD : Real.exp (Real.pi * Real.exp (623 / 800 : ℝ) - (311 / 1600 : ℝ)) ≤
      (309225565727 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell622_denomUpper
    linarith [hpThetaJensenCell622_product_upper]
  have hi : (1 / (309225565727 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (623 / 800 : ℝ) - (311 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (309225565727 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (309225565727 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((311 / 1600 : ℝ) - Real.pi * Real.exp (623 / 800 : ℝ)) := by
    rw [show (311 / 1600 : ℝ) - Real.pi * Real.exp (623 / 800 : ℝ) =
      -(Real.pi * Real.exp (623 / 800 : ℝ) - (311 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (311 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (311 / 400 : ℝ)) := by
    have h := hpThetaJensenCell622_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (309225565727 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell622_endpointUpper :
    hpThetaJensenKernelEndpointUpper (311 / 800 : ℝ) (623 / 1600 : ℝ) ≤ (239348121 / 625000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (623 / 800 : ℝ)) (8555920910760223 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (623 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell622_product_upper
  have hD : (3831203984051 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (311 / 400 : ℝ) - (623 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell622_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell622_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (311 / 400 : ℝ) - (623 / 3200 : ℝ)) ≤
      (1 / (3831203984051 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3831203984051 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((623 / 3200 : ℝ) - Real.pi * Real.exp (311 / 400 : ℝ)) ≤
      (2 / (3831203984051 / 5000000000 : ℝ) : ℝ) := by
    rw [show (623 / 3200 : ℝ) - Real.pi * Real.exp (311 / 400 : ℝ) =
      -(Real.pi * Real.exp (311 / 400 : ℝ) - (623 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8555920910760223 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (8555920910760223 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell622_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (311 / 800 : ℝ) (623 / 1600 : ℝ)) :
    (3775018827 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (239348121 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell622_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell622_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell623_leftExp :
    (21787471287 / 10000000000 : ℝ) ≤ Real.exp (623 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (623 / 800 : ℝ) (1024634473223 / 1000000000000 : ℝ)
    (21787471287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell623_rightExp :
    Real.exp (39 / 50 : ℝ) ≤ (681710083 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 50 : ℝ) (102467449879 / 100000000000 : ℝ)
    (681710083 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell623_denomUpper :
    Real.exp (2080815781032219 / 312500000000000 : ℝ) ≤ (487166946387 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2080815781032219 / 312500000000000 : ℝ) (1231313613681 /
    1000000000000 : ℝ) (487166946387 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell623_denomLower :
    (7725792168023 / 10000000000 : ℝ) ≤ Real.exp (8312168186933613 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8312168186933613 / 1250000000000000 : ℝ) (615486063681 /
    500000000000 : ℝ) (7725792168023 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell623_product_lower :
    (8555918186933613 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (623 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell623_leftExp
    (by norm_num : (0 : ℝ) ≤ (21787471287 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell623_product_upper :
    Real.pi * Real.exp (39 / 50 : ℝ) ≤ (2141655624782219 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell623_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell623_endpointLower :
    (938674347 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (623 / 1600 : ℝ) (39 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8555918186933613 / 1250000000000000 : ℝ) (Real.pi * Real.exp (623 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell623_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 50 : ℝ) - (623 / 3200 : ℝ)) ≤
      (487166946387 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell623_denomUpper
    linarith [hpThetaJensenCell623_product_upper]
  have hi : (1 / (487166946387 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 50 : ℝ) - (623 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (487166946387 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (487166946387 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((623 / 3200 : ℝ) - Real.pi * Real.exp (39 / 50 : ℝ)) := by
    rw [show (623 / 3200 : ℝ) - Real.pi * Real.exp (39 / 50 : ℝ) =
      -(Real.pi * Real.exp (39 / 50 : ℝ) - (623 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (623 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (623 / 800 : ℝ)) := by
    have h := hpThetaJensenCell623_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (487166946387 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell623_endpointUpper :
    hpThetaJensenKernelEndpointUpper (623 / 1600 : ℝ) (39 / 100 : ℝ) ≤ (476124181 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 50 : ℝ)) (2141655624782219 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell623_product_upper
  have hD : (7725792168023 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (623 / 800 : ℝ) - (39 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell623_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell623_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (623 / 800 : ℝ) - (39 / 200 : ℝ)) ≤
      (1 / (7725792168023 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7725792168023 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 200 : ℝ) - Real.pi * Real.exp (623 / 800 : ℝ)) ≤
      (2 / (7725792168023 / 10000000000 : ℝ) : ℝ) := by
    rw [show (39 / 200 : ℝ) - Real.pi * Real.exp (623 / 800 : ℝ) =
      -(Real.pi * Real.exp (623 / 800 : ℝ) - (39 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2141655624782219 / 312500000000000 : ℝ) ^ 2 - 6 *
      (2141655624782219 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell623_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (623 / 1600 : ℝ) (39 / 100 : ℝ)) :
    (938674347 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (476124181 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell623_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell623_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell624_leftExp :
    (10907361327 / 5000000000 : ℝ) ≤ Real.exp (39 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 50 : ℝ) (1024674498789 / 1000000000000 : ℝ)
    (10907361327 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell624_rightExp :
    Real.exp (25 / 32 : ℝ) ≤ (21842008109 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25 / 32 : ℝ) (1024714525919 / 1000000000000 : ℝ)
    (21842008109 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell624_denomUpper :
    Real.exp (66668699781177637 / 10000000000000000 : ℝ) ≤ (3929658834607 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (66668699781177637 / 10000000000000000 : ℝ) (76976966717
    / 62500000000 : ℝ) (3929658834607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell624_denomLower :
    (7789783996613 / 10000000000 : ℝ) ≤ Real.exp (4161239573251573 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4161239573251573 / 625000000000000 : ℝ) (1231289480859 /
    1000000000000 : ℝ) (7789783996613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell624_product_lower :
    (4283309885751573 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell624_leftExp
    (by norm_num : (0 : ℝ) ≤ (10907361327 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell624_product_upper :
    Real.pi * Real.exp (25 / 32 : ℝ) ≤ (68618699781177637 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell624_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell624_endpointLower :
    (746888651 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 100 : ℝ) (25 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4283309885751573 / 625000000000000 : ℝ) (Real.pi * Real.exp (39 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell624_product_lower
  have hD : Real.exp (Real.pi * Real.exp (25 / 32 : ℝ) - (39 / 200 : ℝ)) ≤
      (3929658834607 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell624_denomUpper
    linarith [hpThetaJensenCell624_product_upper]
  have hi : (1 / (3929658834607 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (25 / 32 : ℝ) - (39 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3929658834607 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3929658834607 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 200 : ℝ) - Real.pi * Real.exp (25 / 32 : ℝ)) := by
    rw [show (39 / 200 : ℝ) - Real.pi * Real.exp (25 / 32 : ℝ) =
      -(Real.pi * Real.exp (25 / 32 : ℝ) - (39 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 50 : ℝ)) := by
    have h := hpThetaJensenCell624_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3929658834607 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell624_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 100 : ℝ) (25 / 64 : ℝ) ≤ (3788484879 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (25 / 32 : ℝ)) (68618699781177637 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (25 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell624_product_upper
  have hD : (7789783996613 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 50 : ℝ) - (25 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell624_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell624_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 50 : ℝ) - (25 / 128 : ℝ)) ≤
      (1 / (7789783996613 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7789783996613 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((25 / 128 : ℝ) - Real.pi * Real.exp (39 / 50 : ℝ)) ≤
      (2 / (7789783996613 / 10000000000 : ℝ) : ℝ) := by
    rw [show (25 / 128 : ℝ) - Real.pi * Real.exp (39 / 50 : ℝ) =
      -(Real.pi * Real.exp (39 / 50 : ℝ) - (25 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68618699781177637 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (68618699781177637 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell624_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 100 : ℝ) (25 / 64 : ℝ)) :
    (746888651 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3788484879 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell624_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell624_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell625_leftExp :
    (21842008107 / 10000000000 : ℝ) ≤ Real.exp (25 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (25 / 32 : ℝ) (512357262959 / 500000000000 : ℝ)
    (21842008107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell625_rightExp :
    Real.exp (313 / 400 : ℝ) ≤ (2186932769 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (313 / 400 : ℝ) (256188638653 / 250000000000 : ℝ)
    (2186932769 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell625_denomUpper :
    Real.exp (6675140178561017 / 1000000000000000 : ℝ) ≤ (7924585317957 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6675140178561017 / 1000000000000000 : ℝ) (15399372701 /
    12500000000 : ℝ) (7924585317957 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell625_denomLower :
    (7854389969711 / 10000000000 : ℝ) ≤ Real.exp (8332803491610793 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8332803491610793 / 1250000000000000 : ℝ) (246321465663 /
    200000000000 : ℝ) (7854389969711 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell625_product_lower :
    (8577334741610793 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (25 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell625_leftExp
    (by norm_num : (0 : ℝ) ≤ (21842008107 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell625_product_upper :
    Real.pi * Real.exp (313 / 400 : ℝ) ≤ (6870452678561017 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell625_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell625_endpointLower :
    (928564119 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (25 / 64 : ℝ) (313 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8577334741610793 / 1250000000000000 : ℝ) (Real.pi * Real.exp (25 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell625_product_lower
  have hD : Real.exp (Real.pi * Real.exp (313 / 400 : ℝ) - (25 / 128 : ℝ)) ≤
      (7924585317957 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell625_denomUpper
    linarith [hpThetaJensenCell625_product_upper]
  have hi : (1 / (7924585317957 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (313 / 400 : ℝ) - (25 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7924585317957 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7924585317957 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((25 / 128 : ℝ) - Real.pi * Real.exp (313 / 400 : ℝ)) := by
    rw [show (25 / 128 : ℝ) - Real.pi * Real.exp (313 / 400 : ℝ) =
      -(Real.pi * Real.exp (313 / 400 : ℝ) - (25 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (25 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (25 / 32 : ℝ)) := by
    have h := hpThetaJensenCell625_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7924585317957 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell625_endpointUpper :
    hpThetaJensenKernelEndpointUpper (25 / 64 : ℝ) (313 / 800 : ℝ) ≤ (1884022137 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (313 / 400 : ℝ)) (6870452678561017 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (313 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell625_product_upper
  have hD : (7854389969711 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (25 / 32 : ℝ) - (313 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell625_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell625_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (25 / 32 : ℝ) - (313 / 1600 : ℝ)) ≤
      (1 / (7854389969711 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7854389969711 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((313 / 1600 : ℝ) - Real.pi * Real.exp (25 / 32 : ℝ)) ≤
      (2 / (7854389969711 / 10000000000 : ℝ) : ℝ) := by
    rw [show (313 / 1600 : ℝ) - Real.pi * Real.exp (25 / 32 : ℝ) =
      -(Real.pi * Real.exp (25 / 32 : ℝ) - (313 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6870452678561017 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (6870452678561017 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell625_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (25 / 64 : ℝ) (313 / 800 : ℝ)) :
    (928564119 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1884022137 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell625_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell625_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell626_leftExp :
    (21869327689 / 10000000000 : ℝ) ≤ Real.exp (313 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (313 / 400 : ℝ) (1024754554611 / 1000000000000 : ℝ)
    (21869327689 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell626_rightExp :
    Real.exp (627 / 800 : ℝ) ≤ (21896681443 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (627 / 800 : ℝ) (1024794584869 / 1000000000000 : ℝ)
    (21896681443 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell626_denomUpper :
    Real.exp (66834211144558699 / 10000000000000000 : ℝ) ≤ (1598096152487 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (66834211144558699 / 10000000000000000 : ℝ)
    (1232268660379 / 1000000000000 : ℝ) (1598096152487 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell626_denomLower :
    (7919616677157 / 10000000000 : ℝ) ≤ Real.exp (8343141239142611 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8343141239142611 / 1250000000000000 : ℝ) (123192567059 /
    100000000000 : ℝ) (7919616677157 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell626_product_lower :
    (8588063114142611 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (313 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell626_leftExp
    (by norm_num : (0 : ℝ) ≤ (21869327689 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell626_product_upper :
    Real.pi * Real.exp (627 / 800 : ℝ) ≤ (68790461144558699 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell626_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell626_endpointLower :
    (923534273 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (313 / 800 : ℝ) (627 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8588063114142611 / 1250000000000000 : ℝ) (Real.pi * Real.exp (313 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell626_product_lower
  have hD : Real.exp (Real.pi * Real.exp (627 / 800 : ℝ) - (313 / 1600 : ℝ)) ≤
      (1598096152487 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell626_denomUpper
    linarith [hpThetaJensenCell626_product_upper]
  have hi : (1 / (1598096152487 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (627 / 800 : ℝ) - (313 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1598096152487 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1598096152487 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((313 / 1600 : ℝ) - Real.pi * Real.exp (627 / 800 : ℝ)) := by
    rw [show (313 / 1600 : ℝ) - Real.pi * Real.exp (627 / 800 : ℝ) =
      -(Real.pi * Real.exp (627 / 800 : ℝ) - (313 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (313 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (313 / 400 : ℝ)) := by
    have h := hpThetaJensenCell626_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1598096152487 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell626_endpointUpper :
    hpThetaJensenKernelEndpointUpper (313 / 800 : ℝ) (627 / 1600 : ℝ) ≤ (1873835841 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (627 / 800 : ℝ)) (68790461144558699 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (627 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell626_product_upper
  have hD : (7919616677157 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (313 / 400 : ℝ) - (627 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell626_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell626_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (313 / 400 : ℝ) - (627 / 3200 : ℝ)) ≤
      (1 / (7919616677157 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7919616677157 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((627 / 3200 : ℝ) - Real.pi * Real.exp (313 / 400 : ℝ)) ≤
      (2 / (7919616677157 / 10000000000 : ℝ) : ℝ) := by
    rw [show (627 / 3200 : ℝ) - Real.pi * Real.exp (313 / 400 : ℝ) =
      -(Real.pi * Real.exp (313 / 400 : ℝ) - (627 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68790461144558699 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (68790461144558699 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell626_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (313 / 800 : ℝ) (627 / 1600 : ℝ)) :
    (923534273 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1873835841 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell626_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell626_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell627_leftExp :
    (21896681441 / 10000000000 : ℝ) ≤ Real.exp (627 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (627 / 800 : ℝ) (256198646217 / 250000000000 : ℝ)
    (21896681441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell627_rightExp :
    Real.exp (157 / 200 : ℝ) ≤ (685127169 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (157 / 200 : ℝ) (1024834616689 / 1000000000000 : ℝ)
    (685127169 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell627_denomUpper :
    Real.exp (2091160249490217 / 312500000000000 : ℝ) ≤ (4028505372441 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2091160249490217 / 312500000000000 : ℝ) (246517600239 /
    200000000000 : ℝ) (4028505372441 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell627_denomLower :
    (1996367695343 / 2500000000 : ℝ) ≤ Real.exp (8353492405199259 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8353492405199259 / 1250000000000000 : ℝ) (616122254261 /
    500000000000 : ℝ) (1996367695343 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell627_product_lower :
    (8598804905199259 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (627 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell627_leftExp
    (by norm_num : (0 : ℝ) ≤ (21896681441 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell627_product_upper :
    Real.pi * Real.exp (157 / 200 : ℝ) ≤ (2152390718240217 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell627_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell627_endpointLower :
    (3674085151 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (627 / 1600 : ℝ) (157 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8598804905199259 / 1250000000000000 : ℝ) (Real.pi * Real.exp (627 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell627_product_lower
  have hD : Real.exp (Real.pi * Real.exp (157 / 200 : ℝ) - (627 / 3200 : ℝ)) ≤
      (4028505372441 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell627_denomUpper
    linarith [hpThetaJensenCell627_product_upper]
  have hi : (1 / (4028505372441 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (157 / 200 : ℝ) - (627 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4028505372441 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4028505372441 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((627 / 3200 : ℝ) - Real.pi * Real.exp (157 / 200 : ℝ)) := by
    rw [show (627 / 3200 : ℝ) - Real.pi * Real.exp (157 / 200 : ℝ) =
      -(Real.pi * Real.exp (157 / 200 : ℝ) - (627 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (627 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (627 / 800 : ℝ)) := by
    have h := hpThetaJensenCell627_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4028505372441 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell627_endpointUpper :
    hpThetaJensenKernelEndpointUpper (627 / 1600 : ℝ) (157 / 400 : ℝ) ≤ (931841787 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (157 / 200 : ℝ)) (2152390718240217 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (157 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell627_product_upper
  have hD : (1996367695343 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (627 / 800 : ℝ) - (157 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell627_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell627_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (627 / 800 : ℝ) - (157 / 800 : ℝ)) ≤
      (1 / (1996367695343 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1996367695343 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((157 / 800 : ℝ) - Real.pi * Real.exp (627 / 800 : ℝ)) ≤
      (2 / (1996367695343 / 2500000000 : ℝ) : ℝ) := by
    rw [show (157 / 800 : ℝ) - Real.pi * Real.exp (627 / 800 : ℝ) =
      -(Real.pi * Real.exp (627 / 800 : ℝ) - (157 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2152390718240217 / 312500000000000 : ℝ) ^ 2 - 6 *
      (2152390718240217 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell627_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (627 / 1600 : ℝ) (157 / 400 : ℝ)) :
    (3674085151 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (931841787 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell627_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell627_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell628_leftExp :
    (10962034703 / 5000000000 : ℝ) ≤ Real.exp (157 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157 / 200 : ℝ) (64052163543 / 62500000000 : ℝ)
    (10962034703 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell628_rightExp :
    Real.exp (629 / 800 : ℝ) ≤ (2195149163 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (629 / 800 : ℝ) (1024874650073 / 1000000000000 : ℝ)
    (2195149163 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell628_denomUpper :
    Real.exp (6700015244436659 / 1000000000000000 : ℝ) ≤ (1624836419863 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6700015244436659 / 1000000000000000 : ℝ) (246581567883 /
    200000000000 : ℝ) (1624836419863 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell628_denomLower :
    (8051959027973 / 10000000000 : ℝ) ≤ Real.exp (4181928503333397 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4181928503333397 / 625000000000000 : ℝ) (616281921487 /
    500000000000 : ℝ) (8051959027973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell628_product_lower :
    (4304780065833397 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (157 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell628_leftExp
    (by norm_num : (0 : ℝ) ≤ (10962034703 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell628_product_upper :
    Real.pi * Real.exp (629 / 800 : ℝ) ≤ (6896265244436659 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell628_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell628_endpointLower :
    (3654100689 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (157 / 400 : ℝ) (629 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4304780065833397 / 625000000000000 : ℝ) (Real.pi * Real.exp (157 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell628_product_lower
  have hD : Real.exp (Real.pi * Real.exp (629 / 800 : ℝ) - (157 / 800 : ℝ)) ≤
      (1624836419863 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell628_denomUpper
    linarith [hpThetaJensenCell628_product_upper]
  have hi : (1 / (1624836419863 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (629 / 800 : ℝ) - (157 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1624836419863 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1624836419863 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((157 / 800 : ℝ) - Real.pi * Real.exp (629 / 800 : ℝ)) := by
    rw [show (157 / 800 : ℝ) - Real.pi * Real.exp (629 / 800 : ℝ) =
      -(Real.pi * Real.exp (629 / 800 : ℝ) - (157 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (157 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (157 / 200 : ℝ)) := by
    have h := hpThetaJensenCell628_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1624836419863 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell628_endpointUpper :
    hpThetaJensenKernelEndpointUpper (157 / 400 : ℝ) (629 / 1600 : ℝ) ≤ (1853565357 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (629 / 800 : ℝ)) (6896265244436659 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (629 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell628_product_upper
  have hD : (8051959027973 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (157 / 200 : ℝ) - (629 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell628_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell628_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (157 / 200 : ℝ) - (629 / 3200 : ℝ)) ≤
      (1 / (8051959027973 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8051959027973 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((629 / 3200 : ℝ) - Real.pi * Real.exp (157 / 200 : ℝ)) ≤
      (2 / (8051959027973 / 10000000000 : ℝ) : ℝ) := by
    rw [show (629 / 3200 : ℝ) - Real.pi * Real.exp (157 / 200 : ℝ) =
      -(Real.pi * Real.exp (157 / 200 : ℝ) - (629 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6896265244436659 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (6896265244436659 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell628_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (157 / 400 : ℝ) (629 / 1600 : ℝ)) :
    (3654100689 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1853565357 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell628_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell628_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell629_leftExp :
    (5487872907 / 2500000000 : ℝ) ≤ Real.exp (629 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (629 / 800 : ℝ) (128109331259 / 125000000000 : ℝ)
    (5487872907 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell629_rightExp :
    Real.exp (63 / 80 : ℝ) ≤ (21978948151 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 80 : ℝ) (1024914685021 / 1000000000000 : ℝ)
    (21978948151 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell629_denomUpper :
    Real.exp (67083284658544543 / 10000000000000000 : ℝ) ≤ (4096000866639 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67083284658544543 / 10000000000000000 : ℝ) (616614087947
    / 500000000000 : ℝ) (4096000866639 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell629_denomLower :
    (8119088244017 / 10000000000 : ℝ) ≤ Real.exp (2093558765205993 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2093558765205993 / 312500000000000 : ℝ) (61644183741 /
    50000000000 : ℝ) (8119088244017 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell629_product_lower :
    (2155082202705993 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (629 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell629_leftExp
    (by norm_num : (0 : ℝ) ≤ (5487872907 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell629_product_upper :
    Real.pi * Real.exp (63 / 80 : ℝ) ≤ (69048909658544543 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell629_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell629_endpointLower :
    (908545937 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (629 / 1600 : ℝ) (63 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2155082202705993 / 312500000000000 : ℝ) (Real.pi * Real.exp (629 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell629_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 80 : ℝ) - (629 / 3200 : ℝ)) ≤
      (4096000866639 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell629_denomUpper
    linarith [hpThetaJensenCell629_product_upper]
  have hi : (1 / (4096000866639 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 80 : ℝ) - (629 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4096000866639 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4096000866639 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((629 / 3200 : ℝ) - Real.pi * Real.exp (63 / 80 : ℝ)) := by
    rw [show (629 / 3200 : ℝ) - Real.pi * Real.exp (63 / 80 : ℝ) =
      -(Real.pi * Real.exp (63 / 80 : ℝ) - (629 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (629 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (629 / 800 : ℝ)) := by
    have h := hpThetaJensenCell629_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4096000866639 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell629_endpointUpper :
    hpThetaJensenKernelEndpointUpper (629 / 1600 : ℝ) (63 / 160 : ℝ) ≤ (3686962421 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 80 : ℝ)) (69048909658544543 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell629_product_upper
  have hD : (8119088244017 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (629 / 800 : ℝ) - (63 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell629_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell629_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (629 / 800 : ℝ) - (63 / 320 : ℝ)) ≤
      (1 / (8119088244017 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8119088244017 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 320 : ℝ) - Real.pi * Real.exp (629 / 800 : ℝ)) ≤
      (2 / (8119088244017 / 10000000000 : ℝ) : ℝ) := by
    rw [show (63 / 320 : ℝ) - Real.pi * Real.exp (629 / 800 : ℝ) =
      -(Real.pi * Real.exp (629 / 800 : ℝ) - (63 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (69048909658544543 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (69048909658544543 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell629_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (629 / 1600 : ℝ) (63 / 160 : ℝ)) :
    (908545937 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3686962421 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell629_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell629_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell630_leftExp :
    (439578963 / 200000000 : ℝ) ≤ Real.exp (63 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 80 : ℝ) (51245734251 / 50000000000 : ℝ) (439578963
    / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell630_rightExp :
    Real.exp (631 / 800 : ℝ) ≤ (4401287803 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (631 / 800 : ℝ) (1024954721533 / 1000000000000 : ℝ)
    (4401287803 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell630_denomUpper :
    Real.exp (13433304952890179 / 2000000000000000 : ℝ) ≤ (8260476639939 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13433304952890179 / 2000000000000000 : ℝ) (308387252877
    / 250000000000 : ℝ) (8260476639939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell630_denomLower :
    (4093432667631 / 5000000000 : ℝ) ≤ Real.exp (167692531691137 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (167692531691137 / 25000000000000 : ℝ) (1233204004927 /
    1000000000000 : ℝ) (4093432667631 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell630_product_lower :
    (172622219191137 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (63 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell630_leftExp
    (by norm_num : (0 : ℝ) ≤ (439578963 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell630_product_upper :
    Real.pi * Real.exp (631 / 800 : ℝ) ≤ (13827054952890179 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell630_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell630_endpointLower :
    (722866873 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 160 : ℝ) (631 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (172622219191137 / 25000000000000 : ℝ) (Real.pi * Real.exp (63 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell630_product_lower
  have hD : Real.exp (Real.pi * Real.exp (631 / 800 : ℝ) - (63 / 320 : ℝ)) ≤
      (8260476639939 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell630_denomUpper
    linarith [hpThetaJensenCell630_product_upper]
  have hi : (1 / (8260476639939 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (631 / 800 : ℝ) - (63 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8260476639939 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8260476639939 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 320 : ℝ) - Real.pi * Real.exp (631 / 800 : ℝ)) := by
    rw [show (63 / 320 : ℝ) - Real.pi * Real.exp (631 / 800 : ℝ) =
      -(Real.pi * Real.exp (631 / 800 : ℝ) - (63 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 80 : ℝ)) := by
    have h := hpThetaJensenCell630_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8260476639939 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell630_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 160 : ℝ) (631 / 1600 : ℝ) ≤ (3666862307 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (631 / 800 : ℝ)) (13827054952890179 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (631 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell630_product_upper
  have hD : (4093432667631 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 80 : ℝ) - (631 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell630_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell630_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 80 : ℝ) - (631 / 3200 : ℝ)) ≤
      (1 / (4093432667631 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4093432667631 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((631 / 3200 : ℝ) - Real.pi * Real.exp (63 / 80 : ℝ)) ≤
      (2 / (4093432667631 / 5000000000 : ℝ) : ℝ) := by
    rw [show (631 / 3200 : ℝ) - Real.pi * Real.exp (63 / 80 : ℝ) =
      -(Real.pi * Real.exp (63 / 80 : ℝ) - (631 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13827054952890179 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (13827054952890179 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell630_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 160 : ℝ) (631 / 1600 : ℝ)) :
    (722866873 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3666862307 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell630_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell630_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell631_leftExp :
    (22006439013 / 10000000000 : ℝ) ≤ Real.exp (631 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (631 / 800 : ℝ) (256238680383 / 250000000000 : ℝ)
    (22006439013 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell631_rightExp :
    Real.exp (79 / 100 : ℝ) ≤ (2754245533 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 100 : ℝ) (1024994759609 / 1000000000000 : ℝ)
    (2754245533 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell631_denomUpper :
    Real.exp (8406234111754069 / 1250000000000000 : ℝ) ≤ (4164806945219 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8406234111754069 / 1250000000000000 : ℝ) (1233870347113
    / 1000000000000 : ℝ) (4164806945219 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell631_denomLower :
    (8255297282841 / 10000000000 : ℝ) ≤ Real.exp (8395031593966087 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8395031593966087 / 1250000000000000 : ℝ) (246704966827 /
    200000000000 : ℝ) (8255297282841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell631_product_lower :
    (8641906593966087 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (631 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell631_leftExp
    (by norm_num : (0 : ℝ) ≤ (22006439013 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell631_product_upper :
    Real.pi * Real.exp (79 / 100 : ℝ) ≤ (8652718486754069 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell631_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell631_endpointLower :
    (1797276287 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (631 / 1600 : ℝ) (79 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8641906593966087 / 1250000000000000 : ℝ) (Real.pi * Real.exp (631 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell631_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 100 : ℝ) - (631 / 3200 : ℝ)) ≤
      (4164806945219 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell631_denomUpper
    linarith [hpThetaJensenCell631_product_upper]
  have hi : (1 / (4164806945219 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 100 : ℝ) - (631 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4164806945219 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4164806945219 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((631 / 3200 : ℝ) - Real.pi * Real.exp (79 / 100 : ℝ)) := by
    rw [show (631 / 3200 : ℝ) - Real.pi * Real.exp (79 / 100 : ℝ) =
      -(Real.pi * Real.exp (79 / 100 : ℝ) - (631 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (631 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (631 / 800 : ℝ)) := by
    have h := hpThetaJensenCell631_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4164806945219 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell631_endpointUpper :
    hpThetaJensenKernelEndpointUpper (631 / 1600 : ℝ) (79 / 200 : ℝ) ≤ (3646830411 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 100 : ℝ)) (8652718486754069 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell631_product_upper
  have hD : (8255297282841 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (631 / 800 : ℝ) - (79 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell631_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell631_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (631 / 800 : ℝ) - (79 / 400 : ℝ)) ≤
      (1 / (8255297282841 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8255297282841 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 400 : ℝ) - Real.pi * Real.exp (631 / 800 : ℝ)) ≤
      (2 / (8255297282841 / 10000000000 : ℝ) : ℝ) := by
    rw [show (79 / 400 : ℝ) - Real.pi * Real.exp (631 / 800 : ℝ) =
      -(Real.pi * Real.exp (631 / 800 : ℝ) - (79 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8652718486754069 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (8652718486754069 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell631_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (631 / 1600 : ℝ) (79 / 200 : ℝ)) :
    (1797276287 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3646830411 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell631_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell631_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell632_leftExp :
    (11016982131 / 5000000000 : ℝ) ≤ Real.exp (79 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 100 : ℝ) (128124344951 / 125000000000 : ℝ)
    (11016982131 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell632_rightExp :
    Real.exp (633 / 800 : ℝ) ≤ (1103076197 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (633 / 800 : ℝ) (1025034799249 / 1000000000000 : ℝ)
    (1103076197 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell632_denomUpper :
    Real.exp (3366666458961821 / 500000000000000 : ℝ) ≤ (8399420639111 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3366666458961821 / 500000000000000 : ℝ) (246838436713 /
    200000000000 : ℝ) (8399420639111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell632_denomLower :
    (8324391160891 / 10000000000 : ℝ) ≤ Real.exp (4202725053361569 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4202725053361569 / 625000000000000 : ℝ) (246769232667 /
    200000000000 : ℝ) (8324391160891 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell632_product_lower :
    (4326357865861569 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell632_leftExp
    (by norm_num : (0 : ℝ) ≤ (11016982131 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell632_product_upper :
    Real.pi * Real.exp (633 / 800 : ℝ) ≤ (3465416458961821 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell632_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell632_endpointLower :
    (3574838411 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 200 : ℝ) (633 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4326357865861569 / 625000000000000 : ℝ) (Real.pi * Real.exp (79 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell632_product_lower
  have hD : Real.exp (Real.pi * Real.exp (633 / 800 : ℝ) - (79 / 400 : ℝ)) ≤
      (8399420639111 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell632_denomUpper
    linarith [hpThetaJensenCell632_product_upper]
  have hi : (1 / (8399420639111 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (633 / 800 : ℝ) - (79 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8399420639111 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8399420639111 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 400 : ℝ) - Real.pi * Real.exp (633 / 800 : ℝ)) := by
    rw [show (79 / 400 : ℝ) - Real.pi * Real.exp (633 / 800 : ℝ) =
      -(Real.pi * Real.exp (633 / 800 : ℝ) - (79 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 100 : ℝ)) := by
    have h := hpThetaJensenCell632_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8399420639111 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell632_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 200 : ℝ) (633 / 1600 : ℝ) ≤ (226679173 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (633 / 800 : ℝ)) (3465416458961821 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (633 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell632_product_upper
  have hD : (8324391160891 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 100 : ℝ) - (633 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell632_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell632_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 100 : ℝ) - (633 / 3200 : ℝ)) ≤
      (1 / (8324391160891 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8324391160891 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((633 / 3200 : ℝ) - Real.pi * Real.exp (79 / 100 : ℝ)) ≤
      (2 / (8324391160891 / 10000000000 : ℝ) : ℝ) := by
    rw [show (633 / 3200 : ℝ) - Real.pi * Real.exp (79 / 100 : ℝ) =
      -(Real.pi * Real.exp (79 / 100 : ℝ) - (633 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3465416458961821 / 500000000000000 : ℝ) ^ 2 - 6 *
      (3465416458961821 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell632_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 200 : ℝ) (633 / 1600 : ℝ)) :
    (3574838411 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (226679173 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell632_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell632_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell633_leftExp :
    (22061523939 / 10000000000 : ℝ) ≤ Real.exp (633 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (633 / 800 : ℝ) (64064674953 / 62500000000 : ℝ)
    (22061523939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell633_rightExp :
    Real.exp (317 / 400 : ℝ) ≤ (22089118087 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (317 / 400 : ℝ) (256268710113 / 250000000000 : ℝ)
    (22089118087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell633_denomUpper :
    Real.exp (67416893758292591 / 10000000000000000 : ℝ) ≤ (4234952065123 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67416893758292591 / 10000000000000000 : ℝ) (617257260873
    / 500000000000 : ℝ) (4234952065123 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell633_denomLower :
    (8394154119751 / 10000000000 : ℝ) ≤ Real.exp (8415882139321361 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8415882139321361 / 1250000000000000 : ℝ) (246833598677 /
    200000000000 : ℝ) (8394154119751 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell633_product_lower :
    (8663538389321361 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (633 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell633_leftExp
    (by norm_num : (0 : ℝ) ≤ (22061523939 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell633_product_upper :
    Real.pi * Real.exp (317 / 400 : ℝ) ≤ (69395018758292591 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell633_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell633_endpointLower :
    (888797977 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (633 / 1600 : ℝ) (317 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8663538389321361 / 1250000000000000 : ℝ) (Real.pi * Real.exp (633 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell633_product_lower
  have hD : Real.exp (Real.pi * Real.exp (317 / 400 : ℝ) - (633 / 3200 : ℝ)) ≤
      (4234952065123 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell633_denomUpper
    linarith [hpThetaJensenCell633_product_upper]
  have hi : (1 / (4234952065123 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (317 / 400 : ℝ) - (633 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4234952065123 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4234952065123 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((633 / 3200 : ℝ) - Real.pi * Real.exp (317 / 400 : ℝ)) := by
    rw [show (633 / 3200 : ℝ) - Real.pi * Real.exp (317 / 400 : ℝ) =
      -(Real.pi * Real.exp (317 / 400 : ℝ) - (633 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (633 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (633 / 800 : ℝ)) := by
    have h := hpThetaJensenCell633_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4234952065123 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell633_endpointUpper :
    hpThetaJensenKernelEndpointUpper (633 / 1600 : ℝ) (317 / 800 : ℝ) ≤ (360697141 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (317 / 400 : ℝ)) (69395018758292591 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (317 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell633_product_upper
  have hD : (8394154119751 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (633 / 800 : ℝ) - (317 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell633_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell633_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (633 / 800 : ℝ) - (317 / 1600 : ℝ)) ≤
      (1 / (8394154119751 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8394154119751 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((317 / 1600 : ℝ) - Real.pi * Real.exp (633 / 800 : ℝ)) ≤
      (2 / (8394154119751 / 10000000000 : ℝ) : ℝ) := by
    rw [show (317 / 1600 : ℝ) - Real.pi * Real.exp (633 / 800 : ℝ) =
      -(Real.pi * Real.exp (633 / 800 : ℝ) - (317 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (69395018758292591 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (69395018758292591 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell633_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (633 / 1600 : ℝ) (317 / 800 : ℝ)) :
    (888797977 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (360697141 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell633_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell633_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell634_leftExp :
    (11044559043 / 5000000000 : ℝ) ≤ Real.exp (317 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (317 / 400 : ℝ) (1025074840451 / 1000000000000 : ℝ)
    (11044559043 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell634_rightExp :
    Real.exp (127 / 160 : ℝ) ≤ (88466987 / 40000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (127 / 160 : ℝ) (1025114883221 / 1000000000000 : ℝ)
    (88466987 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell634_denomUpper :
    Real.exp (270002267090291 / 40000000000000 : ℝ) ≤ (8541071696063 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (270002267090291 / 40000000000000 : ℝ) (1234837362549 /
    1000000000000 : ℝ) (8541071696063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell634_denomLower :
    (846459339353 / 1000000000 : ℝ) ≤ Real.exp (4213163854127057 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4213163854127057 / 625000000000000 : ℝ) (1234490325141 /
    1000000000000 : ℝ) (846459339353 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell634_product_lower :
    (4337187291627057 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (317 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell634_leftExp
    (by norm_num : (0 : ℝ) ≤ (11044559043 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell634_product_upper :
    Real.pi * Real.exp (127 / 160 : ℝ) ≤ (277927267090291 / 40000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell634_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell634_endpointLower :
    (353561309 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (317 / 800 : ℝ) (127 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4337187291627057 / 625000000000000 : ℝ) (Real.pi * Real.exp (317 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell634_product_lower
  have hD : Real.exp (Real.pi * Real.exp (127 / 160 : ℝ) - (317 / 1600 : ℝ)) ≤
      (8541071696063 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell634_denomUpper
    linarith [hpThetaJensenCell634_product_upper]
  have hi : (1 / (8541071696063 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (127 / 160 : ℝ) - (317 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8541071696063 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8541071696063 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((317 / 1600 : ℝ) - Real.pi * Real.exp (127 / 160 : ℝ)) := by
    rw [show (317 / 1600 : ℝ) - Real.pi * Real.exp (127 / 160 : ℝ) =
      -(Real.pi * Real.exp (127 / 160 : ℝ) - (317 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (317 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (317 / 400 : ℝ)) := by
    have h := hpThetaJensenCell634_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8541071696063 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell634_endpointUpper :
    hpThetaJensenKernelEndpointUpper (317 / 800 : ℝ) (127 / 320 : ℝ) ≤ (3587144373 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (127 / 160 : ℝ)) (277927267090291 / 40000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (127 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell634_product_upper
  have hD : (846459339353 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (317 / 400 : ℝ) - (127 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell634_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell634_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (317 / 400 : ℝ) - (127 / 640 : ℝ)) ≤
      (1 / (846459339353 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (846459339353 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((127 / 640 : ℝ) - Real.pi * Real.exp (317 / 400 : ℝ)) ≤
      (2 / (846459339353 / 1000000000 : ℝ) : ℝ) := by
    rw [show (127 / 640 : ℝ) - Real.pi * Real.exp (317 / 400 : ℝ) =
      -(Real.pi * Real.exp (317 / 400 : ℝ) - (127 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (277927267090291 / 40000000000000 : ℝ) ^ 2 - 6 *
      (277927267090291 / 40000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell634_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (317 / 800 : ℝ) (127 / 320 : ℝ)) :
    (353561309 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3587144373 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell634_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell634_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell635_leftExp :
    (5529186687 / 2500000000 : ℝ) ≤ Real.exp (127 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (127 / 160 : ℝ) (51255744161 / 50000000000 : ℝ)
    (5529186687 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell635_rightExp :
    Real.exp (159 / 200 : ℝ) ≤ (22144409969 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (159 / 200 : ℝ) (1025154927553 / 1000000000000 : ℝ)
    (22144409969 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell635_denomUpper :
    Real.exp (67584348347740617 / 10000000000000000 : ℝ) ≤ (8612930743171 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67584348347740617 / 10000000000000000 : ℝ) (308790176703
    / 250000000000 : ℝ) (8612930743171 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell635_denomLower :
    (4267858155221 / 5000000000 : ℝ) ≤ Real.exp (2109196707798213 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2109196707798213 / 312500000000000 : ℝ) (1234813159499 /
    1000000000000 : ℝ) (4267858155221 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell635_product_lower :
    (2171306082798213 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (127 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell635_leftExp
    (by norm_num : (0 : ℝ) ≤ (5529186687 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell635_product_upper :
    Real.pi * Real.exp (159 / 200 : ℝ) ≤ (69568723347740617 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell635_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell635_endpointLower :
    (439512749 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (127 / 320 : ℝ) (159 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2171306082798213 / 312500000000000 : ℝ) (Real.pi * Real.exp (127 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell635_product_lower
  have hD : Real.exp (Real.pi * Real.exp (159 / 200 : ℝ) - (127 / 640 : ℝ)) ≤
      (8612930743171 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell635_denomUpper
    linarith [hpThetaJensenCell635_product_upper]
  have hi : (1 / (8612930743171 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (159 / 200 : ℝ) - (127 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8612930743171 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8612930743171 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((127 / 640 : ℝ) - Real.pi * Real.exp (159 / 200 : ℝ)) := by
    rw [show (127 / 640 : ℝ) - Real.pi * Real.exp (159 / 200 : ℝ) =
      -(Real.pi * Real.exp (159 / 200 : ℝ) - (127 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (127 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (127 / 160 : ℝ)) := by
    have h := hpThetaJensenCell635_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8612930743171 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell635_endpointUpper :
    hpThetaJensenKernelEndpointUpper (127 / 320 : ℝ) (159 / 400 : ℝ) ≤ (1783692841 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (159 / 200 : ℝ)) (69568723347740617 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (159 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell635_product_upper
  have hD : (4267858155221 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (127 / 160 : ℝ) - (159 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell635_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell635_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (127 / 160 : ℝ) - (159 / 800 : ℝ)) ≤
      (1 / (4267858155221 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4267858155221 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((159 / 800 : ℝ) - Real.pi * Real.exp (127 / 160 : ℝ)) ≤
      (2 / (4267858155221 / 5000000000 : ℝ) : ℝ) := by
    rw [show (159 / 800 : ℝ) - Real.pi * Real.exp (127 / 160 : ℝ) =
      -(Real.pi * Real.exp (127 / 160 : ℝ) - (159 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (69568723347740617 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (69568723347740617 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell635_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (127 / 320 : ℝ) (159 / 400 : ℝ)) :
    (439512749 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1783692841 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell635_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell635_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell636_leftExp :
    (22144409967 / 10000000000 : ℝ) ≤ Real.exp (159 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (159 / 200 : ℝ) (16018045743 / 15625000000 : ℝ)
    (22144409967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell636_rightExp :
    Real.exp (637 / 800 : ℝ) ≤ (22172107789 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (637 / 800 : ℝ) (1025194973449 / 1000000000000 : ℝ)
    (22172107789 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell636_denomUpper :
    Real.exp (67668238625167877 / 10000000000000000 : ℝ) ≤ (8685488778137 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67668238625167877 / 10000000000000000 : ℝ)
    (1235484555429 / 1000000000000 : ℝ) (8685488778137 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell636_denomLower :
    (8607530276631 / 10000000000 : ℝ) ≤ Real.exp (8447259524630933 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8447259524630933 / 1250000000000000 : ℝ) (308784124329 /
    250000000000 : ℝ) (8607530276631 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell636_product_lower :
    (8696087649630933 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (159 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell636_leftExp
    (by norm_num : (0 : ℝ) ≤ (22144409967 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell636_product_upper :
    Real.pi * Real.exp (637 / 800 : ℝ) ≤ (69655738625167877 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell636_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell636_endpointLower :
    (874164659 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (159 / 400 : ℝ) (637 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8696087649630933 / 1250000000000000 : ℝ) (Real.pi * Real.exp (159 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell636_product_lower
  have hD : Real.exp (Real.pi * Real.exp (637 / 800 : ℝ) - (159 / 800 : ℝ)) ≤
      (8685488778137 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell636_denomUpper
    linarith [hpThetaJensenCell636_product_upper]
  have hi : (1 / (8685488778137 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (637 / 800 : ℝ) - (159 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8685488778137 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8685488778137 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((159 / 800 : ℝ) - Real.pi * Real.exp (637 / 800 : ℝ)) := by
    rw [show (159 / 800 : ℝ) - Real.pi * Real.exp (637 / 800 : ℝ) =
      -(Real.pi * Real.exp (637 / 800 : ℝ) - (159 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (159 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (159 / 200 : ℝ)) := by
    have h := hpThetaJensenCell636_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8685488778137 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell636_endpointUpper :
    hpThetaJensenKernelEndpointUpper (159 / 400 : ℝ) (637 / 1600 : ℝ) ≤ (3547695369 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (637 / 800 : ℝ)) (69655738625167877 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (637 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell636_product_upper
  have hD : (8607530276631 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (159 / 200 : ℝ) - (637 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell636_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell636_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (159 / 200 : ℝ) - (637 / 3200 : ℝ)) ≤
      (1 / (8607530276631 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8607530276631 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((637 / 3200 : ℝ) - Real.pi * Real.exp (159 / 200 : ℝ)) ≤
      (2 / (8607530276631 / 10000000000 : ℝ) : ℝ) := by
    rw [show (637 / 3200 : ℝ) - Real.pi * Real.exp (159 / 200 : ℝ) =
      -(Real.pi * Real.exp (159 / 200 : ℝ) - (637 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (69655738625167877 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (69655738625167877 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell636_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (159 / 400 : ℝ) (637 / 1600 : ℝ)) :
    (874164659 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3547695369 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell636_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell636_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell637_leftExp :
    (22172107787 / 10000000000 : ℝ) ≤ Real.exp (637 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (637 / 800 : ℝ) (128149371681 / 125000000000 : ℝ)
    (22172107787 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell637_rightExp :
    Real.exp (319 / 400 : ℝ) ≤ (22199840253 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (319 / 400 : ℝ) (102523502091 / 100000000000 : ℝ)
    (22199840253 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell637_denomUpper :
    Real.exp (67752237739943029 / 10000000000000000 : ℝ) ≤ (8758753392323 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67752237739943029 / 10000000000000000 : ℝ) (308952227319
    / 250000000000 : ℝ) (8758753392323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell637_denomLower :
    (8680042792431 / 10000000000 : ℝ) ≤ Real.exp (8457745805847113 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8457745805847113 / 1250000000000000 : ℝ) (1235460339479
    / 1000000000000 : ℝ) (8680042792431 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell637_product_lower :
    (8706964555847113 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (637 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell637_leftExp
    (by norm_num : (0 : ℝ) ≤ (22172107787 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell637_product_upper :
    Real.pi * Real.exp (319 / 400 : ℝ) ≤ (69742862739943029 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell637_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell637_endpointLower :
    (434660381 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (637 / 1600 : ℝ) (319 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8706964555847113 / 1250000000000000 : ℝ) (Real.pi * Real.exp (637 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell637_product_lower
  have hD : Real.exp (Real.pi * Real.exp (319 / 400 : ℝ) - (637 / 3200 : ℝ)) ≤
      (8758753392323 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell637_denomUpper
    linarith [hpThetaJensenCell637_product_upper]
  have hi : (1 / (8758753392323 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (319 / 400 : ℝ) - (637 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8758753392323 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8758753392323 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((637 / 3200 : ℝ) - Real.pi * Real.exp (319 / 400 : ℝ)) := by
    rw [show (637 / 3200 : ℝ) - Real.pi * Real.exp (319 / 400 : ℝ) =
      -(Real.pi * Real.exp (319 / 400 : ℝ) - (637 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (637 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (637 / 800 : ℝ)) := by
    have h := hpThetaJensenCell637_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8758753392323 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell637_endpointUpper :
    hpThetaJensenKernelEndpointUpper (637 / 1600 : ℝ) (319 / 800 : ℝ) ≤ (3528073457 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (319 / 400 : ℝ)) (69742862739943029 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (319 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell637_product_upper
  have hD : (8680042792431 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (637 / 800 : ℝ) - (319 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell637_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell637_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (637 / 800 : ℝ) - (319 / 1600 : ℝ)) ≤
      (1 / (8680042792431 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8680042792431 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((319 / 1600 : ℝ) - Real.pi * Real.exp (637 / 800 : ℝ)) ≤
      (2 / (8680042792431 / 10000000000 : ℝ) : ℝ) := by
    rw [show (319 / 1600 : ℝ) - Real.pi * Real.exp (637 / 800 : ℝ) =
      -(Real.pi * Real.exp (637 / 800 : ℝ) - (319 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (69742862739943029 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (69742862739943029 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell637_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (637 / 1600 : ℝ) (319 / 800 : ℝ)) :
    (434660381 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3528073457 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell637_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell637_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell638_leftExp :
    (22199840251 / 10000000000 : ℝ) ≤ Real.exp (319 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (319 / 400 : ℝ) (1025235020909 / 1000000000000 : ℝ)
    (22199840251 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell638_rightExp :
    Real.exp (639 / 800 : ℝ) ≤ (5556901851 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (639 / 800 : ℝ) (205055013987 / 200000000000 : ℝ)
    (5556901851 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell638_denomUpper :
    Real.exp (16959086456788643 / 2500000000000000 : ℝ) ≤ (8832732266739 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16959086456788643 / 2500000000000000 : ℝ) (309033442307
    / 250000000000 : ℝ) (8832732266739 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell638_denomLower :
    (2188315361 / 2500000 : ℝ) ≤ Real.exp (8468245691727449 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8468245691727449 / 1250000000000000 : ℝ) (617892343431 /
    500000000000 : ℝ) (2188315361 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell638_product_lower :
    (8717855066727449 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (319 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell638_leftExp
    (by norm_num : (0 : ℝ) ≤ (22199840251 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell638_product_upper :
    Real.pi * Real.exp (639 / 800 : ℝ) ≤ (17457523956788643 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell638_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell638_endpointLower :
    (3457975251 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (319 / 800 : ℝ) (639 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8717855066727449 / 1250000000000000 : ℝ) (Real.pi * Real.exp (319 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell638_product_lower
  have hD : Real.exp (Real.pi * Real.exp (639 / 800 : ℝ) - (319 / 1600 : ℝ)) ≤
      (8832732266739 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell638_denomUpper
    linarith [hpThetaJensenCell638_product_upper]
  have hi : (1 / (8832732266739 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (639 / 800 : ℝ) - (319 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8832732266739 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8832732266739 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((319 / 1600 : ℝ) - Real.pi * Real.exp (639 / 800 : ℝ)) := by
    rw [show (319 / 1600 : ℝ) - Real.pi * Real.exp (639 / 800 : ℝ) =
      -(Real.pi * Real.exp (639 / 800 : ℝ) - (319 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (319 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (319 / 400 : ℝ)) := by
    have h := hpThetaJensenCell638_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8832732266739 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell638_endpointUpper :
    hpThetaJensenKernelEndpointUpper (319 / 800 : ℝ) (639 / 1600 : ℝ) ≤ (877129993 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (639 / 800 : ℝ)) (17457523956788643 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (639 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell638_product_upper
  have hD : (2188315361 / 2500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (319 / 400 : ℝ) - (639 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell638_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell638_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (319 / 400 : ℝ) - (639 / 3200 : ℝ)) ≤
      (1 / (2188315361 / 2500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2188315361 / 2500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((639 / 3200 : ℝ) - Real.pi * Real.exp (319 / 400 : ℝ)) ≤
      (2 / (2188315361 / 2500000 : ℝ) : ℝ) := by
    rw [show (639 / 3200 : ℝ) - Real.pi * Real.exp (319 / 400 : ℝ) =
      -(Real.pi * Real.exp (319 / 400 : ℝ) - (639 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17457523956788643 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (17457523956788643 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell638_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (319 / 800 : ℝ) (639 / 1600 : ℝ)) :
    (3457975251 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (877129993 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell638_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell638_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell639_leftExp :
    (11113803701 / 5000000000 : ℝ) ≤ Real.exp (639 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (639 / 800 : ℝ) (512637534967 / 500000000000 : ℝ)
    (11113803701 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell639_rightExp :
    Real.exp (4 / 5 : ℝ) ≤ (11127704643 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4 / 5 : ℝ) (41012604821 / 40000000000 : ℝ)
    (11127704643 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell639_denomUpper :
    Real.exp (33960281512516299 / 5000000000000000 : ℝ) ≤ (4453716588203 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33960281512516299 / 5000000000000000 : ℝ) (1236459136173
    / 1000000000000 : ℝ) (4453716588203 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell639_denomLower :
    (8827193907301 / 10000000000 : ℝ) ≤ Real.exp (4239379599578999 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4239379599578999 / 625000000000000 : ℝ) (1236109540339 /
    1000000000000 : ℝ) (8827193907301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell639_product_lower :
    (4364379599578999 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (639 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell639_leftExp
    (by norm_num : (0 : ℝ) ≤ (11113803701 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell639_product_upper :
    Real.pi * Real.exp (4 / 5 : ℝ) ≤ (34958719012516299 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell639_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell639_endpointLower :
    (687747053 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (639 / 1600 : ℝ) (2 / 5 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4364379599578999 / 625000000000000 : ℝ) (Real.pi * Real.exp (639 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell639_product_lower
  have hD : Real.exp (Real.pi * Real.exp (4 / 5 : ℝ) - (639 / 3200 : ℝ)) ≤
      (4453716588203 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell639_denomUpper
    linarith [hpThetaJensenCell639_product_upper]
  have hi : (1 / (4453716588203 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (4 / 5 : ℝ) - (639 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4453716588203 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4453716588203 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((639 / 3200 : ℝ) - Real.pi * Real.exp (4 / 5 : ℝ)) := by
    rw [show (639 / 3200 : ℝ) - Real.pi * Real.exp (4 / 5 : ℝ) =
      -(Real.pi * Real.exp (4 / 5 : ℝ) - (639 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (639 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (639 / 800 : ℝ)) := by
    have h := hpThetaJensenCell639_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4453716588203 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell639_endpointUpper :
    hpThetaJensenKernelEndpointUpper (639 / 1600 : ℝ) (2 / 5 : ℝ) ≤ (3489034937 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (4 / 5 : ℝ)) (34958719012516299 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (2 / 5 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell639_product_upper
  have hD : (8827193907301 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (639 / 800 : ℝ) - (1 / 5 : ℝ)) := by
    apply le_trans hpThetaJensenCell639_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell639_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (639 / 800 : ℝ) - (1 / 5 : ℝ)) ≤
      (1 / (8827193907301 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8827193907301 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 5 : ℝ) - Real.pi * Real.exp (639 / 800 : ℝ)) ≤
      (2 / (8827193907301 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 5 : ℝ) - Real.pi * Real.exp (639 / 800 : ℝ) =
      -(Real.pi * Real.exp (639 / 800 : ℝ) - (1 / 5 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34958719012516299 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (34958719012516299 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell639_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (639 / 1600 : ℝ) (2 / 5 : ℝ)) :
    (687747053 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3489034937 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell639_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell639_endpointUpper

def hpThetaJensenCellsBatch031Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (953965857 / 2500000000 : ℝ)
  | 1 => (3795407523 / 10000000000 : ℝ)
  | 2 => (3775018827 / 10000000000 : ℝ)
  | 3 => (938674347 / 2500000000 : ℝ)
  | 4 => (746888651 / 2000000000 : ℝ)
  | 5 => (928564119 / 2500000000 : ℝ)
  | 6 => (923534273 / 2500000000 : ℝ)
  | 7 => (3674085151 / 10000000000 : ℝ)
  | 8 => (3654100689 / 10000000000 : ℝ)
  | 9 => (908545937 / 2500000000 : ℝ)
  | 10 => (722866873 / 2000000000 : ℝ)
  | 11 => (1797276287 / 5000000000 : ℝ)
  | 12 => (3574838411 / 10000000000 : ℝ)
  | 13 => (888797977 / 2500000000 : ℝ)
  | 14 => (353561309 / 1000000000 : ℝ)
  | 15 => (439512749 / 1250000000 : ℝ)
  | 16 => (874164659 / 2500000000 : ℝ)
  | 17 => (434660381 / 1250000000 : ℝ)
  | 18 => (3457975251 / 10000000000 : ℝ)
  | 19 => (687747053 / 2000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch031Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (193546323 / 500000000 : ℝ)
  | 1 => (385021429 / 1000000000 : ℝ)
  | 2 => (239348121 / 625000000 : ℝ)
  | 3 => (476124181 / 1250000000 : ℝ)
  | 4 => (3788484879 / 10000000000 : ℝ)
  | 5 => (1884022137 / 5000000000 : ℝ)
  | 6 => (1873835841 / 5000000000 : ℝ)
  | 7 => (931841787 / 2500000000 : ℝ)
  | 8 => (1853565357 / 5000000000 : ℝ)
  | 9 => (3686962421 / 10000000000 : ℝ)
  | 10 => (3666862307 / 10000000000 : ℝ)
  | 11 => (3646830411 / 10000000000 : ℝ)
  | 12 => (226679173 / 625000000 : ℝ)
  | 13 => (360697141 / 1000000000 : ℝ)
  | 14 => (3587144373 / 10000000000 : ℝ)
  | 15 => (1783692841 / 5000000000 : ℝ)
  | 16 => (3547695369 / 10000000000 : ℝ)
  | 17 => (3528073457 / 10000000000 : ℝ)
  | 18 => (877129993 / 2500000000 : ℝ)
  | 19 => (3489034937 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch031_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch031Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch031Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell620_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell621_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell622_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell623_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell624_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell625_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell626_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell627_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell628_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell629_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell630_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell631_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell632_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell633_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell634_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell635_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell636_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell637_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell638_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell639_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper] at h ⊢
    exact h

end HodgeProofHP
