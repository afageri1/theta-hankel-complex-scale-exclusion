import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell440_leftExp :
    (8666265089 / 5000000000 : ℝ) ≤ Real.exp (11 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 20 : ℝ) (1017336054953 / 1000000000000 : ℝ)
    (8666265089 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell440_rightExp :
    Real.exp (441 / 800 : ℝ) ≤ (17354209389 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (441 / 800 : ℝ) (50868789771 / 50000000000 : ℝ)
    (17354209389 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell440_denomUpper :
    Real.exp (53144862737016677 / 10000000000000000 : ℝ) ≤ (406520132531 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53144862737016677 / 10000000000000000 : ℝ) (590332415579
    / 500000000000 : ℝ) (406520132531 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell440_denomLower :
    (403633987279 / 2000000000 : ℝ) ≤ Real.exp (3317100821685211 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3317100821685211 / 625000000000000 : ℝ) (1180401979529 /
    1000000000000 : ℝ) (403633987279 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell440_product_lower :
    (3403233634185211 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell440_leftExp
    (by norm_num : (0 : ℝ) ≤ (8666265089 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell440_product_upper :
    Real.pi * Real.exp (441 / 800 : ℝ) ≤ (54519862737016677 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell440_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell440_endpointLower :
    (422752143 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 40 : ℝ) (441 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3403233634185211 / 625000000000000 : ℝ) (Real.pi * Real.exp (11 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell440_product_lower
  have hD : Real.exp (Real.pi * Real.exp (441 / 800 : ℝ) - (11 / 80 : ℝ)) ≤
      (406520132531 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell440_denomUpper
    linarith [hpThetaJensenCell440_product_upper]
  have hi : (1 / (406520132531 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (441 / 800 : ℝ) - (11 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (406520132531 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (406520132531 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 80 : ℝ) - Real.pi * Real.exp (441 / 800 : ℝ)) := by
    rw [show (11 / 80 : ℝ) - Real.pi * Real.exp (441 / 800 : ℝ) =
      -(Real.pi * Real.exp (441 / 800 : ℝ) - (11 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 20 : ℝ)) := by
    have h := hpThetaJensenCell440_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (406520132531 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell440_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 40 : ℝ) (441 / 1600 : ℝ) ≤ (1712673803 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (441 / 800 : ℝ)) (54519862737016677 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (441 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell440_product_upper
  have hD : (403633987279 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 20 : ℝ) - (441 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell440_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell440_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 20 : ℝ) - (441 / 3200 : ℝ)) ≤
      (1 / (403633987279 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (403633987279 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((441 / 3200 : ℝ) - Real.pi * Real.exp (11 / 20 : ℝ)) ≤
      (2 / (403633987279 / 2000000000 : ℝ) : ℝ) := by
    rw [show (441 / 3200 : ℝ) - Real.pi * Real.exp (11 / 20 : ℝ) =
      -(Real.pi * Real.exp (11 / 20 : ℝ) - (441 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54519862737016677 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (54519862737016677 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell440_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 40 : ℝ) (441 / 1600 : ℝ)) :
    (422752143 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1712673803 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell440_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell440_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell441_leftExp :
    (17354209387 / 10000000000 : ℝ) ≤ Real.exp (441 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (441 / 800 : ℝ) (1017375795419 / 1000000000000 : ℝ)
    (17354209387 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell441_rightExp :
    Real.exp (221 / 400 : ℝ) ≤ (8687957857 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (221 / 400 : ℝ) (508707768719 / 500000000000 : ℝ)
    (8687957857 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell441_denomUpper :
    Real.exp (26604965087846201 / 5000000000000000 : ℝ) ≤ (255733674481 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (26604965087846201 / 5000000000000000 : ℝ) (1180904926931
    / 1000000000000 : ℝ) (255733674481 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell441_denomLower :
    (81253086303 / 400000000 : ℝ) ≤ Real.exp (6642324422065513 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6642324422065513 / 1250000000000000 : ℝ) (118064170747 /
    100000000000 : ℝ) (81253086303 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell441_product_lower :
    (6814980672065513 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (441 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell441_leftExp
    (by norm_num : (0 : ℝ) ≤ (17354209387 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell441_product_upper :
    Real.pi * Real.exp (221 / 400 : ℝ) ≤ (27294027587846201 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell441_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell441_endpointLower :
    (8425233257 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (441 / 1600 : ℝ) (221 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6814980672065513 / 1250000000000000 : ℝ) (Real.pi * Real.exp (441 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell441_product_lower
  have hD : Real.exp (Real.pi * Real.exp (221 / 400 : ℝ) - (441 / 3200 : ℝ)) ≤
      (255733674481 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell441_denomUpper
    linarith [hpThetaJensenCell441_product_upper]
  have hi : (1 / (255733674481 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (221 / 400 : ℝ) - (441 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (255733674481 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (255733674481 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((441 / 3200 : ℝ) - Real.pi * Real.exp (221 / 400 : ℝ)) := by
    rw [show (441 / 3200 : ℝ) - Real.pi * Real.exp (221 / 400 : ℝ) =
      -(Real.pi * Real.exp (221 / 400 : ℝ) - (441 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (441 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (441 / 800 : ℝ)) := by
    have h := hpThetaJensenCell441_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (255733674481 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell441_endpointUpper :
    hpThetaJensenKernelEndpointUpper (441 / 1600 : ℝ) (221 / 800 : ℝ) ≤ (8533243219 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (221 / 400 : ℝ)) (27294027587846201 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (221 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell441_product_upper
  have hD : (81253086303 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (441 / 800 : ℝ) - (221 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell441_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell441_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (441 / 800 : ℝ) - (221 / 1600 : ℝ)) ≤
      (1 / (81253086303 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (81253086303 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((221 / 1600 : ℝ) - Real.pi * Real.exp (441 / 800 : ℝ)) ≤
      (2 / (81253086303 / 400000000 : ℝ) : ℝ) := by
    rw [show (221 / 1600 : ℝ) - Real.pi * Real.exp (441 / 800 : ℝ) =
      -(Real.pi * Real.exp (441 / 800 : ℝ) - (221 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27294027587846201 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (27294027587846201 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell441_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (441 / 1600 : ℝ) (221 / 800 : ℝ)) :
    (8425233257 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8533243219 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell441_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell441_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell442_leftExp :
    (271498683 / 156250000 : ℝ) ≤ Real.exp (221 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (221 / 400 : ℝ) (1017415537437 / 1000000000000 : ℝ)
    (271498683 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell442_rightExp :
    Real.exp (443 / 800 : ℝ) ≤ (17397649189 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (443 / 800 : ℝ) (1017455281009 / 1000000000000 : ℝ)
    (17397649189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell442_denomUpper :
    Real.exp (53275082908618077 / 10000000000000000 : ℝ) ≤ (2059242310871 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53275082908618077 / 10000000000000000 : ℝ)
    (1181145386357 / 1000000000000 : ℝ) (2059242310871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell442_denomLower :
    (2044587572967 / 10000000000 : ℝ) ≤ Real.exp (51956701946771 / 9765625000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51956701946771 / 9765625000000 : ℝ) (1180881798461 /
    1000000000000 : ℝ) (2044587572967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell442_product_lower :
    (106617261315417 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (221 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell442_leftExp
    (by norm_num : (0 : ℝ) ≤ (271498683 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell442_product_upper :
    Real.pi * Real.exp (443 / 800 : ℝ) ≤ (54656332908618077 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell442_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell442_endpointLower :
    (335818011 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (221 / 800 : ℝ) (443 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (106617261315417 / 19531250000000 : ℝ) (Real.pi * Real.exp (221 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell442_product_lower
  have hD : Real.exp (Real.pi * Real.exp (443 / 800 : ℝ) - (221 / 1600 : ℝ)) ≤
      (2059242310871 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell442_denomUpper
    linarith [hpThetaJensenCell442_product_upper]
  have hi : (1 / (2059242310871 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (443 / 800 : ℝ) - (221 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2059242310871 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2059242310871 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((221 / 1600 : ℝ) - Real.pi * Real.exp (443 / 800 : ℝ)) := by
    rw [show (221 / 1600 : ℝ) - Real.pi * Real.exp (443 / 800 : ℝ) =
      -(Real.pi * Real.exp (443 / 800 : ℝ) - (221 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (221 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (221 / 400 : ℝ)) := by
    have h := hpThetaJensenCell442_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2059242310871 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell442_endpointUpper :
    hpThetaJensenKernelEndpointUpper (221 / 800 : ℝ) (443 / 1600 : ℝ) ≤ (8503144027 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (443 / 800 : ℝ)) (54656332908618077 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (443 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell442_product_upper
  have hD : (2044587572967 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (221 / 400 : ℝ) - (443 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell442_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell442_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (221 / 400 : ℝ) - (443 / 3200 : ℝ)) ≤
      (1 / (2044587572967 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2044587572967 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((443 / 3200 : ℝ) - Real.pi * Real.exp (221 / 400 : ℝ)) ≤
      (2 / (2044587572967 / 10000000000 : ℝ) : ℝ) := by
    rw [show (443 / 3200 : ℝ) - Real.pi * Real.exp (221 / 400 : ℝ) =
      -(Real.pi * Real.exp (221 / 400 : ℝ) - (443 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54656332908618077 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (54656332908618077 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell442_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (221 / 800 : ℝ) (443 / 1600 : ℝ)) :
    (335818011 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8503144027 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell442_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell442_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell443_leftExp :
    (4349412297 / 2500000000 : ℝ) ≤ Real.exp (443 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (443 / 800 : ℝ) (63590955063 / 62500000000 : ℝ)
    (4349412297 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell443_rightExp :
    Real.exp (111 / 200 : ℝ) ≤ (2177426231 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (111 / 200 : ℝ) (254373756533 / 250000000000 : ℝ)
    (2177426231 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell443_denomUpper :
    Real.exp (6667540130325983 / 1250000000000000 : ℝ) ≤ (8290881359 / 40000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6667540130325983 / 1250000000000000 : ℝ) (1181386210033
    / 1000000000000 : ℝ) (8290881359 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell443_denomLower :
    (2057952105479 / 10000000000 : ℝ) ≤ Real.exp (1664650484619603 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1664650484619603 / 312500000000000 : ℝ) (1181122253109 /
    1000000000000 : ℝ) (2057952105479 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell443_product_lower :
    (1708009859619603 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (443 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell443_leftExp
    (by norm_num : (0 : ℝ) ≤ (4349412297 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell443_product_upper :
    Real.pi * Real.exp (111 / 200 : ℝ) ≤ (6840587005325983 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell443_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell443_endpointLower :
    (8365694303 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (443 / 1600 : ℝ) (111 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1708009859619603 / 312500000000000 : ℝ) (Real.pi * Real.exp (443 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell443_product_lower
  have hD : Real.exp (Real.pi * Real.exp (111 / 200 : ℝ) - (443 / 3200 : ℝ)) ≤
      (8290881359 / 40000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell443_denomUpper
    linarith [hpThetaJensenCell443_product_upper]
  have hi : (1 / (8290881359 / 40000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (111 / 200 : ℝ) - (443 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8290881359 / 40000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8290881359 / 40000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((443 / 3200 : ℝ) - Real.pi * Real.exp (111 / 200 : ℝ)) := by
    rw [show (443 / 3200 : ℝ) - Real.pi * Real.exp (111 / 200 : ℝ) =
      -(Real.pi * Real.exp (111 / 200 : ℝ) - (443 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (443 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (443 / 800 : ℝ)) := by
    have h := hpThetaJensenCell443_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8290881359 / 40000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell443_endpointUpper :
    hpThetaJensenKernelEndpointUpper (443 / 1600 : ℝ) (111 / 400 : ℝ) ≤ (8473071827 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (111 / 200 : ℝ)) (6840587005325983 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (111 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell443_product_upper
  have hD : (2057952105479 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (443 / 800 : ℝ) - (111 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell443_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell443_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (443 / 800 : ℝ) - (111 / 800 : ℝ)) ≤
      (1 / (2057952105479 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2057952105479 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((111 / 800 : ℝ) - Real.pi * Real.exp (443 / 800 : ℝ)) ≤
      (2 / (2057952105479 / 10000000000 : ℝ) : ℝ) := by
    rw [show (111 / 800 : ℝ) - Real.pi * Real.exp (443 / 800 : ℝ) =
      -(Real.pi * Real.exp (443 / 800 : ℝ) - (111 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6840587005325983 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (6840587005325983 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell443_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (443 / 1600 : ℝ) (111 / 400 : ℝ)) :
    (8365694303 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8473071827 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell443_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell443_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell444_leftExp :
    (17419409847 / 10000000000 : ℝ) ≤ Real.exp (111 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (111 / 200 : ℝ) (1017495026131 / 1000000000000 : ℝ)
    (17419409847 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell444_rightExp :
    Real.exp (89 / 160 : ℝ) ≤ (697647909 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89 / 160 : ℝ) (127191846601 / 125000000000 : ℝ)
    (697647909 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell444_denomUpper :
    Real.exp (2136225787379037 / 400000000000000 : ℝ) ≤ (2086304423647 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2136225787379037 / 400000000000000 : ℝ) (236325479711 /
    200000000000 : ℝ) (2086304423647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell444_denomLower :
    (1035710842637 / 5000000000 : ℝ) ≤ Real.exp (6666756702507053 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6666756702507053 / 1250000000000000 : ℝ) (295340767997 /
    250000000000 : ℝ) (1035710842637 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell444_product_lower :
    (6840584827507053 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (111 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell444_leftExp
    (by norm_num : (0 : ℝ) ≤ (17419409847 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell444_product_upper :
    Real.pi * Real.exp (89 / 160 : ℝ) ≤ (2191725787379037 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell444_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell444_endpointLower :
    (2083991431 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (111 / 400 : ℝ) (89 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6840584827507053 / 1250000000000000 : ℝ) (Real.pi * Real.exp (111 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell444_product_lower
  have hD : Real.exp (Real.pi * Real.exp (89 / 160 : ℝ) - (111 / 800 : ℝ)) ≤
      (2086304423647 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell444_denomUpper
    linarith [hpThetaJensenCell444_product_upper]
  have hi : (1 / (2086304423647 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (89 / 160 : ℝ) - (111 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2086304423647 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2086304423647 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((111 / 800 : ℝ) - Real.pi * Real.exp (89 / 160 : ℝ)) := by
    rw [show (111 / 800 : ℝ) - Real.pi * Real.exp (89 / 160 : ℝ) =
      -(Real.pi * Real.exp (89 / 160 : ℝ) - (111 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (111 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (111 / 200 : ℝ)) := by
    have h := hpThetaJensenCell444_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2086304423647 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell444_endpointUpper :
    hpThetaJensenKernelEndpointUpper (111 / 400 : ℝ) (89 / 320 : ℝ) ≤ (8443027017 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (89 / 160 : ℝ)) (2191725787379037 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (89 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell444_product_upper
  have hD : (1035710842637 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (111 / 200 : ℝ) - (89 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell444_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell444_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (111 / 200 : ℝ) - (89 / 640 : ℝ)) ≤
      (1 / (1035710842637 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1035710842637 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((89 / 640 : ℝ) - Real.pi * Real.exp (111 / 200 : ℝ)) ≤
      (2 / (1035710842637 / 5000000000 : ℝ) : ℝ) := by
    rw [show (89 / 640 : ℝ) - Real.pi * Real.exp (111 / 200 : ℝ) =
      -(Real.pi * Real.exp (111 / 200 : ℝ) - (89 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2191725787379037 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2191725787379037 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell444_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (111 / 400 : ℝ) (89 / 320 : ℝ)) :
    (2083991431 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8443027017 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell444_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell444_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell445_leftExp :
    (4360299431 / 2500000000 : ℝ) ≤ Real.exp (89 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (89 / 160 : ℝ) (1017534772807 / 1000000000000 : ℝ)
    (4360299431 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell445_rightExp :
    Real.exp (223 / 400 : ℝ) ≤ (8731506427 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (223 / 400 : ℝ) (254393630259 / 250000000000 : ℝ)
    (8731506427 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell445_denomUpper :
    Real.exp (26735526970518211 / 5000000000000000 : ℝ) ≤ (1049997756563 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (26735526970518211 / 5000000000000000 : ℝ) (1181868952521
    / 1000000000000 : ℝ) (1049997756563 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell445_denomLower :
    (2084997253533 / 10000000000 : ℝ) ≤ Real.exp (1668730538754269 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1668730538754269 / 312500000000000 : ℝ) (236320851141 /
    200000000000 : ℝ) (2084997253533 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell445_product_lower :
    (1712285226254269 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (89 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell445_leftExp
    (by norm_num : (0 : ℝ) ≤ (4360299431 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell445_product_upper :
    Real.pi * Real.exp (223 / 400 : ℝ) ≤ (27430839470518211 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell445_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell445_endpointLower :
    (2076566231 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 320 : ℝ) (223 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1712285226254269 / 312500000000000 : ℝ) (Real.pi * Real.exp (89 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell445_product_lower
  have hD : Real.exp (Real.pi * Real.exp (223 / 400 : ℝ) - (89 / 640 : ℝ)) ≤
      (1049997756563 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell445_denomUpper
    linarith [hpThetaJensenCell445_product_upper]
  have hi : (1 / (1049997756563 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (223 / 400 : ℝ) - (89 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1049997756563 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1049997756563 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((89 / 640 : ℝ) - Real.pi * Real.exp (223 / 400 : ℝ)) := by
    rw [show (89 / 640 : ℝ) - Real.pi * Real.exp (223 / 400 : ℝ) =
      -(Real.pi * Real.exp (223 / 400 : ℝ) - (89 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (89 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (89 / 160 : ℝ)) := by
    have h := hpThetaJensenCell445_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1049997756563 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell445_endpointUpper :
    hpThetaJensenKernelEndpointUpper (89 / 320 : ℝ) (223 / 800 : ℝ) ≤ (8413009983 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (223 / 400 : ℝ)) (27430839470518211 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (223 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell445_product_upper
  have hD : (2084997253533 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (89 / 160 : ℝ) - (223 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell445_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell445_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (89 / 160 : ℝ) - (223 / 1600 : ℝ)) ≤
      (1 / (2084997253533 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2084997253533 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((223 / 1600 : ℝ) - Real.pi * Real.exp (89 / 160 : ℝ)) ≤
      (2 / (2084997253533 / 10000000000 : ℝ) : ℝ) := by
    rw [show (223 / 1600 : ℝ) - Real.pi * Real.exp (89 / 160 : ℝ) =
      -(Real.pi * Real.exp (89 / 160 : ℝ) - (223 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27430839470518211 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (27430839470518211 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell445_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (89 / 320 : ℝ) (223 / 800 : ℝ)) :
    (2076566231 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8413009983 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell445_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell445_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell446_leftExp :
    (4365753213 / 2500000000 : ℝ) ≤ Real.exp (223 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (223 / 400 : ℝ) (203514904207 / 200000000000 : ℝ)
    (4365753213 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell446_rightExp :
    Real.exp (447 / 800 : ℝ) ≤ (17484855269 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (447 / 800 : ℝ) (1017614270817 / 1000000000000 : ℝ)
    (17484855269 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell446_denomUpper :
    Real.exp (53536548919103517 / 10000000000000000 : ℝ) ≤ (105689728413 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53536548919103517 / 10000000000000000 : ℝ)
    (1182110872531 / 1000000000000 : ℝ) (105689728413 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell446_denomLower :
    (2098679759713 / 10000000000 : ℝ) ≤ Real.exp (1670774577241887 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1670774577241887 / 312500000000000 : ℝ) (1181845804849 /
    1000000000000 : ℝ) (2098679759713 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell446_product_lower :
    (1714426920991887 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (223 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell446_leftExp
    (by norm_num : (0 : ℝ) ≤ (4365753213 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell446_product_upper :
    Real.pi * Real.exp (447 / 800 : ℝ) ≤ (54930298919103517 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell446_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell446_endpointLower :
    (4138296143 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (223 / 800 : ℝ) (447 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1714426920991887 / 312500000000000 : ℝ) (Real.pi * Real.exp (223 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell446_product_lower
  have hD : Real.exp (Real.pi * Real.exp (447 / 800 : ℝ) - (223 / 1600 : ℝ)) ≤
      (105689728413 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell446_denomUpper
    linarith [hpThetaJensenCell446_product_upper]
  have hi : (1 / (105689728413 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (447 / 800 : ℝ) - (223 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (105689728413 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (105689728413 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((223 / 1600 : ℝ) - Real.pi * Real.exp (447 / 800 : ℝ)) := by
    rw [show (223 / 1600 : ℝ) - Real.pi * Real.exp (447 / 800 : ℝ) =
      -(Real.pi * Real.exp (447 / 800 : ℝ) - (223 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (223 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (223 / 400 : ℝ)) := by
    have h := hpThetaJensenCell446_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (105689728413 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell446_endpointUpper :
    hpThetaJensenKernelEndpointUpper (223 / 800 : ℝ) (447 / 1600 : ℝ) ≤ (4191510557 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (447 / 800 : ℝ)) (54930298919103517 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (447 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell446_product_upper
  have hD : (2098679759713 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (223 / 400 : ℝ) - (447 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell446_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell446_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (223 / 400 : ℝ) - (447 / 3200 : ℝ)) ≤
      (1 / (2098679759713 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2098679759713 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((447 / 3200 : ℝ) - Real.pi * Real.exp (223 / 400 : ℝ)) ≤
      (2 / (2098679759713 / 10000000000 : ℝ) : ℝ) := by
    rw [show (447 / 3200 : ℝ) - Real.pi * Real.exp (223 / 400 : ℝ) =
      -(Real.pi * Real.exp (223 / 400 : ℝ) - (447 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54930298919103517 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (54930298919103517 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell446_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (223 / 800 : ℝ) (447 / 1600 : ℝ)) :
    (4138296143 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4191510557 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell446_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell446_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell447_leftExp :
    (17484855267 / 10000000000 : ℝ) ≤ Real.exp (447 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (447 / 800 : ℝ) (31800445963 / 31250000000 : ℝ)
    (17484855267 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell447_rightExp :
    Real.exp (14 / 25 : ℝ) ≤ (4376681251 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14 / 25 : ℝ) (1017654022151 / 1000000000000 : ℝ)
    (4376681251 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell447_denomUpper :
    Real.exp (13400532431372843 / 2500000000000000 : ℝ) ≤ (1063851279251 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13400532431372843 / 2500000000000000 : ℝ) (1182353159183
    / 1000000000000 : ℝ) (1063851279251 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell447_denomLower :
    (2112470164419 / 10000000000 : ℝ) ≤ Real.exp (6691285178495633 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6691285178495633 / 1250000000000000 : ℝ) (29552193001 /
    25000000000 : ℝ) (2112470164419 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell447_product_lower :
    (6866285178495633 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (447 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell447_leftExp
    (by norm_num : (0 : ℝ) ≤ (17484855267 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell447_product_upper :
    Real.pi * Real.exp (14 / 25 : ℝ) ≤ (13749751181372843 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell447_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell447_endpointLower :
    (8246948193 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (447 / 1600 : ℝ) (7 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6866285178495633 / 1250000000000000 : ℝ) (Real.pi * Real.exp (447 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell447_product_lower
  have hD : Real.exp (Real.pi * Real.exp (14 / 25 : ℝ) - (447 / 3200 : ℝ)) ≤
      (1063851279251 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell447_denomUpper
    linarith [hpThetaJensenCell447_product_upper]
  have hi : (1 / (1063851279251 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (14 / 25 : ℝ) - (447 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1063851279251 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1063851279251 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((447 / 3200 : ℝ) - Real.pi * Real.exp (14 / 25 : ℝ)) := by
    rw [show (447 / 3200 : ℝ) - Real.pi * Real.exp (14 / 25 : ℝ) =
      -(Real.pi * Real.exp (14 / 25 : ℝ) - (447 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (447 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (447 / 800 : ℝ)) := by
    have h := hpThetaJensenCell447_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1063851279251 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell447_endpointUpper :
    hpThetaJensenKernelEndpointUpper (447 / 1600 : ℝ) (7 / 25 : ℝ) ≤ (8353060791 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (14 / 25 : ℝ)) (13749751181372843 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell447_product_upper
  have hD : (2112470164419 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (447 / 800 : ℝ) - (7 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell447_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell447_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (447 / 800 : ℝ) - (7 / 50 : ℝ)) ≤
      (1 / (2112470164419 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2112470164419 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 50 : ℝ) - Real.pi * Real.exp (447 / 800 : ℝ)) ≤
      (2 / (2112470164419 / 10000000000 : ℝ) : ℝ) := by
    rw [show (7 / 50 : ℝ) - Real.pi * Real.exp (447 / 800 : ℝ) =
      -(Real.pi * Real.exp (447 / 800 : ℝ) - (7 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13749751181372843 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (13749751181372843 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell447_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (447 / 1600 : ℝ) (7 / 25 : ℝ)) :
    (8246948193 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8353060791 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell447_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell447_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell448_leftExp :
    (8753362501 / 5000000000 : ℝ) ≤ Real.exp (14 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14 / 25 : ℝ) (20353080443 / 20000000000 : ℝ) (8753362501
    / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell448_rightExp :
    Real.exp (449 / 800 : ℝ) ≤ (17528622093 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (449 / 800 : ℝ) (508846887519 / 500000000000 : ℝ)
    (17528622093 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell448_denomUpper :
    Real.exp (53667796467014149 / 10000000000000000 : ℝ) ≤ (1070860231507 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53667796467014149 / 10000000000000000 : ℝ)
    (1182595813077 / 1000000000000 : ℝ) (1070860231507 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell448_denomLower :
    (212636943593 / 1000000000 : ℝ) ≤ Real.exp (3349741388280199 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3349741388280199 / 625000000000000 : ℝ) (591165000933 /
    500000000000 : ℝ) (212636943593 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell448_product_lower :
    (3437436700780199 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (14 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell448_leftExp
    (by norm_num : (0 : ℝ) ≤ (8753362501 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell448_product_upper :
    Real.pi * Real.exp (449 / 800 : ℝ) ≤ (55067796467014149 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell448_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell448_endpointLower :
    (256791657 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 25 : ℝ) (449 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3437436700780199 / 625000000000000 : ℝ) (Real.pi * Real.exp (14 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell448_product_lower
  have hD : Real.exp (Real.pi * Real.exp (449 / 800 : ℝ) - (7 / 50 : ℝ)) ≤
      (1070860231507 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell448_denomUpper
    linarith [hpThetaJensenCell448_product_upper]
  have hi : (1 / (1070860231507 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (449 / 800 : ℝ) - (7 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1070860231507 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1070860231507 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 50 : ℝ) - Real.pi * Real.exp (449 / 800 : ℝ)) := by
    rw [show (7 / 50 : ℝ) - Real.pi * Real.exp (449 / 800 : ℝ) =
      -(Real.pi * Real.exp (449 / 800 : ℝ) - (7 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (14 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (14 / 25 : ℝ)) := by
    have h := hpThetaJensenCell448_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1070860231507 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell448_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 25 : ℝ) (449 / 1600 : ℝ) ≤ (4161564701 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (449 / 800 : ℝ)) (55067796467014149 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (449 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell448_product_upper
  have hD : (212636943593 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (14 / 25 : ℝ) - (449 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell448_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell448_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (14 / 25 : ℝ) - (449 / 3200 : ℝ)) ≤
      (1 / (212636943593 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (212636943593 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((449 / 3200 : ℝ) - Real.pi * Real.exp (14 / 25 : ℝ)) ≤
      (2 / (212636943593 / 1000000000 : ℝ) : ℝ) := by
    rw [show (449 / 3200 : ℝ) - Real.pi * Real.exp (14 / 25 : ℝ) =
      -(Real.pi * Real.exp (14 / 25 : ℝ) - (449 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55067796467014149 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (55067796467014149 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell448_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 25 : ℝ) (449 / 1600 : ℝ)) :
    (256791657 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4161564701 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell448_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell448_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell449_leftExp :
    (17528622091 / 10000000000 : ℝ) ≤ Real.exp (449 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (449 / 800 : ℝ) (1017693775037 / 1000000000000 : ℝ)
    (17528622091 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell449_rightExp :
    Real.exp (9 / 16 : ℝ) ≤ (1755054657 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 16 : ℝ) (1017733529477 / 1000000000000 : ℝ)
    (1755054657 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell449_denomUpper :
    Real.exp (5373354925048601 / 1000000000000000 : ℝ) ≤ (2155849270719 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5373354925048601 / 1000000000000000 : ℝ) (591419417407 /
    500000000000 : ℝ) (2155849270719 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell449_denomLower :
    (535094638199 / 2500000000 : ℝ) ≤ Real.exp (6707691116513609 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6707691116513609 / 1250000000000000 : ℝ) (1182572650927
    / 1000000000000 : ℝ) (535094638199 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell449_product_lower :
    (6883472366513609 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (449 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell449_leftExp
    (by norm_num : (0 : ℝ) ≤ (17528622091 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell449_product_upper :
    Real.pi * Real.exp (9 / 16 : ℝ) ≤ (5513667425048601 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell449_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell449_endpointLower :
    (4093873579 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (449 / 1600 : ℝ) (9 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6883472366513609 / 1250000000000000 : ℝ) (Real.pi * Real.exp (449 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell449_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 16 : ℝ) - (449 / 3200 : ℝ)) ≤
      (2155849270719 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell449_denomUpper
    linarith [hpThetaJensenCell449_product_upper]
  have hi : (1 / (2155849270719 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 16 : ℝ) - (449 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2155849270719 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2155849270719 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((449 / 3200 : ℝ) - Real.pi * Real.exp (9 / 16 : ℝ)) := by
    rw [show (449 / 3200 : ℝ) - Real.pi * Real.exp (9 / 16 : ℝ) =
      -(Real.pi * Real.exp (9 / 16 : ℝ) - (449 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (449 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (449 / 800 : ℝ)) := by
    have h := hpThetaJensenCell449_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2155849270719 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell449_endpointUpper :
    hpThetaJensenKernelEndpointUpper (449 / 1600 : ℝ) (9 / 32 : ℝ) ≤ (8293227329 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 16 : ℝ)) (5513667425048601 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell449_product_upper
  have hD : (535094638199 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (449 / 800 : ℝ) - (9 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell449_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell449_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (449 / 800 : ℝ) - (9 / 64 : ℝ)) ≤
      (1 / (535094638199 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (535094638199 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 64 : ℝ) - Real.pi * Real.exp (449 / 800 : ℝ)) ≤
      (2 / (535094638199 / 2500000000 : ℝ) : ℝ) := by
    rw [show (9 / 64 : ℝ) - Real.pi * Real.exp (449 / 800 : ℝ) =
      -(Real.pi * Real.exp (449 / 800 : ℝ) - (9 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5513667425048601 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5513667425048601 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell449_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (449 / 1600 : ℝ) (9 / 32 : ℝ)) :
    (4093873579 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8293227329 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell449_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell449_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell450_leftExp :
    (17550546569 / 10000000000 : ℝ) ≤ Real.exp (9 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 16 : ℝ) (254433382369 / 250000000000 : ℝ)
    (17550546569 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell450_rightExp :
    Real.exp (451 / 800 : ℝ) ≤ (17572498471 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (451 / 800 : ℝ) (101777328547 / 100000000000 : ℝ)
    (17572498471 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell450_denomUpper :
    Real.exp (53799388189004303 / 10000000000000000 : ℝ) ≤ (2170089981751 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53799388189004303 / 10000000000000000 : ℝ)
    (1183082225019 / 1000000000000 : ℝ) (2170089981751 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell450_denomLower :
    (2154498503903 / 10000000000 : ℝ) ≤ Real.exp (6715910212099731 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6715910212099731 / 1250000000000000 : ℝ) (591407833917 /
    500000000000 : ℝ) (2154498503903 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell450_product_lower :
    (6892082087099731 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell450_leftExp
    (by norm_num : (0 : ℝ) ≤ (17550546569 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell450_product_upper :
    Real.pi * Real.exp (451 / 800 : ℝ) ≤ (55205638189004303 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell450_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell450_endpointLower :
    (1019773871 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 32 : ℝ) (451 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6892082087099731 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell450_product_lower
  have hD : Real.exp (Real.pi * Real.exp (451 / 800 : ℝ) - (9 / 64 : ℝ)) ≤
      (2170089981751 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell450_denomUpper
    linarith [hpThetaJensenCell450_product_upper]
  have hi : (1 / (2170089981751 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (451 / 800 : ℝ) - (9 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2170089981751 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2170089981751 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 64 : ℝ) - Real.pi * Real.exp (451 / 800 : ℝ)) := by
    rw [show (9 / 64 : ℝ) - Real.pi * Real.exp (451 / 800 : ℝ) =
      -(Real.pi * Real.exp (451 / 800 : ℝ) - (9 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 16 : ℝ)) := by
    have h := hpThetaJensenCell450_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2170089981751 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell450_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 32 : ℝ) (451 / 1600 : ℝ) ≤ (1652670991 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (451 / 800 : ℝ)) (55205638189004303 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (451 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell450_product_upper
  have hD : (2154498503903 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 16 : ℝ) - (451 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell450_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell450_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 16 : ℝ) - (451 / 3200 : ℝ)) ≤
      (1 / (2154498503903 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2154498503903 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((451 / 3200 : ℝ) - Real.pi * Real.exp (9 / 16 : ℝ)) ≤
      (2 / (2154498503903 / 10000000000 : ℝ) : ℝ) := by
    rw [show (451 / 3200 : ℝ) - Real.pi * Real.exp (9 / 16 : ℝ) =
      -(Real.pi * Real.exp (9 / 16 : ℝ) - (451 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55205638189004303 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (55205638189004303 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell450_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 32 : ℝ) (451 / 1600 : ℝ)) :
    (1019773871 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1652670991 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell450_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell450_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell451_leftExp :
    (17572498469 / 10000000000 : ℝ) ≤ Real.exp (451 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (451 / 800 : ℝ) (1017773285469 / 1000000000000 : ℝ)
    (17572498469 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell451_rightExp :
    Real.exp (113 / 200 : ℝ) ≤ (4398619457 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (113 / 200 : ℝ) (203562608603 / 200000000000 : ℝ)
    (4398619457 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell451_denomUpper :
    Real.exp (13466328345775001 / 2500000000000000 : ℝ) ≤ (13652772521 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13466328345775001 / 2500000000000000 : ℝ) (1183325984269
    / 1000000000000 : ℝ) (13652772521 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell451_denomLower :
    (433746057367 / 2000000000 : ℝ) ≤ Real.exp (6724140076277831 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6724140076277831 / 1250000000000000 : ℝ) (1183059053179
    / 1000000000000 : ℝ) (433746057367 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell451_product_lower :
    (6900702576277831 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (451 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell451_leftExp
    (by norm_num : (0 : ℝ) ≤ (17572498469 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell451_product_upper :
    Real.pi * Real.exp (113 / 200 : ℝ) ≤ (13818672095775001 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell451_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell451_endpointLower :
    (4064332417 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (451 / 1600 : ℝ) (113 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6900702576277831 / 1250000000000000 : ℝ) (Real.pi * Real.exp (451 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell451_product_lower
  have hD : Real.exp (Real.pi * Real.exp (113 / 200 : ℝ) - (451 / 3200 : ℝ)) ≤
      (13652772521 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell451_denomUpper
    linarith [hpThetaJensenCell451_product_upper]
  have hi : (1 / (13652772521 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (113 / 200 : ℝ) - (451 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13652772521 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13652772521 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((451 / 3200 : ℝ) - Real.pi * Real.exp (113 / 200 : ℝ)) := by
    rw [show (451 / 3200 : ℝ) - Real.pi * Real.exp (113 / 200 : ℝ) =
      -(Real.pi * Real.exp (113 / 200 : ℝ) - (451 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (451 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (451 / 800 : ℝ)) := by
    have h := hpThetaJensenCell451_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13652772521 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell451_endpointUpper :
    hpThetaJensenKernelEndpointUpper (451 / 1600 : ℝ) (113 / 400 : ℝ) ≤ (8233512659 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (113 / 200 : ℝ)) (13818672095775001 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (113 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell451_product_upper
  have hD : (433746057367 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (451 / 800 : ℝ) - (113 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell451_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell451_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (451 / 800 : ℝ) - (113 / 800 : ℝ)) ≤
      (1 / (433746057367 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (433746057367 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((113 / 800 : ℝ) - Real.pi * Real.exp (451 / 800 : ℝ)) ≤
      (2 / (433746057367 / 2000000000 : ℝ) : ℝ) := by
    rw [show (113 / 800 : ℝ) - Real.pi * Real.exp (451 / 800 : ℝ) =
      -(Real.pi * Real.exp (451 / 800 : ℝ) - (113 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13818672095775001 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (13818672095775001 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell451_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (451 / 1600 : ℝ) (113 / 400 : ℝ)) :
    (4064332417 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8233512659 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell451_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell451_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell452_leftExp :
    (8797238913 / 5000000000 : ℝ) ≤ Real.exp (113 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (113 / 200 : ℝ) (508906521507 / 500000000000 : ℝ)
    (8797238913 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell452_rightExp :
    Real.exp (453 / 800 : ℝ) ≤ (17616484677 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (453 / 800 : ℝ) (508926401057 / 500000000000 : ℝ)
    (17616484677 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell452_denomUpper :
    Real.exp (53931324945870461 / 10000000000000000 : ℝ) ≤ (1099455577843 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53931324945870461 / 10000000000000000 : ℝ) (118357011319
    / 100000000000 : ℝ) (1099455577843 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell452_denomLower :
    (2183074910191 / 10000000000 : ℝ) ≤ Real.exp (3366190361396187 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3366190361396187 / 625000000000000 : ℝ) (1183302807573 /
    1000000000000 : ℝ) (2183074910191 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell452_product_lower :
    (3454666923896187 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (113 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell452_leftExp
    (by norm_num : (0 : ℝ) ≤ (8797238913 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell452_product_upper :
    Real.pi * Real.exp (453 / 800 : ℝ) ≤ (55343824945870461 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell452_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell452_endpointLower :
    (8099169127 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (113 / 400 : ℝ) (453 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3454666923896187 / 625000000000000 : ℝ) (Real.pi * Real.exp (113 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell452_product_lower
  have hD : Real.exp (Real.pi * Real.exp (453 / 800 : ℝ) - (113 / 800 : ℝ)) ≤
      (1099455577843 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell452_denomUpper
    linarith [hpThetaJensenCell452_product_upper]
  have hi : (1 / (1099455577843 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (453 / 800 : ℝ) - (113 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1099455577843 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1099455577843 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((113 / 800 : ℝ) - Real.pi * Real.exp (453 / 800 : ℝ)) := by
    rw [show (113 / 800 : ℝ) - Real.pi * Real.exp (453 / 800 : ℝ) =
      -(Real.pi * Real.exp (453 / 800 : ℝ) - (113 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (113 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (113 / 200 : ℝ)) := by
    have h := hpThetaJensenCell452_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1099455577843 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell452_endpointUpper :
    hpThetaJensenKernelEndpointUpper (113 / 400 : ℝ) (453 / 1600 : ℝ) ≤ (8203700819 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (453 / 800 : ℝ)) (55343824945870461 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (453 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell452_product_upper
  have hD : (2183074910191 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (113 / 200 : ℝ) - (453 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell452_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell452_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (113 / 200 : ℝ) - (453 / 3200 : ℝ)) ≤
      (1 / (2183074910191 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2183074910191 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((453 / 3200 : ℝ) - Real.pi * Real.exp (113 / 200 : ℝ)) ≤
      (2 / (2183074910191 / 10000000000 : ℝ) : ℝ) := by
    rw [show (453 / 3200 : ℝ) - Real.pi * Real.exp (113 / 200 : ℝ) =
      -(Real.pi * Real.exp (113 / 200 : ℝ) - (453 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55343824945870461 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (55343824945870461 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell452_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (113 / 400 : ℝ) (453 / 1600 : ℝ)) :
    (8099169127 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8203700819 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell452_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell452_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell453_leftExp :
    (704659387 / 400000000 : ℝ) ≤ Real.exp (453 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (453 / 800 : ℝ) (1017852802113 / 1000000000000 : ℝ)
    (704659387 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell453_rightExp :
    Real.exp (227 / 400 : ℝ) ≤ (17638519051 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (227 / 400 : ℝ) (508946281383 / 500000000000 : ℝ)
    (17638519051 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell453_denomUpper :
    Real.exp (53997422980988243 / 10000000000000000 : ℝ) ≤ (1106746833531 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53997422980988243 / 10000000000000000 : ℝ) (9470516899 /
    8000000000 : ℝ) (1106746833531 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell453_denomLower :
    (549383348223 / 2500000000 : ℝ) ≤ Real.exp (269625286615513 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (269625286615513 / 50000000000000 : ℝ) (73971683227 /
    62500000000 : ℝ) (549383348223 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell453_product_lower :
    (276719036615513 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (453 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell453_leftExp
    (by norm_num : (0 : ℝ) ≤ (704659387 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell453_product_upper :
    Real.pi * Real.exp (227 / 400 : ℝ) ≤ (55413047980988243 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell453_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell453_endpointLower :
    (8069704223 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (453 / 1600 : ℝ) (227 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (276719036615513 / 50000000000000 : ℝ) (Real.pi * Real.exp (453 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell453_product_lower
  have hD : Real.exp (Real.pi * Real.exp (227 / 400 : ℝ) - (453 / 3200 : ℝ)) ≤
      (1106746833531 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell453_denomUpper
    linarith [hpThetaJensenCell453_product_upper]
  have hi : (1 / (1106746833531 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (227 / 400 : ℝ) - (453 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1106746833531 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1106746833531 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((453 / 3200 : ℝ) - Real.pi * Real.exp (227 / 400 : ℝ)) := by
    rw [show (453 / 3200 : ℝ) - Real.pi * Real.exp (227 / 400 : ℝ) =
      -(Real.pi * Real.exp (227 / 400 : ℝ) - (453 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (453 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (453 / 800 : ℝ)) := by
    have h := hpThetaJensenCell453_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1106746833531 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell453_endpointUpper :
    hpThetaJensenKernelEndpointUpper (453 / 1600 : ℝ) (227 / 800 : ℝ) ≤ (817391981 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (227 / 400 : ℝ)) (55413047980988243 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (227 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell453_product_upper
  have hD : (549383348223 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (453 / 800 : ℝ) - (227 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell453_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell453_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (453 / 800 : ℝ) - (227 / 1600 : ℝ)) ≤
      (1 / (549383348223 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (549383348223 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((227 / 1600 : ℝ) - Real.pi * Real.exp (453 / 800 : ℝ)) ≤
      (2 / (549383348223 / 2500000000 : ℝ) : ℝ) := by
    rw [show (227 / 1600 : ℝ) - Real.pi * Real.exp (453 / 800 : ℝ) =
      -(Real.pi * Real.exp (453 / 800 : ℝ) - (227 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55413047980988243 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (55413047980988243 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell453_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (453 / 1600 : ℝ) (227 / 800 : ℝ)) :
    (8069704223 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (817391981 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell453_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell453_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell454_leftExp :
    (352770381 / 200000000 : ℝ) ≤ Real.exp (227 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (227 / 400 : ℝ) (203578512553 / 200000000000 : ℝ)
    (352770381 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell454_rightExp :
    Real.exp (91 / 160 : ℝ) ≤ (8830290493 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91 / 160 : ℝ) (101793232497 / 100000000000 : ℝ)
    (8830290493 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell454_denomUpper :
    Real.exp (27031803800775349 / 5000000000000000 : ℝ) ≤ (557048044507 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27031803800775349 / 5000000000000000 : ℝ) (23681189649 /
    20000000000 : ℝ) (557048044507 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell454_denomLower :
    (442421352633 / 2000000000 : ℝ) ≤ Real.exp (134977888348319 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (134977888348319 / 25000000000000 : ℝ) (591895712979 /
    500000000000 : ℝ) (442421352633 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell454_product_lower :
    (138532575848319 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (227 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell454_leftExp
    (by norm_num : (0 : ℝ) ≤ (352770381 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell454_product_upper :
    Real.pi * Real.exp (91 / 160 : ℝ) ≤ (27741178800775349 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell454_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell454_endpointLower :
    (8040270487 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (227 / 800 : ℝ) (91 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (138532575848319 / 25000000000000 : ℝ) (Real.pi * Real.exp (227 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell454_product_lower
  have hD : Real.exp (Real.pi * Real.exp (91 / 160 : ℝ) - (227 / 1600 : ℝ)) ≤
      (557048044507 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell454_denomUpper
    linarith [hpThetaJensenCell454_product_upper]
  have hi : (1 / (557048044507 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (91 / 160 : ℝ) - (227 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (557048044507 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (557048044507 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((227 / 1600 : ℝ) - Real.pi * Real.exp (91 / 160 : ℝ)) := by
    rw [show (227 / 1600 : ℝ) - Real.pi * Real.exp (91 / 160 : ℝ) =
      -(Real.pi * Real.exp (91 / 160 : ℝ) - (227 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (227 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (227 / 400 : ℝ)) := by
    have h := hpThetaJensenCell454_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (557048044507 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell454_endpointUpper :
    hpThetaJensenKernelEndpointUpper (227 / 800 : ℝ) (91 / 320 : ℝ) ≤ (1018021251 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (91 / 160 : ℝ)) (27741178800775349 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (91 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell454_product_upper
  have hD : (442421352633 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (227 / 400 : ℝ) - (91 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell454_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell454_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (227 / 400 : ℝ) - (91 / 640 : ℝ)) ≤
      (1 / (442421352633 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (442421352633 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((91 / 640 : ℝ) - Real.pi * Real.exp (227 / 400 : ℝ)) ≤
      (2 / (442421352633 / 2000000000 : ℝ) : ℝ) := by
    rw [show (91 / 640 : ℝ) - Real.pi * Real.exp (227 / 400 : ℝ) =
      -(Real.pi * Real.exp (227 / 400 : ℝ) - (91 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27741178800775349 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (27741178800775349 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell454_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (227 / 800 : ℝ) (91 / 320 : ℝ)) :
    (8040270487 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1018021251 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell454_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell454_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell455_leftExp :
    (2207572623 / 1250000000 : ℝ) ≤ Real.exp (91 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (91 / 160 : ℝ) (1017932324969 / 1000000000000 : ℝ)
    (2207572623 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell455_rightExp :
    Real.exp (57 / 100 : ℝ) ≤ (3536534103 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 100 : ℝ) (127246511091 / 125000000000 : ℝ)
    (3536534103 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell455_denomUpper :
    Real.exp (10825975782246079 / 2000000000000000 : ℝ) ≤ (2243007737509 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10825975782246079 / 2000000000000000 : ℝ) (148038090501
    / 125000000000 : ℝ) (2243007737509 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell455_denomLower :
    (445359211773 / 2000000000 : ℝ) ≤ Real.exp (844645936479477 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (844645936479477 / 156250000000000 : ℝ) (1184036291143 /
    1000000000000 : ℝ) (445359211773 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell455_product_lower :
    (866911561479477 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (91 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell455_leftExp
    (by norm_num : (0 : ℝ) ≤ (2207572623 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell455_product_upper :
    Real.pi * Real.exp (57 / 100 : ℝ) ≤ (11110350782246079 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell455_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell455_endpointLower :
    (2002717073 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 320 : ℝ) (57 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (866911561479477 / 156250000000000 : ℝ) (Real.pi * Real.exp (91 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell455_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 100 : ℝ) - (91 / 640 : ℝ)) ≤
      (2243007737509 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell455_denomUpper
    linarith [hpThetaJensenCell455_product_upper]
  have hi : (1 / (2243007737509 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 100 : ℝ) - (91 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2243007737509 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2243007737509 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((91 / 640 : ℝ) - Real.pi * Real.exp (57 / 100 : ℝ)) := by
    rw [show (91 / 640 : ℝ) - Real.pi * Real.exp (57 / 100 : ℝ) =
      -(Real.pi * Real.exp (57 / 100 : ℝ) - (91 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (91 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (91 / 160 : ℝ)) := by
    have h := hpThetaJensenCell455_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2243007737509 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell455_endpointUpper :
    hpThetaJensenKernelEndpointUpper (91 / 320 : ℝ) (57 / 200 : ℝ) ≤ (811445179 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 100 : ℝ)) (11110350782246079 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell455_product_upper
  have hD : (445359211773 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (91 / 160 : ℝ) - (57 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell455_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell455_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (91 / 160 : ℝ) - (57 / 400 : ℝ)) ≤
      (1 / (445359211773 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (445359211773 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 400 : ℝ) - Real.pi * Real.exp (91 / 160 : ℝ)) ≤
      (2 / (445359211773 / 2000000000 : ℝ) : ℝ) := by
    rw [show (57 / 400 : ℝ) - Real.pi * Real.exp (91 / 160 : ℝ) =
      -(Real.pi * Real.exp (91 / 160 : ℝ) - (57 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11110350782246079 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (11110350782246079 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell455_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (91 / 320 : ℝ) (57 / 200 : ℝ)) :
    (2002717073 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (811445179 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell455_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell455_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell456_leftExp :
    (17682670513 / 10000000000 : ℝ) ≤ Real.exp (57 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 100 : ℝ) (1017972088727 / 1000000000000 : ℝ)
    (17682670513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell456_rightExp :
    Real.exp (457 / 800 : ℝ) ≤ (8852393837 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (457 / 800 : ℝ) (25450296351 / 25000000000 : ℝ)
    (8852393837 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell456_denomUpper :
    Real.exp (27098118511562341 / 5000000000000000 : ℝ) ≤ (2257941407009 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27098118511562341 / 5000000000000000 : ℝ) (1184550337677
    / 1000000000000 : ℝ) (2257941407009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell456_denomLower :
    (2241602330411 / 10000000000 : ℝ) ≤ Real.exp (6765451402784587 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6765451402784587 / 1250000000000000 : ℝ) (148035190977 /
    125000000000 : ℝ) (2241602330411 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell456_product_lower :
    (6943967027784587 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell456_leftExp
    (by norm_num : (0 : ℝ) ≤ (17682670513 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell456_product_upper :
    Real.pi * Real.exp (457 / 800 : ℝ) ≤ (27810618511562341 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell456_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell456_endpointLower :
    (7981498003 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 200 : ℝ) (457 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6943967027784587 / 1250000000000000 : ℝ) (Real.pi * Real.exp (57 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell456_product_lower
  have hD : Real.exp (Real.pi * Real.exp (457 / 800 : ℝ) - (57 / 400 : ℝ)) ≤
      (2257941407009 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell456_denomUpper
    linarith [hpThetaJensenCell456_product_upper]
  have hi : (1 / (2257941407009 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (457 / 800 : ℝ) - (57 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2257941407009 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2257941407009 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 400 : ℝ) - Real.pi * Real.exp (457 / 800 : ℝ)) := by
    rw [show (57 / 400 : ℝ) - Real.pi * Real.exp (457 / 800 : ℝ) =
      -(Real.pi * Real.exp (457 / 800 : ℝ) - (57 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 100 : ℝ)) := by
    have h := hpThetaJensenCell456_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2257941407009 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell456_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 200 : ℝ) (457 / 1600 : ℝ) ≤ (323390621 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (457 / 800 : ℝ)) (27810618511562341 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (457 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell456_product_upper
  have hD : (2241602330411 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 100 : ℝ) - (457 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell456_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell456_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 100 : ℝ) - (457 / 3200 : ℝ)) ≤
      (1 / (2241602330411 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2241602330411 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((457 / 3200 : ℝ) - Real.pi * Real.exp (57 / 100 : ℝ)) ≤
      (2 / (2241602330411 / 10000000000 : ℝ) : ℝ) := by
    rw [show (457 / 3200 : ℝ) - Real.pi * Real.exp (57 / 100 : ℝ) =
      -(Real.pi * Real.exp (57 / 100 : ℝ) - (457 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27810618511562341 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (27810618511562341 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell456_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 200 : ℝ) (457 / 1600 : ℝ)) :
    (7981498003 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (323390621 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell456_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell456_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell457_leftExp :
    (2213098459 / 1250000000 : ℝ) ≤ Real.exp (457 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (457 / 800 : ℝ) (1018011854039 / 1000000000000 : ℝ)
    (2213098459 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell457_rightExp :
    Real.exp (229 / 400 : ℝ) ≤ (1107933281 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (229 / 400 : ℝ) (203610324181 / 200000000000 : ℝ)
    (1107933281 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell457_denomUpper :
    Real.exp (3391417627556633 / 625000000000000 : ℝ) ≤ (1136497128339 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3391417627556633 / 625000000000000 : ℝ) (1184796324053 /
    1000000000000 : ℝ) (1136497128339 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell457_denomLower :
    (1128263318993 / 5000000000 : ℝ) ≤ Real.exp (846718270500841 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (846718270500841 / 156250000000000 : ℝ) (592263568297 /
    500000000000 : ℝ) (1128263318993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell457_product_lower :
    (869081551750841 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (457 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell457_leftExp
    (by norm_num : (0 : ℝ) ≤ (2213098459 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell457_product_upper :
    Real.pi * Real.exp (229 / 400 : ℝ) ≤ (3480675440056633 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell457_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell457_endpointLower :
    (7952159989 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (457 / 1600 : ℝ) (229 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (869081551750841 / 156250000000000 : ℝ) (Real.pi * Real.exp (457 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell457_product_lower
  have hD : Real.exp (Real.pi * Real.exp (229 / 400 : ℝ) - (457 / 3200 : ℝ)) ≤
      (1136497128339 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell457_denomUpper
    linarith [hpThetaJensenCell457_product_upper]
  have hi : (1 / (1136497128339 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (229 / 400 : ℝ) - (457 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1136497128339 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1136497128339 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((457 / 3200 : ℝ) - Real.pi * Real.exp (229 / 400 : ℝ)) := by
    rw [show (457 / 3200 : ℝ) - Real.pi * Real.exp (229 / 400 : ℝ) =
      -(Real.pi * Real.exp (229 / 400 : ℝ) - (457 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (457 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (457 / 800 : ℝ)) := by
    have h := hpThetaJensenCell457_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1136497128339 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell457_endpointUpper :
    hpThetaJensenKernelEndpointUpper (457 / 1600 : ℝ) (229 / 800 : ℝ) ≤ (402755579 / 500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (229 / 400 : ℝ)) (3480675440056633 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (229 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell457_product_upper
  have hD : (1128263318993 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (457 / 800 : ℝ) - (229 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell457_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell457_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (457 / 800 : ℝ) - (229 / 1600 : ℝ)) ≤
      (1 / (1128263318993 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1128263318993 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((229 / 1600 : ℝ) - Real.pi * Real.exp (457 / 800 : ℝ)) ≤
      (2 / (1128263318993 / 5000000000 : ℝ) : ℝ) := by
    rw [show (229 / 1600 : ℝ) - Real.pi * Real.exp (457 / 800 : ℝ) =
      -(Real.pi * Real.exp (457 / 800 : ℝ) - (229 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3480675440056633 / 625000000000000 : ℝ) ^ 2 - 6 *
      (3480675440056633 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell457_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (457 / 1600 : ℝ) (229 / 800 : ℝ)) :
    (7952159989 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (402755579 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell457_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell457_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell458_leftExp :
    (8863466247 / 5000000000 : ℝ) ≤ Real.exp (229 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (229 / 400 : ℝ) (127256452613 / 125000000000 : ℝ)
    (8863466247 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell458_rightExp :
    Real.exp (459 / 800 : ℝ) ≤ (17749105017 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (459 / 800 : ℝ) (1018091389323 / 1000000000000 : ℝ)
    (17749105017 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell458_denomUpper :
    Real.exp (54329214077672081 / 10000000000000000 : ℝ) ≤ (1144083684691 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (54329214077672081 / 10000000000000000 : ℝ) (237008536753
    / 200000000000 : ℝ) (1144083684691 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell458_denomLower :
    (2271570050827 / 10000000000 : ℝ) ≤ Real.exp (3391025894230653 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3391025894230653 / 625000000000000 : ℝ) (1184773118069 /
    1000000000000 : ℝ) (2271570050827 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell458_product_lower :
    (3480674331730653 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (229 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell458_leftExp
    (by norm_num : (0 : ℝ) ≤ (8863466247 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell458_product_upper :
    Real.pi * Real.exp (459 / 800 : ℝ) ≤ (55760464077672081 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell458_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell458_endpointLower :
    (792285461 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (229 / 800 : ℝ) (459 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3480674331730653 / 625000000000000 : ℝ) (Real.pi * Real.exp (229 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell458_product_lower
  have hD : Real.exp (Real.pi * Real.exp (459 / 800 : ℝ) - (229 / 1600 : ℝ)) ≤
      (1144083684691 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell458_denomUpper
    linarith [hpThetaJensenCell458_product_upper]
  have hi : (1 / (1144083684691 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (459 / 800 : ℝ) - (229 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1144083684691 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1144083684691 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((229 / 1600 : ℝ) - Real.pi * Real.exp (459 / 800 : ℝ)) := by
    rw [show (229 / 1600 : ℝ) - Real.pi * Real.exp (459 / 800 : ℝ) =
      -(Real.pi * Real.exp (459 / 800 : ℝ) - (229 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (229 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (229 / 400 : ℝ)) := by
    have h := hpThetaJensenCell458_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1144083684691 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell458_endpointUpper :
    hpThetaJensenKernelEndpointUpper (229 / 800 : ℝ) (459 / 1600 : ℝ) ≤ (8025490331 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (459 / 800 : ℝ)) (55760464077672081 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (459 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell458_product_upper
  have hD : (2271570050827 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (229 / 400 : ℝ) - (459 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell458_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell458_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (229 / 400 : ℝ) - (459 / 3200 : ℝ)) ≤
      (1 / (2271570050827 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2271570050827 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((459 / 3200 : ℝ) - Real.pi * Real.exp (229 / 400 : ℝ)) ≤
      (2 / (2271570050827 / 10000000000 : ℝ) : ℝ) := by
    rw [show (459 / 3200 : ℝ) - Real.pi * Real.exp (229 / 400 : ℝ) =
      -(Real.pi * Real.exp (229 / 400 : ℝ) - (459 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55760464077672081 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (55760464077672081 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell458_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (229 / 800 : ℝ) (459 / 1600 : ℝ)) :
    (792285461 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8025490331 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell458_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell458_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell459_leftExp :
    (3549821003 / 2000000000 : ℝ) ≤ Real.exp (459 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (459 / 800 : ℝ) (509045694661 / 500000000000 : ℝ)
    (3549821003 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell459_rightExp :
    Real.exp (23 / 40 : ℝ) ≤ (1777130527 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 40 : ℝ) (509065579647 / 500000000000 : ℝ)
    (1777130527 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell459_denomUpper :
    Real.exp (5439583323709511 / 1000000000000000 : ℝ) ≤ (2303461836717 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5439583323709511 / 1000000000000000 : ℝ) (18520147147 /
    15625000000 : ℝ) (2303461836717 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell459_denomLower :
    (2286733651303 / 10000000000 : ℝ) ≤ Real.exp (1358073658057097 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1358073658057097 / 250000000000000 : ℝ) (1185019472873 /
    1000000000000 : ℝ) (2286733651303 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell459_product_lower :
    (1394011158057097 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (459 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell459_leftExp
    (by norm_num : (0 : ℝ) ≤ (3549821003 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell459_product_upper :
    Real.pi * Real.exp (23 / 40 : ℝ) ≤ (5583020823709511 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell459_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell459_endpointLower :
    (1578716447 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (459 / 1600 : ℝ) (23 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1394011158057097 / 250000000000000 : ℝ) (Real.pi * Real.exp (459 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell459_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 40 : ℝ) - (459 / 3200 : ℝ)) ≤
      (2303461836717 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell459_denomUpper
    linarith [hpThetaJensenCell459_product_upper]
  have hi : (1 / (2303461836717 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 40 : ℝ) - (459 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2303461836717 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2303461836717 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((459 / 3200 : ℝ) - Real.pi * Real.exp (23 / 40 : ℝ)) := by
    rw [show (459 / 3200 : ℝ) - Real.pi * Real.exp (23 / 40 : ℝ) =
      -(Real.pi * Real.exp (23 / 40 : ℝ) - (459 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (459 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (459 / 800 : ℝ)) := by
    have h := hpThetaJensenCell459_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2303461836717 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell459_endpointUpper :
    hpThetaJensenKernelEndpointUpper (459 / 1600 : ℝ) (23 / 80 : ℝ) ≤ (7995902137 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 40 : ℝ)) (5583020823709511 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell459_product_upper
  have hD : (2286733651303 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (459 / 800 : ℝ) - (23 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell459_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell459_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (459 / 800 : ℝ) - (23 / 160 : ℝ)) ≤
      (1 / (2286733651303 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2286733651303 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 160 : ℝ) - Real.pi * Real.exp (459 / 800 : ℝ)) ≤
      (2 / (2286733651303 / 10000000000 : ℝ) : ℝ) := by
    rw [show (23 / 160 : ℝ) - Real.pi * Real.exp (459 / 800 : ℝ) =
      -(Real.pi * Real.exp (459 / 800 : ℝ) - (23 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5583020823709511 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5583020823709511 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell459_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (459 / 1600 : ℝ) (23 / 80 : ℝ)) :
    (1578716447 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7995902137 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell459_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell459_endpointUpper

def hpThetaJensenCellsBatch022Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (422752143 / 500000000 : ℝ)
  | 1 => (8425233257 / 10000000000 : ℝ)
  | 2 => (335818011 / 400000000 : ℝ)
  | 3 => (8365694303 / 10000000000 : ℝ)
  | 4 => (2083991431 / 2500000000 : ℝ)
  | 5 => (2076566231 / 2500000000 : ℝ)
  | 6 => (4138296143 / 5000000000 : ℝ)
  | 7 => (8246948193 / 10000000000 : ℝ)
  | 8 => (256791657 / 312500000 : ℝ)
  | 9 => (4093873579 / 5000000000 : ℝ)
  | 10 => (1019773871 / 1250000000 : ℝ)
  | 11 => (4064332417 / 5000000000 : ℝ)
  | 12 => (8099169127 / 10000000000 : ℝ)
  | 13 => (8069704223 / 10000000000 : ℝ)
  | 14 => (8040270487 / 10000000000 : ℝ)
  | 15 => (2002717073 / 2500000000 : ℝ)
  | 16 => (7981498003 / 10000000000 : ℝ)
  | 17 => (7952159989 / 10000000000 : ℝ)
  | 18 => (792285461 / 1000000000 : ℝ)
  | 19 => (1578716447 / 2000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch022Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1712673803 / 2000000000 : ℝ)
  | 1 => (8533243219 / 10000000000 : ℝ)
  | 2 => (8503144027 / 10000000000 : ℝ)
  | 3 => (8473071827 / 10000000000 : ℝ)
  | 4 => (8443027017 / 10000000000 : ℝ)
  | 5 => (8413009983 / 10000000000 : ℝ)
  | 6 => (4191510557 / 5000000000 : ℝ)
  | 7 => (8353060791 / 10000000000 : ℝ)
  | 8 => (4161564701 / 5000000000 : ℝ)
  | 9 => (8293227329 / 10000000000 : ℝ)
  | 10 => (1652670991 / 2000000000 : ℝ)
  | 11 => (8233512659 / 10000000000 : ℝ)
  | 12 => (8203700819 / 10000000000 : ℝ)
  | 13 => (817391981 / 1000000000 : ℝ)
  | 14 => (1018021251 / 1250000000 : ℝ)
  | 15 => (811445179 / 1000000000 : ℝ)
  | 16 => (323390621 / 400000000 : ℝ)
  | 17 => (402755579 / 500000000 : ℝ)
  | 18 => (8025490331 / 10000000000 : ℝ)
  | 19 => (7995902137 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch022_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch022Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch022Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell440_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell441_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell442_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell443_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell444_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell445_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell446_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell447_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell448_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell449_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell450_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell451_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell452_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell453_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell454_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell455_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell456_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell457_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell458_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell459_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper] at h ⊢
    exact h

end HodgeProofHP
