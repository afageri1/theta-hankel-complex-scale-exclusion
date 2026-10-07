import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell120_leftExp :
    (11618342427 / 10000000000 : ℝ) ≤ Real.exp (3 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 20 : ℝ) (502349251757 / 500000000000 : ℝ)
    (11618342427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell120_rightExp :
    Real.exp (121 / 800 : ℝ) ≤ (11632874437 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (121 / 800 : ℝ) (1004737750317 / 1000000000000 : ℝ)
    (11632874437 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell120_denomUpper :
    Real.exp (36170756901158141 / 10000000000000000 : ℝ) ≤ (186142703481 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36170756901158141 / 10000000000000000 : ℝ)
    (1119669570363 / 1000000000000 : ℝ) (186142703481 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell120_denomLower :
    (11577294999 / 312500000 : ℝ) ≤ Real.exp (4515245827740473 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4515245827740473 / 1250000000000000 : ℝ) (1119498867779
    / 1000000000000 : ℝ) (11577294999 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell120_product_lower :
    (4562511452740473 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell120_leftExp
    (by norm_num : (0 : ℝ) ≤ (11618342427 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell120_product_upper :
    Real.pi * Real.exp (121 / 800 : ℝ) ≤ (36545756901158141 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell120_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell120_endpointLower :
    (8431760143 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 40 : ℝ) (121 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4562511452740473 / 1250000000000000 : ℝ) (Real.pi * Real.exp (3 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell120_product_lower
  have hD : Real.exp (Real.pi * Real.exp (121 / 800 : ℝ) - (3 / 80 : ℝ)) ≤
      (186142703481 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell120_denomUpper
    linarith [hpThetaJensenCell120_product_upper]
  have hi : (1 / (186142703481 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (121 / 800 : ℝ) - (3 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (186142703481 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (186142703481 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 80 : ℝ) - Real.pi * Real.exp (121 / 800 : ℝ)) := by
    rw [show (3 / 80 : ℝ) - Real.pi * Real.exp (121 / 800 : ℝ) =
      -(Real.pi * Real.exp (121 / 800 : ℝ) - (3 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 20 : ℝ)) := by
    have h := hpThetaJensenCell120_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (186142703481 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell120_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 40 : ℝ) (121 / 1600 : ℝ) ≤ (17048016179 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (121 / 800 : ℝ)) (36545756901158141 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (121 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell120_product_upper
  have hD : (11577294999 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 20 : ℝ) - (121 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell120_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell120_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 20 : ℝ) - (121 / 3200 : ℝ)) ≤
      (1 / (11577294999 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11577294999 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((121 / 3200 : ℝ) - Real.pi * Real.exp (3 / 20 : ℝ)) ≤
      (2 / (11577294999 / 312500000 : ℝ) : ℝ) := by
    rw [show (121 / 3200 : ℝ) - Real.pi * Real.exp (3 / 20 : ℝ) =
      -(Real.pi * Real.exp (3 / 20 : ℝ) - (121 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36545756901158141 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36545756901158141 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell120_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 40 : ℝ) (121 / 1600 : ℝ)) :
    (8431760143 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17048016179 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell120_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell120_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell121_leftExp :
    (2326574887 / 2000000000 : ℝ) ≤ Real.exp (121 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (121 / 800 : ℝ) (251184437579 / 250000000000 : ℝ)
    (2326574887 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell121_rightExp :
    Real.exp (61 / 400 : ℝ) ≤ (5823712311 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 400 : ℝ) (251194249663 / 250000000000 : ℝ)
    (5823712311 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell121_denomUpper :
    Real.exp (18106671330251423 / 5000000000000000 : ℝ) ≤ (5841784269 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18106671330251423 / 5000000000000000 : ℝ) (559909293231
    / 500000000000 : ℝ) (5841784269 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell121_denomLower :
    (37205236823 / 1000000000 : ℝ) ≤ Real.exp (904112381550013 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (904112381550013 / 250000000000000 : ℝ) (223929532261 /
    200000000000 : ℝ) (37205236823 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell121_product_lower :
    (913643631550013 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (121 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell121_leftExp
    (by norm_num : (0 : ℝ) ≤ (2326574887 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell121_product_upper :
    Real.pi * Real.exp (61 / 400 : ℝ) ≤ (18295733830251423 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell121_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell121_endpointLower :
    (131629391 / 78125000 : ℝ) ≤ hpThetaTraceEndpointLower (121 / 1600 : ℝ) (61 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (913643631550013 / 250000000000000 : ℝ) (Real.pi * Real.exp (121 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell121_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 400 : ℝ) - (121 / 3200 : ℝ)) ≤
      (5841784269 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell121_denomUpper
    linarith [hpThetaJensenCell121_product_upper]
  have hi : (1 / (5841784269 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 400 : ℝ) - (121 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5841784269 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5841784269 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((121 / 3200 : ℝ) - Real.pi * Real.exp (61 / 400 : ℝ)) := by
    rw [show (121 / 3200 : ℝ) - Real.pi * Real.exp (61 / 400 : ℝ) =
      -(Real.pi * Real.exp (61 / 400 : ℝ) - (121 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (121 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (121 / 800 : ℝ)) := by
    have h := hpThetaJensenCell121_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5841784269 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell121_endpointUpper :
    hpThetaJensenKernelEndpointUpper (121 / 1600 : ℝ) (61 / 800 : ℝ) ≤ (17032960147 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 400 : ℝ)) (18295733830251423 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell121_product_upper
  have hD : (37205236823 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (121 / 800 : ℝ) - (61 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell121_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell121_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (121 / 800 : ℝ) - (61 / 1600 : ℝ)) ≤
      (1 / (37205236823 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (37205236823 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 1600 : ℝ) - Real.pi * Real.exp (121 / 800 : ℝ)) ≤
      (2 / (37205236823 / 1000000000 : ℝ) : ℝ) := by
    rw [show (61 / 1600 : ℝ) - Real.pi * Real.exp (121 / 800 : ℝ) =
      -(Real.pi * Real.exp (121 / 800 : ℝ) - (61 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18295733830251423 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18295733830251423 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell121_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (121 / 1600 : ℝ) (61 / 800 : ℝ)) :
    (131629391 / 78125000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17032960147 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell121_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell121_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell122_leftExp :
    (582371231 / 500000000 : ℝ) ≤ Real.exp (61 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 400 : ℝ) (1004776998651 / 1000000000000 : ℝ)
    (582371231 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell122_rightExp :
    Real.exp (123 / 800 : ℝ) ≤ (5830996503 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (123 / 800 : ℝ) (25120406213 / 25000000000 : ℝ)
    (5830996503 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell122_denomUpper :
    Real.exp (18127992796849279 / 5000000000000000 : ℝ) ≤ (46933988323 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18127992796849279 / 5000000000000000 : ℝ) (1119967822497
    / 1000000000000 : ℝ) (46933988323 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell122_denomLower :
    (373640159419 / 10000000000 : ℝ) ≤ Real.exp (226294256292469 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (226294256292469 / 62500000000000 : ℝ) (559898337219 /
    500000000000 : ℝ) (373640159419 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell122_product_lower :
    (228696600042469 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell122_leftExp
    (by norm_num : (0 : ℝ) ≤ (582371231 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell122_product_upper :
    Real.pi * Real.exp (123 / 800 : ℝ) ≤ (18318617796849279 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell122_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell122_endpointLower :
    (1052093111 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 800 : ℝ) (123 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (228696600042469 / 62500000000000 : ℝ) (Real.pi * Real.exp (61 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell122_product_lower
  have hD : Real.exp (Real.pi * Real.exp (123 / 800 : ℝ) - (61 / 1600 : ℝ)) ≤
      (46933988323 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell122_denomUpper
    linarith [hpThetaJensenCell122_product_upper]
  have hi : (1 / (46933988323 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (123 / 800 : ℝ) - (61 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (46933988323 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (46933988323 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 1600 : ℝ) - Real.pi * Real.exp (123 / 800 : ℝ)) := by
    rw [show (61 / 1600 : ℝ) - Real.pi * Real.exp (123 / 800 : ℝ) =
      -(Real.pi * Real.exp (123 / 800 : ℝ) - (61 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 400 : ℝ)) := by
    have h := hpThetaJensenCell122_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (46933988323 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell122_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 800 : ℝ) (123 / 1600 : ℝ) ≤ (680711557 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (123 / 800 : ℝ)) (18318617796849279 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (123 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell122_product_upper
  have hD : (373640159419 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 400 : ℝ) - (123 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell122_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell122_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 400 : ℝ) - (123 / 3200 : ℝ)) ≤
      (1 / (373640159419 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (373640159419 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((123 / 3200 : ℝ) - Real.pi * Real.exp (61 / 400 : ℝ)) ≤
      (2 / (373640159419 / 10000000000 : ℝ) : ℝ) := by
    rw [show (123 / 3200 : ℝ) - Real.pi * Real.exp (61 / 400 : ℝ) =
      -(Real.pi * Real.exp (61 / 400 : ℝ) - (123 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18318617796849279 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18318617796849279 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell122_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 800 : ℝ) (123 / 1600 : ℝ)) :
    (1052093111 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (680711557 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell122_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell122_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell123_leftExp :
    (2915498251 / 2500000000 : ℝ) ≤ Real.exp (123 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (123 / 800 : ℝ) (1004816248519 / 1000000000000 : ℝ)
    (2915498251 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell123_rightExp :
    Real.exp (31 / 200 : ℝ) ≤ (2919144903 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 200 : ℝ) (1004855499921 / 1000000000000 : ℝ)
    (2919144903 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell123_denomUpper :
    Real.exp (9074671443250479 / 2500000000000000 : ℝ) ≤ (47134825779 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9074671443250479 / 2500000000000000 : ℝ) (560058639401 /
    500000000000 : ℝ) (47134825779 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell123_denomLower :
    (23452304507 / 625000000 : ℝ) ≤ Real.exp (1132803872669449 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1132803872669449 / 312500000000000 : ℝ) (1119945907501 /
    1000000000000 : ℝ) (23452304507 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell123_product_lower :
    (1144913247669449 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (123 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell123_leftExp
    (by norm_num : (0 : ℝ) ≤ (2915498251 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell123_product_upper :
    Real.pi * Real.exp (31 / 200 : ℝ) ≤ (9170765193250479 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell123_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell123_endpointLower :
    (16818303769 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (123 / 1600 : ℝ) (31 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1144913247669449 / 312500000000000 : ℝ) (Real.pi * Real.exp (123 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell123_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 200 : ℝ) - (123 / 3200 : ℝ)) ≤
      (47134825779 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell123_denomUpper
    linarith [hpThetaJensenCell123_product_upper]
  have hi : (1 / (47134825779 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 200 : ℝ) - (123 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (47134825779 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (47134825779 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((123 / 3200 : ℝ) - Real.pi * Real.exp (31 / 200 : ℝ)) := by
    rw [show (123 / 3200 : ℝ) - Real.pi * Real.exp (31 / 200 : ℝ) =
      -(Real.pi * Real.exp (31 / 200 : ℝ) - (123 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (123 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (123 / 800 : ℝ)) := by
    have h := hpThetaJensenCell123_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (47134825779 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell123_endpointUpper :
    hpThetaJensenKernelEndpointUpper (123 / 1600 : ℝ) (31 / 400 : ℝ) ≤ (17002502821 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 200 : ℝ)) (9170765193250479 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell123_product_upper
  have hD : (23452304507 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (123 / 800 : ℝ) - (31 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell123_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell123_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (123 / 800 : ℝ) - (31 / 800 : ℝ)) ≤
      (1 / (23452304507 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23452304507 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 800 : ℝ) - Real.pi * Real.exp (123 / 800 : ℝ)) ≤
      (2 / (23452304507 / 625000000 : ℝ) : ℝ) := by
    rw [show (31 / 800 : ℝ) - Real.pi * Real.exp (123 / 800 : ℝ) =
      -(Real.pi * Real.exp (123 / 800 : ℝ) - (31 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9170765193250479 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9170765193250479 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell123_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (123 / 1600 : ℝ) (31 / 400 : ℝ)) :
    (16818303769 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17002502821 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell123_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell123_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell124_leftExp :
    (1167657961 / 1000000000 : ℝ) ≤ Real.exp (31 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 200 : ℝ) (12560693749 / 12500000000 : ℝ)
    (1167657961 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell124_rightExp :
    Real.exp (5 / 32 : ℝ) ≤ (5845592231 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5 / 32 : ℝ) (125611844107 / 125000000000 : ℝ)
    (5845592231 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell124_denomUpper :
    Real.exp (18170721633763983 / 5000000000000000 : ℝ) ≤ (189347175839 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18170721633763983 / 5000000000000000 : ℝ) (1120266955703
    / 1000000000000 : ℝ) (189347175839 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell124_denomLower :
    (376842565469 / 10000000000 : ℝ) ≤ Real.exp (453655301126739 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (453655301126739 / 125000000000000 : ℝ) (1120095360831 /
    1000000000000 : ℝ) (376842565469 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell124_product_lower :
    (458538113626739 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell124_leftExp
    (by norm_num : (0 : ℝ) ≤ (1167657961 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell124_product_upper :
    Real.pi * Real.exp (5 / 32 : ℝ) ≤ (18364471633763983 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell124_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell124_endpointLower :
    (1050187771 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 400 : ℝ) (5 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (458538113626739 / 125000000000000 : ℝ) (Real.pi * Real.exp (31 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell124_product_lower
  have hD : Real.exp (Real.pi * Real.exp (5 / 32 : ℝ) - (31 / 800 : ℝ)) ≤
      (189347175839 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell124_denomUpper
    linarith [hpThetaJensenCell124_product_upper]
  have hi : (1 / (189347175839 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (5 / 32 : ℝ) - (31 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (189347175839 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (189347175839 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 800 : ℝ) - Real.pi * Real.exp (5 / 32 : ℝ)) := by
    rw [show (31 / 800 : ℝ) - Real.pi * Real.exp (5 / 32 : ℝ) =
      -(Real.pi * Real.exp (5 / 32 : ℝ) - (31 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 200 : ℝ)) := by
    have h := hpThetaJensenCell124_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (189347175839 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell124_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 400 : ℝ) (5 / 64 : ℝ) ≤ (16987102137 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (5 / 32 : ℝ)) (18364471633763983 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (5 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell124_product_upper
  have hD : (376842565469 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 200 : ℝ) - (5 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell124_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell124_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 200 : ℝ) - (5 / 128 : ℝ)) ≤
      (1 / (376842565469 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (376842565469 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((5 / 128 : ℝ) - Real.pi * Real.exp (31 / 200 : ℝ)) ≤
      (2 / (376842565469 / 10000000000 : ℝ) : ℝ) := by
    rw [show (5 / 128 : ℝ) - Real.pi * Real.exp (31 / 200 : ℝ) =
      -(Real.pi * Real.exp (31 / 200 : ℝ) - (5 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18364471633763983 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18364471633763983 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell124_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 400 : ℝ) (5 / 64 : ℝ)) :
    (1050187771 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16987102137 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell124_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell124_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell125_leftExp :
    (11691184461 / 10000000000 : ℝ) ≤ Real.exp (5 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5 / 32 : ℝ) (200978950571 / 200000000000 : ℝ)
    (11691184461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell125_rightExp :
    Real.exp (63 / 400 : ℝ) ≤ (11705807581 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 400 : ℝ) (251233501831 / 250000000000 : ℝ)
    (11705807581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell125_denomUpper :
    Real.exp (36384258155816533 / 10000000000000000 : ℝ) ≤ (19015960161 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36384258155816533 / 10000000000000000 : ℝ)
    (1120416853557 / 1000000000000 : ℝ) (19015960161 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell125_denomLower :
    (189228649529 / 5000000000 : ℝ) ≤ Real.exp (4541897696650239 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4541897696650239 / 1250000000000000 : ℝ) (560122517381 /
    500000000000 : ℝ) (189228649529 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell125_product_lower :
    (4591116446650239 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (5 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell125_leftExp
    (by norm_num : (0 : ℝ) ≤ (11691184461 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell125_product_upper :
    Real.pi * Real.exp (63 / 400 : ℝ) ≤ (36774883155816533 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell125_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell125_endpointLower :
    (16787591773 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (5 / 64 : ℝ) (63 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4591116446650239 / 1250000000000000 : ℝ) (Real.pi * Real.exp (5 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell125_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 400 : ℝ) - (5 / 128 : ℝ)) ≤
      (19015960161 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell125_denomUpper
    linarith [hpThetaJensenCell125_product_upper]
  have hi : (1 / (19015960161 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 400 : ℝ) - (5 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19015960161 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19015960161 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((5 / 128 : ℝ) - Real.pi * Real.exp (63 / 400 : ℝ)) := by
    rw [show (5 / 128 : ℝ) - Real.pi * Real.exp (63 / 400 : ℝ) =
      -(Real.pi * Real.exp (63 / 400 : ℝ) - (5 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (5 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (5 / 32 : ℝ)) := by
    have h := hpThetaJensenCell125_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19015960161 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell125_endpointUpper :
    hpThetaJensenKernelEndpointUpper (5 / 64 : ℝ) (63 / 800 : ℝ) ≤ (8485793593 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 400 : ℝ)) (36774883155816533 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell125_product_upper
  have hD : (189228649529 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (5 / 32 : ℝ) - (63 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell125_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell125_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (5 / 32 : ℝ) - (63 / 1600 : ℝ)) ≤
      (1 / (189228649529 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (189228649529 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 1600 : ℝ) - Real.pi * Real.exp (5 / 32 : ℝ)) ≤
      (2 / (189228649529 / 5000000000 : ℝ) : ℝ) := by
    rw [show (63 / 1600 : ℝ) - Real.pi * Real.exp (5 / 32 : ℝ) =
      -(Real.pi * Real.exp (5 / 32 : ℝ) - (63 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36774883155816533 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36774883155816533 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell125_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (5 / 64 : ℝ) (63 / 800 : ℝ)) :
    (16787591773 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8485793593 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell125_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell125_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell126_leftExp :
    (11705807579 / 10000000000 : ℝ) ≤ Real.exp (63 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 400 : ℝ) (1004934007323 / 1000000000000 : ℝ)
    (11705807579 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell126_rightExp :
    Real.exp (127 / 800 : ℝ) ≤ (11720448989 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (127 / 800 : ℝ) (40198930533 / 40000000000 : ℝ)
    (11720448989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell126_denomUpper :
    Real.exp (36427130500699477 / 10000000000000000 : ℝ) ≤ (95488305259 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36427130500699477 / 10000000000000000 : ℝ)
    (1120566972669 / 1000000000000 : ℝ) (95488305259 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell126_denomLower :
    (15203245313 / 400000000 : ℝ) ≤ Real.exp (4547249555465721 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4547249555465721 / 1250000000000000 : ℝ) (560197464811 /
    500000000000 : ℝ) (15203245313 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell126_product_lower :
    (4596858930465721 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (63 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell126_leftExp
    (by norm_num : (0 : ℝ) ≤ (11705807579 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell126_product_upper :
    Real.pi * Real.exp (127 / 800 : ℝ) ≤ (36820880500699477 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell126_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell126_endpointLower :
    (8386033199 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 800 : ℝ) (127 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4596858930465721 / 1250000000000000 : ℝ) (Real.pi * Real.exp (63 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell126_product_lower
  have hD : Real.exp (Real.pi * Real.exp (127 / 800 : ℝ) - (63 / 1600 : ℝ)) ≤
      (95488305259 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell126_denomUpper
    linarith [hpThetaJensenCell126_product_upper]
  have hi : (1 / (95488305259 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (127 / 800 : ℝ) - (63 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (95488305259 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (95488305259 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 1600 : ℝ) - Real.pi * Real.exp (127 / 800 : ℝ)) := by
    rw [show (63 / 1600 : ℝ) - Real.pi * Real.exp (127 / 800 : ℝ) =
      -(Real.pi * Real.exp (127 / 800 : ℝ) - (63 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 400 : ℝ)) := by
    have h := hpThetaJensenCell126_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (95488305259 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell126_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 800 : ℝ) (127 / 1600 : ℝ) ≤ (16955958271 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (127 / 800 : ℝ)) (36820880500699477 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (127 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell126_product_upper
  have hD : (15203245313 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 400 : ℝ) - (127 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell126_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell126_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 400 : ℝ) - (127 / 3200 : ℝ)) ≤
      (1 / (15203245313 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15203245313 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((127 / 3200 : ℝ) - Real.pi * Real.exp (63 / 400 : ℝ)) ≤
      (2 / (15203245313 / 400000000 : ℝ) : ℝ) := by
    rw [show (127 / 3200 : ℝ) - Real.pi * Real.exp (63 / 400 : ℝ) =
      -(Real.pi * Real.exp (63 / 400 : ℝ) - (127 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36820880500699477 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36820880500699477 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell126_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 800 : ℝ) (127 / 1600 : ℝ)) :
    (8386033199 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16955958271 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell126_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell126_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell127_leftExp :
    (2930112247 / 2500000000 : ℝ) ≤ Real.exp (127 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (127 / 800 : ℝ) (251243315831 / 250000000000 : ℝ)
    (2930112247 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell127_rightExp :
    Real.exp (4 / 25 : ℝ) ≤ (11735108711 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4 / 25 : ℝ) (50250626043 / 50000000000 : ℝ)
    (11735108711 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell127_denomUpper :
    Real.exp (36470060380716623 / 10000000000000000 : ℝ) ≤ (383596466323 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36470060380716623 / 10000000000000000 : ℝ) (280179328349
    / 250000000000 : ℝ) (383596466323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell127_denomLower :
    (190857063667 / 5000000000 : ℝ) ≤ Real.exp (1138152149284653 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1138152149284653 / 312500000000000 : ℝ) (224109009151 /
    200000000000 : ℝ) (190857063667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell127_product_lower :
    (1150652149284653 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (127 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell127_leftExp
    (by norm_num : (0 : ℝ) ≤ (2930112247 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell127_product_upper :
    Real.pi * Real.exp (4 / 25 : ℝ) ≤ (36866935380716623 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell127_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell127_endpointLower :
    (3351285703 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (127 / 1600 : ℝ) (2 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1150652149284653 / 312500000000000 : ℝ) (Real.pi * Real.exp (127 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell127_product_lower
  have hD : Real.exp (Real.pi * Real.exp (4 / 25 : ℝ) - (127 / 3200 : ℝ)) ≤
      (383596466323 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell127_denomUpper
    linarith [hpThetaJensenCell127_product_upper]
  have hi : (1 / (383596466323 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (4 / 25 : ℝ) - (127 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (383596466323 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (383596466323 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((127 / 3200 : ℝ) - Real.pi * Real.exp (4 / 25 : ℝ)) := by
    rw [show (127 / 3200 : ℝ) - Real.pi * Real.exp (4 / 25 : ℝ) =
      -(Real.pi * Real.exp (4 / 25 : ℝ) - (127 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (127 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (127 / 800 : ℝ)) := by
    have h := hpThetaJensenCell127_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (383596466323 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell127_endpointUpper :
    hpThetaJensenKernelEndpointUpper (127 / 1600 : ℝ) (2 / 25 : ℝ) ≤ (3388043141 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (4 / 25 : ℝ)) (36866935380716623 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (2 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell127_product_upper
  have hD : (190857063667 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (127 / 800 : ℝ) - (1 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell127_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell127_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (127 / 800 : ℝ) - (1 / 25 : ℝ)) ≤
      (1 / (190857063667 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (190857063667 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 25 : ℝ) - Real.pi * Real.exp (127 / 800 : ℝ)) ≤
      (2 / (190857063667 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 25 : ℝ) - Real.pi * Real.exp (127 / 800 : ℝ) =
      -(Real.pi * Real.exp (127 / 800 : ℝ) - (1 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36866935380716623 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36866935380716623 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell127_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (127 / 1600 : ℝ) (2 / 25 : ℝ)) :
    (3351285703 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3388043141 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell127_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell127_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell128_leftExp :
    (11735108709 / 10000000000 : ℝ) ≤ Real.exp (4 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4 / 25 : ℝ) (1005012520859 / 1000000000000 : ℝ)
    (11735108709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell128_rightExp :
    Real.exp (129 / 800 : ℝ) ≤ (734361673 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (129 / 800 : ℝ) (125631472491 / 125000000000 : ℝ)
    (734361673 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell128_denomUpper :
    Real.exp (2282065491365089 / 625000000000000 : ℝ) ≤ (38524900027 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2282065491365089 / 625000000000000 : ℝ) (1120867876053 /
    1000000000000 : ℝ) (38524900027 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell128_denomLower :
    (383356343307 / 10000000000 : ℝ) ≤ Real.exp (4557974829915591 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4557974829915591 / 1250000000000000 : ℝ) (560347691739 /
    500000000000 : ℝ) (383356343307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell128_product_lower :
    (4608365454915591 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (4 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell128_leftExp
    (by norm_num : (0 : ℝ) ≤ (11735108709 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell128_product_upper :
    Real.pi * Real.exp (129 / 800 : ℝ) ≤ (2307065491365089 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell128_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell128_endpointLower :
    (8370339219 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (2 / 25 : ℝ) (129 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4608365454915591 / 1250000000000000 : ℝ) (Real.pi * Real.exp (4 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell128_product_lower
  have hD : Real.exp (Real.pi * Real.exp (129 / 800 : ℝ) - (1 / 25 : ℝ)) ≤
      (38524900027 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell128_denomUpper
    linarith [hpThetaJensenCell128_product_upper]
  have hi : (1 / (38524900027 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (129 / 800 : ℝ) - (1 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38524900027 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38524900027 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 25 : ℝ) - Real.pi * Real.exp (129 / 800 : ℝ)) := by
    rw [show (1 / 25 : ℝ) - Real.pi * Real.exp (129 / 800 : ℝ) =
      -(Real.pi * Real.exp (129 / 800 : ℝ) - (1 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (4 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (4 / 25 : ℝ)) := by
    have h := hpThetaJensenCell128_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38524900027 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell128_endpointUpper :
    hpThetaJensenKernelEndpointUpper (2 / 25 : ℝ) (129 / 1600 : ℝ) ≤ (16924359803 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (129 / 800 : ℝ)) (2307065491365089 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (129 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell128_product_upper
  have hD : (383356343307 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (4 / 25 : ℝ) - (129 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell128_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell128_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (4 / 25 : ℝ) - (129 / 3200 : ℝ)) ≤
      (1 / (383356343307 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (383356343307 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((129 / 3200 : ℝ) - Real.pi * Real.exp (4 / 25 : ℝ)) ≤
      (2 / (383356343307 / 10000000000 : ℝ) : ℝ) := by
    rw [show (129 / 3200 : ℝ) - Real.pi * Real.exp (4 / 25 : ℝ) =
      -(Real.pi * Real.exp (4 / 25 : ℝ) - (129 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2307065491365089 / 625000000000000 : ℝ) ^ 2 - 6 *
      (2307065491365089 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell128_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (2 / 25 : ℝ) (129 / 1600 : ℝ)) :
    (8370339219 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16924359803 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell128_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell128_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell129_leftExp :
    (11749786767 / 10000000000 : ℝ) ≤ Real.exp (129 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (129 / 800 : ℝ) (1005051779927 / 1000000000000 : ℝ)
    (11749786767 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell129_rightExp :
    Real.exp (13 / 80 : ℝ) ≤ (2352896637 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 80 : ℝ) (100509104053 / 100000000000 : ℝ)
    (2352896637 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell129_denomUpper :
    Real.exp (7311218604522741 / 2000000000000000 : ℝ) ≤ (48363860629 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7311218604522741 / 2000000000000000 : ℝ) (1121018661001
    / 1000000000000 : ℝ) (48363860629 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell129_denomLower :
    (385007842367 / 10000000000 : ℝ) ≤ Real.exp (4563348263614133 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4563348263614133 / 1250000000000000 : ℝ) (1120845943149
    / 1000000000000 : ℝ) (385007842367 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell129_product_lower :
    (4614129513614133 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (129 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell129_leftExp
    (by norm_num : (0 : ℝ) ≤ (11749786767 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell129_product_upper :
    Real.pi * Real.exp (13 / 80 : ℝ) ≤ (7391843604522741 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell129_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell129_endpointLower :
    (16724816477 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (129 / 1600 : ℝ) (13 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4614129513614133 / 1250000000000000 : ℝ) (Real.pi * Real.exp (129 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell129_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 80 : ℝ) - (129 / 3200 : ℝ)) ≤
      (48363860629 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell129_denomUpper
    linarith [hpThetaJensenCell129_product_upper]
  have hi : (1 / (48363860629 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 80 : ℝ) - (129 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (48363860629 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (48363860629 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((129 / 3200 : ℝ) - Real.pi * Real.exp (13 / 80 : ℝ)) := by
    rw [show (129 / 3200 : ℝ) - Real.pi * Real.exp (13 / 80 : ℝ) =
      -(Real.pi * Real.exp (13 / 80 : ℝ) - (129 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (129 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (129 / 800 : ℝ)) := by
    have h := hpThetaJensenCell129_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (48363860629 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell129_endpointUpper :
    hpThetaJensenKernelEndpointUpper (129 / 1600 : ℝ) (13 / 160 : ℝ) ≤ (4227097719 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 80 : ℝ)) (7391843604522741 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell129_product_upper
  have hD : (385007842367 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (129 / 800 : ℝ) - (13 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell129_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell129_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (129 / 800 : ℝ) - (13 / 320 : ℝ)) ≤
      (1 / (385007842367 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (385007842367 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 320 : ℝ) - Real.pi * Real.exp (129 / 800 : ℝ)) ≤
      (2 / (385007842367 / 10000000000 : ℝ) : ℝ) := by
    rw [show (13 / 320 : ℝ) - Real.pi * Real.exp (129 / 800 : ℝ) =
      -(Real.pi * Real.exp (129 / 800 : ℝ) - (13 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7391843604522741 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (7391843604522741 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell129_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (129 / 1600 : ℝ) (13 / 160 : ℝ)) :
    (16724816477 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4227097719 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell129_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell129_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell130_leftExp :
    (735280199 / 625000000 : ℝ) ≤ Real.exp (13 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 80 : ℝ) (1005091040529 / 1000000000000 : ℝ)
    (735280199 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell130_rightExp :
    Real.exp (131 / 800 : ℝ) ≤ (368099937 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (131 / 800 : ℝ) (502565151333 / 500000000000 : ℝ)
    (368099937 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell130_denomUpper :
    Real.exp (1143724872879641 / 312500000000000 : ℝ) ≤ (388582182817 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1143724872879641 / 312500000000000 : ℝ) (280292417141 /
    250000000000 : ℝ) (388582182817 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell130_denomLower :
    (77333737251 / 2000000000 : ℝ) ≤ Real.exp (285545556679601 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (285545556679601 / 78125000000000 : ℝ) (224199345019 /
    200000000000 : ℝ) (77333737251 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell130_product_lower :
    (288743798867101 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell130_leftExp
    (by norm_num : (0 : ℝ) ≤ (735280199 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell130_product_upper :
    Real.pi * Real.exp (131 / 800 : ℝ) ≤ (1156420185379641 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell130_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell130_endpointLower :
    (4177210737 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 160 : ℝ) (131 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (288743798867101 / 78125000000000 : ℝ) (Real.pi * Real.exp (13 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell130_product_lower
  have hD : Real.exp (Real.pi * Real.exp (131 / 800 : ℝ) - (13 / 320 : ℝ)) ≤
      (388582182817 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell130_denomUpper
    linarith [hpThetaJensenCell130_product_upper]
  have hi : (1 / (388582182817 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (131 / 800 : ℝ) - (13 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (388582182817 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (388582182817 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 320 : ℝ) - Real.pi * Real.exp (131 / 800 : ℝ)) := by
    rw [show (13 / 320 : ℝ) - Real.pi * Real.exp (131 / 800 : ℝ) =
      -(Real.pi * Real.exp (131 / 800 : ℝ) - (13 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 80 : ℝ)) := by
    have h := hpThetaJensenCell130_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (388582182817 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell130_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 160 : ℝ) (131 / 1600 : ℝ) ≤ (8446154621 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (131 / 800 : ℝ)) (1156420185379641 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (131 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell130_product_upper
  have hD : (77333737251 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 80 : ℝ) - (131 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell130_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell130_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 80 : ℝ) - (131 / 3200 : ℝ)) ≤
      (1 / (77333737251 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (77333737251 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((131 / 3200 : ℝ) - Real.pi * Real.exp (13 / 80 : ℝ)) ≤
      (2 / (77333737251 / 2000000000 : ℝ) : ℝ) := by
    rw [show (131 / 3200 : ℝ) - Real.pi * Real.exp (13 / 80 : ℝ) =
      -(Real.pi * Real.exp (13 / 80 : ℝ) - (131 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1156420185379641 / 312500000000000 : ℝ) ^ 2 - 6 *
      (1156420185379641 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell130_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 160 : ℝ) (131 / 1600 : ℝ)) :
    (4177210737 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8446154621 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell130_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell130_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell131_leftExp :
    (11779197983 / 10000000000 : ℝ) ≤ Real.exp (131 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (131 / 800 : ℝ) (201026060533 / 200000000000 : ℝ)
    (11779197983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell131_rightExp :
    Real.exp (33 / 200 : ℝ) ≤ (2948482797 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 200 : ℝ) (201033913267 / 200000000000 : ℝ)
    (2948482797 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell131_denomUpper :
    Real.exp (9160589165675621 / 2500000000000000 : ℝ) ≤ (195131478233 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9160589165675621 / 2500000000000000 : ℝ) (1121320899081
    / 1000000000000 : ℝ) (195131478233 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell131_denomLower :
    (194169468631 / 5000000000 : ℝ) ≤ Real.exp (4574116768726117 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4574116768726117 / 1250000000000000 : ℝ) (1121147729651
    / 1000000000000 : ℝ) (194169468631 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell131_product_lower :
    (4625679268726117 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (131 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell131_leftExp
    (by norm_num : (0 : ℝ) ≤ (11779197983 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell131_product_upper :
    Real.pi * Real.exp (33 / 200 : ℝ) ≤ (9262932915675621 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell131_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell131_endpointLower :
    (16692758169 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (131 / 1600 : ℝ) (33 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4625679268726117 / 1250000000000000 : ℝ) (Real.pi * Real.exp (131 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell131_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 200 : ℝ) - (131 / 3200 : ℝ)) ≤
      (195131478233 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell131_denomUpper
    linarith [hpThetaJensenCell131_product_upper]
  have hi : (1 / (195131478233 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 200 : ℝ) - (131 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (195131478233 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (195131478233 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((131 / 3200 : ℝ) - Real.pi * Real.exp (33 / 200 : ℝ)) := by
    rw [show (131 / 3200 : ℝ) - Real.pi * Real.exp (33 / 200 : ℝ) =
      -(Real.pi * Real.exp (33 / 200 : ℝ) - (131 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (131 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (131 / 800 : ℝ)) := by
    have h := hpThetaJensenCell131_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (195131478233 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell131_endpointUpper :
    hpThetaJensenKernelEndpointUpper (131 / 1600 : ℝ) (33 / 400 : ℝ) ≤ (843805761 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 200 : ℝ)) (9262932915675621 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell131_product_upper
  have hD : (194169468631 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (131 / 800 : ℝ) - (33 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell131_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell131_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (131 / 800 : ℝ) - (33 / 800 : ℝ)) ≤
      (1 / (194169468631 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (194169468631 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 800 : ℝ) - Real.pi * Real.exp (131 / 800 : ℝ)) ≤
      (2 / (194169468631 / 5000000000 : ℝ) : ℝ) := by
    rw [show (33 / 800 : ℝ) - Real.pi * Real.exp (131 / 800 : ℝ) =
      -(Real.pi * Real.exp (131 / 800 : ℝ) - (33 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9262932915675621 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9262932915675621 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell131_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (131 / 1600 : ℝ) (33 / 400 : ℝ)) :
    (16692758169 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (843805761 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell131_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell131_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell132_leftExp :
    (5896965593 / 5000000000 : ℝ) ≤ Real.exp (33 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 200 : ℝ) (502584783167 / 500000000000 : ℝ)
    (5896965593 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell132_rightExp :
    Real.exp (133 / 800 : ℝ) ≤ (590434141 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (133 / 800 : ℝ) (502604415769 / 500000000000 : ℝ)
    (590434141 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell132_denomUpper :
    Real.exp (1834278764326613 / 500000000000000 : ℝ) ≤ (97988317319 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1834278764326613 / 500000000000000 : ℝ) (112147235289 /
    100000000000 : ℝ) (97988317319 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell132_denomLower :
    (390018658089 / 10000000000 : ℝ) ≤ Real.exp (2289755928905507 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2289755928905507 / 625000000000000 : ℝ) (1121298957147 /
    1000000000000 : ℝ) (390018658089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell132_product_lower :
    (2315732491405507 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell132_leftExp
    (by norm_num : (0 : ℝ) ≤ (5896965593 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell132_product_upper :
    Real.pi * Real.exp (133 / 800 : ℝ) ≤ (1854903764326613 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell132_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell132_endpointLower :
    (3335312491 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 400 : ℝ) (133 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2315732491405507 / 625000000000000 : ℝ) (Real.pi * Real.exp (33 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell132_product_lower
  have hD : Real.exp (Real.pi * Real.exp (133 / 800 : ℝ) - (33 / 800 : ℝ)) ≤
      (97988317319 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell132_denomUpper
    linarith [hpThetaJensenCell132_product_upper]
  have hi : (1 / (97988317319 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (133 / 800 : ℝ) - (33 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (97988317319 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (97988317319 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 800 : ℝ) - Real.pi * Real.exp (133 / 800 : ℝ)) := by
    rw [show (33 / 800 : ℝ) - Real.pi * Real.exp (133 / 800 : ℝ) =
      -(Real.pi * Real.exp (133 / 800 : ℝ) - (33 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 200 : ℝ)) := by
    have h := hpThetaJensenCell132_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (97988317319 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell132_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 400 : ℝ) (133 / 1600 : ℝ) ≤ (4214952283 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (133 / 800 : ℝ)) (1854903764326613 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (133 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell132_product_upper
  have hD : (390018658089 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 200 : ℝ) - (133 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell132_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell132_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 200 : ℝ) - (133 / 3200 : ℝ)) ≤
      (1 / (390018658089 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (390018658089 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((133 / 3200 : ℝ) - Real.pi * Real.exp (33 / 200 : ℝ)) ≤
      (2 / (390018658089 / 10000000000 : ℝ) : ℝ) := by
    rw [show (133 / 3200 : ℝ) - Real.pi * Real.exp (33 / 200 : ℝ) =
      -(Real.pi * Real.exp (33 / 200 : ℝ) - (133 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1854903764326613 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1854903764326613 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell132_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 400 : ℝ) (133 / 1600 : ℝ)) :
    (3335312491 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4214952283 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell132_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell132_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell133_leftExp :
    (5904341409 / 5000000000 : ℝ) ≤ Real.exp (133 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (133 / 800 : ℝ) (1005208831537 / 1000000000000 : ℝ)
    (5904341409 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell133_rightExp :
    Real.exp (67 / 400 : ℝ) ≤ (5911726451 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 400 : ℝ) (40209923931 / 40000000000 : ℝ)
    (5911726451 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell133_denomUpper :
    Real.exp (18364425936376443 / 5000000000000000 : ℝ) ≤ (3075415507 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18364425936376443 / 5000000000000000 : ℝ) (560812015159
    / 500000000000 : ℝ) (3075415507 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell133_denomLower :
    (78341582441 / 2000000000 : ℝ) ≤ Real.exp (2292457091972891 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2292457091972891 / 625000000000000 : ℝ) (56072520397 /
    50000000000 : ℝ) (78341582441 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell133_product_lower :
    (2318628966972891 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (133 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell133_leftExp
    (by norm_num : (0 : ℝ) ≤ (5904341409 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell133_product_upper :
    Real.pi * Real.exp (67 / 400 : ℝ) ≤ (18572238436376443 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell133_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell133_endpointLower :
    (8330128069 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (133 / 1600 : ℝ) (67 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2318628966972891 / 625000000000000 : ℝ) (Real.pi * Real.exp (133 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell133_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 400 : ℝ) - (133 / 3200 : ℝ)) ≤
      (3075415507 / 78125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell133_denomUpper
    linarith [hpThetaJensenCell133_product_upper]
  have hi : (1 / (3075415507 / 78125000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 400 : ℝ) - (133 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3075415507 / 78125000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3075415507 / 78125000 : ℝ) : ℝ) ≤
      2 * Real.exp ((133 / 3200 : ℝ) - Real.pi * Real.exp (67 / 400 : ℝ)) := by
    rw [show (133 / 3200 : ℝ) - Real.pi * Real.exp (67 / 400 : ℝ) =
      -(Real.pi * Real.exp (67 / 400 : ℝ) - (133 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (133 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (133 / 800 : ℝ)) := by
    have h := hpThetaJensenCell133_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3075415507 / 78125000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell133_endpointUpper :
    hpThetaJensenKernelEndpointUpper (133 / 1600 : ℝ) (67 / 800 : ℝ) ≤ (2105423911 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 400 : ℝ)) (18572238436376443 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell133_product_upper
  have hD : (78341582441 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (133 / 800 : ℝ) - (67 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell133_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell133_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (133 / 800 : ℝ) - (67 / 1600 : ℝ)) ≤
      (1 / (78341582441 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (78341582441 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 1600 : ℝ) - Real.pi * Real.exp (133 / 800 : ℝ)) ≤
      (2 / (78341582441 / 2000000000 : ℝ) : ℝ) := by
    rw [show (67 / 1600 : ℝ) - Real.pi * Real.exp (133 / 800 : ℝ) =
      -(Real.pi * Real.exp (133 / 800 : ℝ) - (67 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18572238436376443 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18572238436376443 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell133_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (133 / 1600 : ℝ) (67 / 800 : ℝ)) :
    (8330128069 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2105423911 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell133_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell133_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell134_leftExp :
    (11823452901 / 10000000000 : ℝ) ≤ Real.exp (67 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 400 : ℝ) (502624049137 / 500000000000 : ℝ)
    (11823452901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell134_rightExp :
    Real.exp (27 / 160 : ℝ) ≤ (591912073 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 160 : ℝ) (502643683273 / 500000000000 : ℝ)
    (591912073 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell134_denomUpper :
    Real.exp (1838609325152289 / 500000000000000 : ℝ) ≤ (395362767957 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1838609325152289 / 500000000000000 : ℝ) (1121775931737 /
    1000000000000 : ℝ) (395362767957 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell134_denomLower :
    (196703381627 / 5000000000 : ℝ) ≤ Real.exp (4590323755769799 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4590323755769799 / 1250000000000000 : ℝ) (28040052059 /
    25000000000 : ℝ) (196703381627 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell134_product_lower :
    (4643058130769799 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell134_leftExp
    (by norm_num : (0 : ℝ) ≤ (11823452901 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell134_product_upper :
    Real.pi * Real.exp (27 / 160 : ℝ) ≤ (1859546825152289 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell134_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell134_endpointLower :
    (8321919761 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 800 : ℝ) (27 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4643058130769799 / 1250000000000000 : ℝ) (Real.pi * Real.exp (67 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell134_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 160 : ℝ) - (67 / 1600 : ℝ)) ≤
      (395362767957 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell134_denomUpper
    linarith [hpThetaJensenCell134_product_upper]
  have hi : (1 / (395362767957 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 160 : ℝ) - (67 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (395362767957 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (395362767957 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 1600 : ℝ) - Real.pi * Real.exp (27 / 160 : ℝ)) := by
    rw [show (67 / 1600 : ℝ) - Real.pi * Real.exp (27 / 160 : ℝ) =
      -(Real.pi * Real.exp (27 / 160 : ℝ) - (67 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 400 : ℝ)) := by
    have h := hpThetaJensenCell134_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (395362767957 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell134_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 800 : ℝ) (27 / 320 : ℝ) ≤ (16826862027 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 160 : ℝ)) (1859546825152289 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell134_product_upper
  have hD : (196703381627 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 400 : ℝ) - (27 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell134_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell134_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 400 : ℝ) - (27 / 640 : ℝ)) ≤
      (1 / (196703381627 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (196703381627 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 640 : ℝ) - Real.pi * Real.exp (67 / 400 : ℝ)) ≤
      (2 / (196703381627 / 5000000000 : ℝ) : ℝ) := by
    rw [show (27 / 640 : ℝ) - Real.pi * Real.exp (67 / 400 : ℝ) =
      -(Real.pi * Real.exp (67 / 400 : ℝ) - (27 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1859546825152289 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1859546825152289 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell134_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 800 : ℝ) (27 / 320 : ℝ)) :
    (8321919761 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16826862027 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell134_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell134_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell135_leftExp :
    (5919120729 / 5000000000 : ℝ) ≤ Real.exp (27 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 160 : ℝ) (201057473309 / 200000000000 : ℝ)
    (5919120729 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell135_rightExp :
    Real.exp (17 / 100 : ℝ) ≤ (5926524257 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 100 : ℝ) (1005326636351 / 1000000000000 : ℝ)
    (5926524257 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell135_denomUpper :
    Real.exp (18407789620121401 / 5000000000000000 : ℝ) ≤ (397082082809 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18407789620121401 / 5000000000000000 : ℝ) (1121928057451
    / 1000000000000 : ℝ) (397082082809 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell135_denomLower :
    (197557637711 / 5000000000 : ℝ) ≤ Real.exp (2297870291157571 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2297870291157571 / 625000000000000 : ℝ) (1121753980743 /
    1000000000000 : ℝ) (197557637711 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell135_product_lower :
    (2324432791157571 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell135_leftExp
    (by norm_num : (0 : ℝ) ≤ (5919120729 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell135_product_upper :
    Real.pi * Real.exp (17 / 100 : ℝ) ≤ (18618727120121401 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell135_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell135_endpointLower :
    (16627312947 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 320 : ℝ) (17 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2324432791157571 / 625000000000000 : ℝ) (Real.pi * Real.exp (27 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell135_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 100 : ℝ) - (27 / 640 : ℝ)) ≤
      (397082082809 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell135_denomUpper
    linarith [hpThetaJensenCell135_product_upper]
  have hi : (1 / (397082082809 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 100 : ℝ) - (27 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (397082082809 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (397082082809 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 640 : ℝ) - Real.pi * Real.exp (17 / 100 : ℝ)) := by
    rw [show (27 / 640 : ℝ) - Real.pi * Real.exp (17 / 100 : ℝ) =
      -(Real.pi * Real.exp (17 / 100 : ℝ) - (27 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 160 : ℝ)) := by
    have h := hpThetaJensenCell135_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (397082082809 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell135_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 320 : ℝ) (17 / 200 : ℝ) ≤ (16810221663 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 100 : ℝ)) (18618727120121401 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell135_product_upper
  have hD : (197557637711 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 160 : ℝ) - (17 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell135_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell135_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 160 : ℝ) - (17 / 400 : ℝ)) ≤
      (1 / (197557637711 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (197557637711 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 400 : ℝ) - Real.pi * Real.exp (27 / 160 : ℝ)) ≤
      (2 / (197557637711 / 5000000000 : ℝ) : ℝ) := by
    rw [show (17 / 400 : ℝ) - Real.pi * Real.exp (27 / 160 : ℝ) =
      -(Real.pi * Real.exp (27 / 160 : ℝ) - (17 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18618727120121401 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18618727120121401 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell135_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 320 : ℝ) (17 / 200 : ℝ)) :
    (16627312947 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16810221663 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell135_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell135_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell136_leftExp :
    (11853048513 / 10000000000 : ℝ) ≤ Real.exp (17 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 100 : ℝ) (20106532727 / 20000000000 : ℝ)
    (11853048513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell136_rightExp :
    Real.exp (137 / 800 : ℝ) ≤ (1483484261 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (137 / 800 : ℝ) (1005365907689 / 1000000000000 : ℝ)
    (1483484261 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell136_denomUpper :
    Real.exp (4607378769967773 / 1250000000000000 : ℝ) ≤ (199405597413 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4607378769967773 / 1250000000000000 : ℝ) (280520101953 /
    250000000000 : ℝ) (199405597413 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell136_denomLower :
    (99208378387 / 2500000000 : ℝ) ≤ Real.exp (4601164673006587 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4601164673006587 / 1250000000000000 : ℝ) (14023826293 /
    12500000000 : ℝ) (99208378387 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell136_product_lower :
    (4654680298006587 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell136_leftExp
    (by norm_num : (0 : ℝ) ≤ (11853048513 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell136_product_upper :
    Real.pi * Real.exp (137 / 800 : ℝ) ≤ (4660503769967773 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell136_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell136_endpointLower :
    (16610676737 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 200 : ℝ) (137 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4654680298006587 / 1250000000000000 : ℝ) (Real.pi * Real.exp (17 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell136_product_lower
  have hD : Real.exp (Real.pi * Real.exp (137 / 800 : ℝ) - (17 / 400 : ℝ)) ≤
      (199405597413 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell136_denomUpper
    linarith [hpThetaJensenCell136_product_upper]
  have hi : (1 / (199405597413 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (137 / 800 : ℝ) - (17 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (199405597413 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (199405597413 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 400 : ℝ) - Real.pi * Real.exp (137 / 800 : ℝ)) := by
    rw [show (17 / 400 : ℝ) - Real.pi * Real.exp (137 / 800 : ℝ) =
      -(Real.pi * Real.exp (137 / 800 : ℝ) - (17 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 100 : ℝ)) := by
    have h := hpThetaJensenCell136_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (199405597413 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell136_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 200 : ℝ) (137 / 1600 : ℝ) ≤ (8396735261 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (137 / 800 : ℝ)) (4660503769967773 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (137 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell136_product_upper
  have hD : (99208378387 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 100 : ℝ) - (137 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell136_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell136_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 100 : ℝ) - (137 / 3200 : ℝ)) ≤
      (1 / (99208378387 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (99208378387 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((137 / 3200 : ℝ) - Real.pi * Real.exp (17 / 100 : ℝ)) ≤
      (2 / (99208378387 / 2500000000 : ℝ) : ℝ) := by
    rw [show (137 / 3200 : ℝ) - Real.pi * Real.exp (17 / 100 : ℝ) =
      -(Real.pi * Real.exp (17 / 100 : ℝ) - (137 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4660503769967773 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4660503769967773 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell136_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 200 : ℝ) (137 / 1600 : ℝ)) :
    (16610676737 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8396735261 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell136_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell136_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell137_leftExp :
    (11867874087 / 10000000000 : ℝ) ≤ Real.exp (137 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (137 / 800 : ℝ) (125670738461 / 125000000000 : ℝ)
    (11867874087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell137_rightExp :
    Real.exp (69 / 400 : ℝ) ≤ (11882718207 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 400 : ℝ) (502702590281 / 500000000000 : ℝ)
    (11882718207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell137_denomUpper :
    Real.exp (36902539340083751 / 10000000000000000 : ℝ) ≤ (50068771247 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36902539340083751 / 10000000000000000 : ℝ)
    (1122232983181 / 1000000000000 : ℝ) (50068771247 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell137_denomLower :
    (39856154257 / 1000000000 : ℝ) ≤ Real.exp (4606596036090813 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4606596036090813 / 1250000000000000 : ℝ) (70128653173 /
    62500000000 : ℝ) (39856154257 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell137_product_lower :
    (4660502286090813 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (137 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell137_leftExp
    (by norm_num : (0 : ℝ) ≤ (11867874087 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell137_product_upper :
    Real.pi * Real.exp (69 / 400 : ℝ) ≤ (37330664340083751 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell137_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell137_endpointLower :
    (16593931201 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (137 / 1600 : ℝ) (69 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4660502286090813 / 1250000000000000 : ℝ) (Real.pi * Real.exp (137 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell137_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 400 : ℝ) - (137 / 3200 : ℝ)) ≤
      (50068771247 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell137_denomUpper
    linarith [hpThetaJensenCell137_product_upper]
  have hi : (1 / (50068771247 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 400 : ℝ) - (137 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (50068771247 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (50068771247 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((137 / 3200 : ℝ) - Real.pi * Real.exp (69 / 400 : ℝ)) := by
    rw [show (137 / 3200 : ℝ) - Real.pi * Real.exp (69 / 400 : ℝ) =
      -(Real.pi * Real.exp (69 / 400 : ℝ) - (137 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (137 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (137 / 800 : ℝ)) := by
    have h := hpThetaJensenCell137_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (50068771247 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell137_endpointUpper :
    hpThetaJensenKernelEndpointUpper (137 / 1600 : ℝ) (69 / 800 : ℝ) ≤ (16776608951 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 400 : ℝ)) (37330664340083751 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell137_product_upper
  have hD : (39856154257 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (137 / 800 : ℝ) - (69 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell137_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell137_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (137 / 800 : ℝ) - (69 / 1600 : ℝ)) ≤
      (1 / (39856154257 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (39856154257 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 1600 : ℝ) - Real.pi * Real.exp (137 / 800 : ℝ)) ≤
      (2 / (39856154257 / 1000000000 : ℝ) : ℝ) := by
    rw [show (69 / 1600 : ℝ) - Real.pi * Real.exp (137 / 800 : ℝ) =
      -(Real.pi * Real.exp (137 / 800 : ℝ) - (69 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37330664340083751 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (37330664340083751 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell137_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (137 / 1600 : ℝ) (69 / 800 : ℝ)) :
    (16593931201 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16776608951 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell137_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell137_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell138_leftExp :
    (2376543641 / 2000000000 : ℝ) ≤ Real.exp (69 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 400 : ℝ) (1005405180561 / 1000000000000 : ℝ)
    (2376543641 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell138_rightExp :
    Real.exp (139 / 800 : ℝ) ≤ (2974395223 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (139 / 800 : ℝ) (1005444454969 / 1000000000000 : ℝ)
    (2974395223 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell138_denomUpper :
    Real.exp (9236526711810239 / 2500000000000000 : ℝ) ≤ (402299074221 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9236526711810239 / 2500000000000000 : ℝ) (8979086271 /
    8000000000 : ℝ) (402299074221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell138_denomLower :
    (200149714201 / 5000000000 : ℝ) ≤ Real.exp (922406936277059 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (922406936277059 / 250000000000000 : ℝ) (1122211023087 /
    1000000000000 : ℝ) (200149714201 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell138_product_lower :
    (933266311277059 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell138_leftExp
    (by norm_num : (0 : ℝ) ≤ (2376543641 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell138_product_upper :
    Real.pi * Real.exp (139 / 800 : ℝ) ≤ (9344339211810239 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell138_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell138_endpointLower :
    (1036067293 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 800 : ℝ) (139 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (933266311277059 / 250000000000000 : ℝ) (Real.pi * Real.exp (69 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell138_product_lower
  have hD : Real.exp (Real.pi * Real.exp (139 / 800 : ℝ) - (69 / 1600 : ℝ)) ≤
      (402299074221 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell138_denomUpper
    linarith [hpThetaJensenCell138_product_upper]
  have hi : (1 / (402299074221 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (139 / 800 : ℝ) - (69 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (402299074221 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (402299074221 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 1600 : ℝ) - Real.pi * Real.exp (139 / 800 : ℝ)) := by
    rw [show (69 / 1600 : ℝ) - Real.pi * Real.exp (139 / 800 : ℝ) =
      -(Real.pi * Real.exp (139 / 800 : ℝ) - (69 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 400 : ℝ)) := by
    have h := hpThetaJensenCell138_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (402299074221 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell138_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 800 : ℝ) (139 / 1600 : ℝ) ≤ (1047477329 / 625000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (139 / 800 : ℝ)) (9344339211810239 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (139 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell138_product_upper
  have hD : (200149714201 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 400 : ℝ) - (139 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell138_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell138_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 400 : ℝ) - (139 / 3200 : ℝ)) ≤
      (1 / (200149714201 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (200149714201 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((139 / 3200 : ℝ) - Real.pi * Real.exp (69 / 400 : ℝ)) ≤
      (2 / (200149714201 / 5000000000 : ℝ) : ℝ) := by
    rw [show (139 / 3200 : ℝ) - Real.pi * Real.exp (69 / 400 : ℝ) =
      -(Real.pi * Real.exp (69 / 400 : ℝ) - (139 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9344339211810239 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9344339211810239 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell138_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 800 : ℝ) (139 / 1600 : ℝ)) :
    (1036067293 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1047477329 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell138_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell138_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell139_leftExp :
    (1189758089 / 1000000000 : ℝ) ≤ Real.exp (139 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (139 / 800 : ℝ) (125680556871 / 125000000000 : ℝ)
    (1189758089 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell139_rightExp :
    Real.exp (7 / 40 : ℝ) ≤ (11912462167 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 40 : ℝ) (100548373091 / 100000000000 : ℝ)
    (11912462167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell139_denomUpper :
    Real.exp (36989732756612031 / 10000000000000000 : ℝ) ≤ (404057974409 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36989732756612031 / 10000000000000000 : ℝ) (224507762049
    / 200000000000 : ℝ) (404057974409 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell139_denomLower :
    (1608188949 / 40000000 : ℝ) ≤ Real.exp (461748061792211 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (461748061792211 / 125000000000000 : ℝ) (1122363820739 /
    1000000000000 : ℝ) (1608188949 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell139_product_lower :
    (467216811792211 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (139 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell139_leftExp
    (by norm_num : (0 : ℝ) ≤ (1189758089 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell139_product_upper :
    Real.pi * Real.exp (7 / 40 : ℝ) ≤ (37424107756612031 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell139_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell139_endpointLower :
    (662404541 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (139 / 1600 : ℝ) (7 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (467216811792211 / 125000000000000 : ℝ) (Real.pi * Real.exp (139 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell139_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 40 : ℝ) - (139 / 3200 : ℝ)) ≤
      (404057974409 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell139_denomUpper
    linarith [hpThetaJensenCell139_product_upper]
  have hi : (1 / (404057974409 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 40 : ℝ) - (139 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (404057974409 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (404057974409 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((139 / 3200 : ℝ) - Real.pi * Real.exp (7 / 40 : ℝ)) := by
    rw [show (139 / 3200 : ℝ) - Real.pi * Real.exp (7 / 40 : ℝ) =
      -(Real.pi * Real.exp (7 / 40 : ℝ) - (139 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (139 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (139 / 800 : ℝ)) := by
    have h := hpThetaJensenCell139_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (404057974409 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell139_endpointUpper :
    hpThetaJensenKernelEndpointUpper (139 / 1600 : ℝ) (7 / 80 : ℝ) ≤ (8371277897 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 40 : ℝ)) (37424107756612031 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell139_product_upper
  have hD : (1608188949 / 40000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (139 / 800 : ℝ) - (7 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell139_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell139_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (139 / 800 : ℝ) - (7 / 160 : ℝ)) ≤
      (1 / (1608188949 / 40000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1608188949 / 40000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 160 : ℝ) - Real.pi * Real.exp (139 / 800 : ℝ)) ≤
      (2 / (1608188949 / 40000000 : ℝ) : ℝ) := by
    rw [show (7 / 160 : ℝ) - Real.pi * Real.exp (139 / 800 : ℝ) =
      -(Real.pi * Real.exp (139 / 800 : ℝ) - (7 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37424107756612031 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (37424107756612031 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell139_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (139 / 1600 : ℝ) (7 / 80 : ℝ)) :
    (662404541 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8371277897 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell139_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell139_endpointUpper

def hpThetaJensenCellsBatch006Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8431760143 / 5000000000 : ℝ)
  | 1 => (131629391 / 78125000 : ℝ)
  | 2 => (1052093111 / 625000000 : ℝ)
  | 3 => (16818303769 / 10000000000 : ℝ)
  | 4 => (1050187771 / 625000000 : ℝ)
  | 5 => (16787591773 / 10000000000 : ℝ)
  | 6 => (8386033199 / 5000000000 : ℝ)
  | 7 => (3351285703 / 2000000000 : ℝ)
  | 8 => (8370339219 / 5000000000 : ℝ)
  | 9 => (16724816477 / 10000000000 : ℝ)
  | 10 => (4177210737 / 2500000000 : ℝ)
  | 11 => (16692758169 / 10000000000 : ℝ)
  | 12 => (3335312491 / 2000000000 : ℝ)
  | 13 => (8330128069 / 5000000000 : ℝ)
  | 14 => (8321919761 / 5000000000 : ℝ)
  | 15 => (16627312947 / 10000000000 : ℝ)
  | 16 => (16610676737 / 10000000000 : ℝ)
  | 17 => (16593931201 / 10000000000 : ℝ)
  | 18 => (1036067293 / 625000000 : ℝ)
  | 19 => (662404541 / 400000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch006Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17048016179 / 10000000000 : ℝ)
  | 1 => (17032960147 / 10000000000 : ℝ)
  | 2 => (680711557 / 400000000 : ℝ)
  | 3 => (17002502821 / 10000000000 : ℝ)
  | 4 => (16987102137 / 10000000000 : ℝ)
  | 5 => (8485793593 / 5000000000 : ℝ)
  | 6 => (16955958271 / 10000000000 : ℝ)
  | 7 => (3388043141 / 2000000000 : ℝ)
  | 8 => (16924359803 / 10000000000 : ℝ)
  | 9 => (4227097719 / 2500000000 : ℝ)
  | 10 => (8446154621 / 5000000000 : ℝ)
  | 11 => (843805761 / 500000000 : ℝ)
  | 12 => (4214952283 / 2500000000 : ℝ)
  | 13 => (2105423911 / 1250000000 : ℝ)
  | 14 => (16826862027 / 10000000000 : ℝ)
  | 15 => (16810221663 / 10000000000 : ℝ)
  | 16 => (8396735261 / 5000000000 : ℝ)
  | 17 => (16776608951 / 10000000000 : ℝ)
  | 18 => (1047477329 / 625000000 : ℝ)
  | 19 => (8371277897 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch006_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch006Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch006Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell120_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell121_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell122_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell123_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell124_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell125_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell126_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell127_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell128_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell129_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell130_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell131_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell132_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell133_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell134_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell135_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell136_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell137_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell138_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell139_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper] at h ⊢
    exact h

end HodgeProofHP
