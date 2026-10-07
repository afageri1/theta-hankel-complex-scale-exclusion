import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell740_leftExp :
    (25218682603 / 10000000000 : ℝ) ≤ Real.exp (37 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 40 : ℝ) (1029328090443 / 1000000000000 : ℝ)
    (25218682603 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell740_rightExp :
    Real.exp (741 / 800 : ℝ) ≤ (6312556417 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (741 / 800 : ℝ) (1029368299357 / 1000000000000 : ℝ)
    (6312556417 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell740_denomUpper :
    Real.exp (19253358051752281 / 2500000000000000 : ℝ) ≤ (22113162837461 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19253358051752281 / 2500000000000000 : ℝ) (1272097325371
    / 1000000000000 : ℝ) (22113162837461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell740_denomLower :
    (10944108610731 / 5000000000 : ℝ) ≤ Real.exp (9613898314515497 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9613898314515497 / 1250000000000000 : ℝ) (63584546629 /
    50000000000 : ℝ) (10944108610731 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell740_product_lower :
    (9903351439515497 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell740_leftExp
    (by norm_num : (0 : ℝ) ≤ (25218682603 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell740_product_upper :
    Real.pi * Real.exp (741 / 800 : ℝ) ≤ (19831483051752281 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell740_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell740_endpointLower :
    (1840889257 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 80 : ℝ) (741 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9903351439515497 / 1250000000000000 : ℝ) (Real.pi * Real.exp (37 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell740_product_lower
  have hD : Real.exp (Real.pi * Real.exp (741 / 800 : ℝ) - (37 / 160 : ℝ)) ≤
      (22113162837461 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell740_denomUpper
    linarith [hpThetaJensenCell740_product_upper]
  have hi : (1 / (22113162837461 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (741 / 800 : ℝ) - (37 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22113162837461 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22113162837461 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 160 : ℝ) - Real.pi * Real.exp (741 / 800 : ℝ)) := by
    rw [show (37 / 160 : ℝ) - Real.pi * Real.exp (741 / 800 : ℝ) =
      -(Real.pi * Real.exp (741 / 800 : ℝ) - (37 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 40 : ℝ)) := by
    have h := hpThetaJensenCell740_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22113162837461 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell740_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 80 : ℝ) (741 / 1600 : ℝ) ≤ (58435009 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (741 / 800 : ℝ)) (19831483051752281 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (741 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell740_product_upper
  have hD : (10944108610731 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 40 : ℝ) - (741 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell740_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell740_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 40 : ℝ) - (741 / 3200 : ℝ)) ≤
      (1 / (10944108610731 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10944108610731 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((741 / 3200 : ℝ) - Real.pi * Real.exp (37 / 40 : ℝ)) ≤
      (2 / (10944108610731 / 5000000000 : ℝ) : ℝ) := by
    rw [show (741 / 3200 : ℝ) - Real.pi * Real.exp (37 / 40 : ℝ) =
      -(Real.pi * Real.exp (37 / 40 : ℝ) - (741 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19831483051752281 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (19831483051752281 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell740_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 80 : ℝ) (741 / 1600 : ℝ)) :
    (1840889257 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (58435009 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell740_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell740_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell741_leftExp :
    (12625112833 / 5000000000 : ℝ) ≤ Real.exp (741 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (741 / 800 : ℝ) (257342074839 / 250000000000 : ℝ)
    (12625112833 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell741_rightExp :
    Real.exp (371 / 400 : ℝ) ≤ (5056361637 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (371 / 400 : ℝ) (514704254921 / 500000000000 : ℝ)
    (5056361637 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell741_denomUpper :
    Real.exp (15421905324267741 / 2000000000000000 : ℝ) ≤ (22326682238647 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15421905324267741 / 2000000000000000 : ℝ) (1272479387257
    / 1000000000000 : ℝ) (22326682238647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell741_denomLower :
    (11049645306409 / 5000000000 : ℝ) ≤ Real.exp (4812947309406267 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4812947309406267 / 625000000000000 : ℝ) (1272072379561 /
    1000000000000 : ℝ) (11049645306409 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell741_product_lower :
    (4957869184406267 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (741 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell741_leftExp
    (by norm_num : (0 : ℝ) ≤ (12625112833 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell741_product_upper :
    Real.pi * Real.exp (371 / 400 : ℝ) ≤ (15885030324267741 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell741_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell741_endpointLower :
    (914190627 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (741 / 1600 : ℝ) (371 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4957869184406267 / 625000000000000 : ℝ) (Real.pi * Real.exp (741 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell741_product_lower
  have hD : Real.exp (Real.pi * Real.exp (371 / 400 : ℝ) - (741 / 3200 : ℝ)) ≤
      (22326682238647 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell741_denomUpper
    linarith [hpThetaJensenCell741_product_upper]
  have hi : (1 / (22326682238647 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (371 / 400 : ℝ) - (741 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22326682238647 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22326682238647 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((741 / 3200 : ℝ) - Real.pi * Real.exp (371 / 400 : ℝ)) := by
    rw [show (741 / 3200 : ℝ) - Real.pi * Real.exp (371 / 400 : ℝ) =
      -(Real.pi * Real.exp (371 / 400 : ℝ) - (741 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (741 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (741 / 800 : ℝ)) := by
    have h := hpThetaJensenCell741_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22326682238647 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell741_endpointUpper :
    hpThetaJensenKernelEndpointUpper (741 / 1600 : ℝ) (371 / 800 : ℝ) ≤ (1857237223 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (371 / 400 : ℝ)) (15885030324267741 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (371 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell741_product_upper
  have hD : (11049645306409 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (741 / 800 : ℝ) - (371 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell741_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell741_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (741 / 800 : ℝ) - (371 / 1600 : ℝ)) ≤
      (1 / (11049645306409 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11049645306409 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((371 / 1600 : ℝ) - Real.pi * Real.exp (741 / 800 : ℝ)) ≤
      (2 / (11049645306409 / 5000000000 : ℝ) : ℝ) := by
    rw [show (371 / 1600 : ℝ) - Real.pi * Real.exp (741 / 800 : ℝ) =
      -(Real.pi * Real.exp (741 / 800 : ℝ) - (371 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15885030324267741 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (15885030324267741 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell741_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (741 / 1600 : ℝ) (371 / 800 : ℝ)) :
    (914190627 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1857237223 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell741_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell741_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell742_leftExp :
    (25281808183 / 10000000000 : ℝ) ≤ Real.exp (371 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (371 / 400 : ℝ) (1029408509841 / 1000000000000 : ℝ)
    (25281808183 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell742_rightExp :
    Real.exp (743 / 800 : ℝ) ≤ (5062686041 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (743 / 800 : ℝ) (1029448721897 / 1000000000000 : ℝ)
    (5062686041 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell742_denomUpper :
    Real.exp (15441149027603313 / 2000000000000000 : ℝ) ≤ (22542543088759 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15441149027603313 / 2000000000000000 : ℝ) (1272862057533
    / 1000000000000 : ℝ) (22542543088759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell742_denomLower :
    (4462535199423 / 2000000000 : ℝ) ≤ Real.exp (9637906416655917 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9637906416655917 / 1250000000000000 : ℝ) (127245443383 /
    100000000000 : ℝ) (4462535199423 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell742_product_lower :
    (9928140791655917 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (371 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell742_leftExp
    (by norm_num : (0 : ℝ) ≤ (25281808183 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell742_product_upper :
    Real.pi * Real.exp (743 / 800 : ℝ) ≤ (15904899027603313 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell742_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell742_endpointLower :
    (453983721 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (371 / 800 : ℝ) (743 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9928140791655917 / 1250000000000000 : ℝ) (Real.pi * Real.exp (371 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell742_product_lower
  have hD : Real.exp (Real.pi * Real.exp (743 / 800 : ℝ) - (371 / 1600 : ℝ)) ≤
      (22542543088759 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell742_denomUpper
    linarith [hpThetaJensenCell742_product_upper]
  have hi : (1 / (22542543088759 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (743 / 800 : ℝ) - (371 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22542543088759 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22542543088759 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((371 / 1600 : ℝ) - Real.pi * Real.exp (743 / 800 : ℝ)) := by
    rw [show (371 / 1600 : ℝ) - Real.pi * Real.exp (743 / 800 : ℝ) =
      -(Real.pi * Real.exp (743 / 800 : ℝ) - (371 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (371 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (371 / 400 : ℝ)) := by
    have h := hpThetaJensenCell742_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22542543088759 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell742_endpointUpper :
    hpThetaJensenKernelEndpointUpper (371 / 800 : ℝ) (743 / 1600 : ℝ) ≤ (461154123 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (743 / 800 : ℝ)) (15904899027603313 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (743 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell742_product_upper
  have hD : (4462535199423 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (371 / 400 : ℝ) - (743 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell742_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell742_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (371 / 400 : ℝ) - (743 / 3200 : ℝ)) ≤
      (1 / (4462535199423 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4462535199423 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((743 / 3200 : ℝ) - Real.pi * Real.exp (371 / 400 : ℝ)) ≤
      (2 / (4462535199423 / 2000000000 : ℝ) : ℝ) := by
    rw [show (743 / 3200 : ℝ) - Real.pi * Real.exp (371 / 400 : ℝ) =
      -(Real.pi * Real.exp (371 / 400 : ℝ) - (743 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15904899027603313 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (15904899027603313 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell742_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (371 / 800 : ℝ) (743 / 1600 : ℝ)) :
    (453983721 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (461154123 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell742_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell742_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell743_leftExp :
    (25313430203 / 10000000000 : ℝ) ≤ Real.exp (743 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (743 / 800 : ℝ) (128681090237 / 125000000000 : ℝ)
    (25313430203 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell743_rightExp :
    Real.exp (93 / 100 : ℝ) ≤ (25345091777 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93 / 100 : ℝ) (1029488935523 / 1000000000000 : ℝ)
    (25345091777 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell743_denomUpper :
    Real.exp (77302087910980761 / 10000000000000000 : ℝ) ≤ (1422548359933 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77302087910980761 / 10000000000000000 : ℝ) (127324533729
    / 100000000000 : ℝ) (1422548359933 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell743_denomLower :
    (5632100339749 / 2500000000 : ℝ) ≤ Real.exp (9649933727287897 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9649933727287897 / 1250000000000000 : ℝ) (50913483859 /
    40000000000 : ℝ) (5632100339749 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell743_product_lower :
    (9940558727287897 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (743 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell743_leftExp
    (by norm_num : (0 : ℝ) ≤ (25313430203 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell743_product_upper :
    Real.pi * Real.exp (93 / 100 : ℝ) ≤ (79623962910980761 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell743_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell743_endpointLower :
    (901775011 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (743 / 1600 : ℝ) (93 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9940558727287897 / 1250000000000000 : ℝ) (Real.pi * Real.exp (743 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell743_product_lower
  have hD : Real.exp (Real.pi * Real.exp (93 / 100 : ℝ) - (743 / 3200 : ℝ)) ≤
      (1422548359933 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell743_denomUpper
    linarith [hpThetaJensenCell743_product_upper]
  have hi : (1 / (1422548359933 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (93 / 100 : ℝ) - (743 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1422548359933 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1422548359933 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((743 / 3200 : ℝ) - Real.pi * Real.exp (93 / 100 : ℝ)) := by
    rw [show (743 / 3200 : ℝ) - Real.pi * Real.exp (93 / 100 : ℝ) =
      -(Real.pi * Real.exp (93 / 100 : ℝ) - (743 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (743 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (743 / 800 : ℝ)) := by
    have h := hpThetaJensenCell743_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1422548359933 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell743_endpointUpper :
    hpThetaJensenKernelEndpointUpper (743 / 1600 : ℝ) (93 / 200 : ℝ) ≤ (114503623 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (93 / 100 : ℝ)) (79623962910980761 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (93 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell743_product_upper
  have hD : (5632100339749 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (743 / 800 : ℝ) - (93 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell743_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell743_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (743 / 800 : ℝ) - (93 / 400 : ℝ)) ≤
      (1 / (5632100339749 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5632100339749 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((93 / 400 : ℝ) - Real.pi * Real.exp (743 / 800 : ℝ)) ≤
      (2 / (5632100339749 / 2500000000 : ℝ) : ℝ) := by
    rw [show (93 / 400 : ℝ) - Real.pi * Real.exp (743 / 800 : ℝ) =
      -(Real.pi * Real.exp (743 / 800 : ℝ) - (93 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (79623962910980761 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (79623962910980761 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell743_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (743 / 1600 : ℝ) (93 / 200 : ℝ)) :
    (901775011 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (114503623 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell743_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell743_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell744_leftExp :
    (1013803671 / 400000000 : ℝ) ≤ Real.exp (93 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (93 / 100 : ℝ) (514744467761 / 500000000000 : ℝ)
    (1013803671 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell744_rightExp :
    Real.exp (149 / 160 : ℝ) ≤ (25376792951 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (149 / 160 : ℝ) (804319649 / 781250000 : ℝ)
    (25376792951 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell744_denomUpper :
    Real.exp (77398555097310943 / 10000000000000000 : ℝ) ≤ (22981403002483 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (77398555097310943 / 10000000000000000 : ℝ) (318407306909
    / 250000000000 : ℝ) (22981403002483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell744_denomLower :
    (22746495054039 / 10000000000 : ℝ) ≤ Real.exp (386479062798029 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (386479062798029 / 50000000000000 : ℝ) (1273220368591 /
    1000000000000 : ℝ) (22746495054039 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell744_product_lower :
    (398119687798029 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (93 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell744_leftExp
    (by norm_num : (0 : ℝ) ≤ (1013803671 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell744_product_upper :
    Real.pi * Real.exp (149 / 160 : ℝ) ≤ (79723555097310943 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell744_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell744_endpointLower :
    (895613269 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 200 : ℝ) (149 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (398119687798029 / 50000000000000 : ℝ) (Real.pi * Real.exp (93 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell744_product_lower
  have hD : Real.exp (Real.pi * Real.exp (149 / 160 : ℝ) - (93 / 400 : ℝ)) ≤
      (22981403002483 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell744_denomUpper
    linarith [hpThetaJensenCell744_product_upper]
  have hi : (1 / (22981403002483 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (149 / 160 : ℝ) - (93 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22981403002483 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22981403002483 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((93 / 400 : ℝ) - Real.pi * Real.exp (149 / 160 : ℝ)) := by
    rw [show (93 / 400 : ℝ) - Real.pi * Real.exp (149 / 160 : ℝ) =
      -(Real.pi * Real.exp (149 / 160 : ℝ) - (93 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (93 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (93 / 100 : ℝ)) := by
    have h := hpThetaJensenCell744_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22981403002483 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell744_endpointUpper :
    hpThetaJensenKernelEndpointUpper (93 / 200 : ℝ) (149 / 320 : ℝ) ≤ (909780761 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (149 / 160 : ℝ)) (79723555097310943 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (149 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell744_product_upper
  have hD : (22746495054039 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (93 / 100 : ℝ) - (149 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell744_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell744_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (93 / 100 : ℝ) - (149 / 640 : ℝ)) ≤
      (1 / (22746495054039 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (22746495054039 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((149 / 640 : ℝ) - Real.pi * Real.exp (93 / 100 : ℝ)) ≤
      (2 / (22746495054039 / 10000000000 : ℝ) : ℝ) := by
    rw [show (149 / 640 : ℝ) - Real.pi * Real.exp (93 / 100 : ℝ) =
      -(Real.pi * Real.exp (93 / 100 : ℝ) - (149 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (79723555097310943 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (79723555097310943 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell744_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (93 / 200 : ℝ) (149 / 320 : ℝ)) :
    (895613269 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (909780761 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell744_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell744_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell745_leftExp :
    (25376792949 / 10000000000 : ℝ) ≤ Real.exp (149 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (149 / 160 : ℝ) (1029529150719 / 1000000000000 : ℝ)
    (25376792949 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell745_rightExp :
    Real.exp (373 / 400 : ℝ) ≤ (1588033361 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (373 / 400 : ℝ) (16087021367 / 15625000000 : ℝ)
    (1588033361 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell745_denomUpper :
    Real.exp (4843446678184073 / 625000000000000 : ℝ) ≤ (23204459943147 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4843446678184073 / 625000000000000 : ℝ) (637006864833 /
    500000000000 : ℝ) (23204459943147 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell745_denomLower :
    (91867943261 / 40000000 : ℝ) ≤ Real.exp (9674034964279351 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9674034964279351 / 1250000000000000 : ℝ) (636802125641 /
    500000000000 : ℝ) (91867943261 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell745_product_lower :
    (9965441214279351 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (149 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell745_leftExp
    (by norm_num : (0 : ℝ) ≤ (25376792949 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell745_product_upper :
    Real.pi * Real.exp (373 / 400 : ℝ) ≤ (4988954490684073 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell745_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell745_endpointLower :
    (111185269 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (149 / 320 : ℝ) (373 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9965441214279351 / 1250000000000000 : ℝ) (Real.pi * Real.exp (149 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell745_product_lower
  have hD : Real.exp (Real.pi * Real.exp (373 / 400 : ℝ) - (149 / 640 : ℝ)) ≤
      (23204459943147 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell745_denomUpper
    linarith [hpThetaJensenCell745_product_upper]
  have hi : (1 / (23204459943147 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (373 / 400 : ℝ) - (149 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23204459943147 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23204459943147 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((149 / 640 : ℝ) - Real.pi * Real.exp (373 / 400 : ℝ)) := by
    rw [show (149 / 640 : ℝ) - Real.pi * Real.exp (373 / 400 : ℝ) =
      -(Real.pi * Real.exp (373 / 400 : ℝ) - (149 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (149 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (149 / 160 : ℝ)) := by
    have h := hpThetaJensenCell745_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23204459943147 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell745_endpointUpper :
    hpThetaJensenKernelEndpointUpper (149 / 320 : ℝ) (373 / 800 : ℝ) ≤ (903563513 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (373 / 400 : ℝ)) (4988954490684073 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (373 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell745_product_upper
  have hD : (91867943261 / 40000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (149 / 160 : ℝ) - (373 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell745_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell745_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (149 / 160 : ℝ) - (373 / 1600 : ℝ)) ≤
      (1 / (91867943261 / 40000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (91867943261 / 40000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((373 / 1600 : ℝ) - Real.pi * Real.exp (149 / 160 : ℝ)) ≤
      (2 / (91867943261 / 40000000 : ℝ) : ℝ) := by
    rw [show (373 / 1600 : ℝ) - Real.pi * Real.exp (149 / 160 : ℝ) =
      -(Real.pi * Real.exp (149 / 160 : ℝ) - (373 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4988954490684073 / 625000000000000 : ℝ) ^ 2 - 6 *
      (4988954490684073 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell745_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (149 / 320 : ℝ) (373 / 800 : ℝ)) :
    (111185269 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (903563513 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell745_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell745_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell746_leftExp :
    (12704266887 / 5000000000 : ℝ) ≤ Real.exp (373 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (373 / 400 : ℝ) (1029569367487 / 1000000000000 : ℝ)
    (12704266887 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell746_rightExp :
    Real.exp (747 / 800 : ℝ) ≤ (12720157151 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (747 / 800 : ℝ) (1029609585827 / 1000000000000 : ℝ)
    (12720157151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell746_denomUpper :
    Real.exp (38795931664481543 / 5000000000000000 : ℝ) ≤ (585749352397 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38795931664481543 / 5000000000000000 : ℝ) (1274398844489
    / 1000000000000 : ℝ) (585749352397 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell746_denomLower :
    (23189902749203 / 10000000000 : ℝ) ≤ Real.exp (4843054464758013 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4843054464758013 / 625000000000000 : ℝ) (254797749129 /
    200000000000 : ℝ) (23189902749203 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell746_product_lower :
    (4988952902258013 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (373 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell746_leftExp
    (by norm_num : (0 : ℝ) ≤ (12704266887 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell746_product_upper :
    Real.pi * Real.exp (747 / 800 : ℝ) ≤ (39961556664481543 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell746_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell746_endpointLower :
    (1766763191 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (373 / 800 : ℝ) (747 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4988952902258013 / 625000000000000 : ℝ) (Real.pi * Real.exp (373 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell746_product_lower
  have hD : Real.exp (Real.pi * Real.exp (747 / 800 : ℝ) - (373 / 1600 : ℝ)) ≤
      (585749352397 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell746_denomUpper
    linarith [hpThetaJensenCell746_product_upper]
  have hi : (1 / (585749352397 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (747 / 800 : ℝ) - (373 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (585749352397 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (585749352397 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((373 / 1600 : ℝ) - Real.pi * Real.exp (747 / 800 : ℝ)) := by
    rw [show (373 / 1600 : ℝ) - Real.pi * Real.exp (747 / 800 : ℝ) =
      -(Real.pi * Real.exp (747 / 800 : ℝ) - (373 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (373 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (373 / 400 : ℝ)) := by
    have h := hpThetaJensenCell746_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (585749352397 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell746_endpointUpper :
    hpThetaJensenKernelEndpointUpper (373 / 800 : ℝ) (747 / 1600 : ℝ) ≤ (448688587 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (747 / 800 : ℝ)) (39961556664481543 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (747 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell746_product_upper
  have hD : (23189902749203 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (373 / 400 : ℝ) - (747 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell746_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell746_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (373 / 400 : ℝ) - (747 / 3200 : ℝ)) ≤
      (1 / (23189902749203 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23189902749203 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((747 / 3200 : ℝ) - Real.pi * Real.exp (373 / 400 : ℝ)) ≤
      (2 / (23189902749203 / 10000000000 : ℝ) : ℝ) := by
    rw [show (747 / 3200 : ℝ) - Real.pi * Real.exp (373 / 400 : ℝ) =
      -(Real.pi * Real.exp (373 / 400 : ℝ) - (747 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39961556664481543 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (39961556664481543 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell746_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (373 / 800 : ℝ) (747 / 1600 : ℝ)) :
    (1766763191 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (448688587 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell746_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell746_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell747_leftExp :
    (254403143 / 100000000 : ℝ) ≤ Real.exp (747 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (747 / 800 : ℝ) (514804792913 / 500000000000 : ℝ)
    (254403143 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell747_rightExp :
    Real.exp (187 / 200 : ℝ) ≤ (12736067289 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (187 / 200 : ℝ) (1029649805737 / 1000000000000 : ℝ)
    (12736067289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell747_denomUpper :
    Real.exp (38844352342651377 / 5000000000000000 : ℝ) ≤ (23657975358401 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38844352342651377 / 5000000000000000 : ℝ) (318696143301
    / 250000000000 : ℝ) (23657975358401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell747_denomLower :
    (11707637676461 / 5000000000 : ℝ) ≤ Real.exp (96981984852957 / 12500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (96981984852957 / 12500000000000 : ℝ) (127437385279 /
    100000000000 : ℝ) (11707637676461 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell747_product_lower :
    (99903859852957 / 12500000000000 : ℝ) ≤ Real.pi * Real.exp (747 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell747_leftExp
    (by norm_num : (0 : ℝ) ≤ (254403143 / 100000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell747_product_upper :
    Real.pi * Real.exp (187 / 200 : ℝ) ≤ (40011539842651377 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell747_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell747_endpointLower :
    (877311533 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (747 / 1600 : ℝ) (187 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (99903859852957 / 12500000000000 : ℝ) (Real.pi * Real.exp (747 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell747_product_lower
  have hD : Real.exp (Real.pi * Real.exp (187 / 200 : ℝ) - (747 / 3200 : ℝ)) ≤
      (23657975358401 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell747_denomUpper
    linarith [hpThetaJensenCell747_product_upper]
  have hi : (1 / (23657975358401 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (187 / 200 : ℝ) - (747 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23657975358401 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23657975358401 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((747 / 3200 : ℝ) - Real.pi * Real.exp (187 / 200 : ℝ)) := by
    rw [show (747 / 3200 : ℝ) - Real.pi * Real.exp (187 / 200 : ℝ) =
      -(Real.pi * Real.exp (187 / 200 : ℝ) - (747 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (747 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (747 / 800 : ℝ)) := by
    have h := hpThetaJensenCell747_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23657975358401 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell747_endpointUpper :
    hpThetaJensenKernelEndpointUpper (747 / 1600 : ℝ) (187 / 400 : ℝ) ≤ (1782443357 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (187 / 200 : ℝ)) (40011539842651377 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (187 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell747_product_upper
  have hD : (11707637676461 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (747 / 800 : ℝ) - (187 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell747_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell747_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (747 / 800 : ℝ) - (187 / 800 : ℝ)) ≤
      (1 / (11707637676461 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11707637676461 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((187 / 800 : ℝ) - Real.pi * Real.exp (747 / 800 : ℝ)) ≤
      (2 / (11707637676461 / 5000000000 : ℝ) : ℝ) := by
    rw [show (187 / 800 : ℝ) - Real.pi * Real.exp (747 / 800 : ℝ) =
      -(Real.pi * Real.exp (747 / 800 : ℝ) - (187 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40011539842651377 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (40011539842651377 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell747_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (747 / 1600 : ℝ) (187 / 400 : ℝ)) :
    (877311533 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1782443357 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell747_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell747_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell748_leftExp :
    (1592008411 / 625000000 : ℝ) ≤ Real.exp (187 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (187 / 200 : ℝ) (128706225717 / 125000000000 : ℝ)
    (1592008411 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell748_rightExp :
    Real.exp (749 / 800 : ℝ) ≤ (5100798931 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (749 / 800 : ℝ) (514845013609 / 500000000000 : ℝ)
    (5100798931 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell748_denomUpper :
    Real.exp (15557134216037083 / 2000000000000000 : ℝ) ≤ (23888494038559 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15557134216037083 / 2000000000000000 : ℝ) (1275170916937
    / 1000000000000 : ℝ) (23888494038559 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell748_denomLower :
    (2364313350419 / 1000000000 : ℝ) ≤ Real.exp (606893978178789 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (606893978178789 / 78125000000000 : ℝ) (637379786907 /
    500000000000 : ℝ) (2364313350419 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell748_product_lower :
    (625180110991289 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (187 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell748_leftExp
    (by norm_num : (0 : ℝ) ≤ (1592008411 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell748_product_upper :
    Real.pi * Real.exp (749 / 800 : ℝ) ≤ (16024634216037083 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell748_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell748_endpointLower :
    (871271899 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (187 / 400 : ℝ) (749 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (625180110991289 / 78125000000000 : ℝ) (Real.pi * Real.exp (187 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell748_product_lower
  have hD : Real.exp (Real.pi * Real.exp (749 / 800 : ℝ) - (187 / 800 : ℝ)) ≤
      (23888494038559 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell748_denomUpper
    linarith [hpThetaJensenCell748_product_upper]
  have hi : (1 / (23888494038559 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (749 / 800 : ℝ) - (187 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23888494038559 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23888494038559 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((187 / 800 : ℝ) - Real.pi * Real.exp (749 / 800 : ℝ)) := by
    rw [show (187 / 800 : ℝ) - Real.pi * Real.exp (749 / 800 : ℝ) =
      -(Real.pi * Real.exp (749 / 800 : ℝ) - (187 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (187 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (187 / 200 : ℝ)) := by
    have h := hpThetaJensenCell748_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23888494038559 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell748_endpointUpper :
    hpThetaJensenKernelEndpointUpper (187 / 400 : ℝ) (749 / 1600 : ℝ) ≤ (1770193921 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (749 / 800 : ℝ)) (16024634216037083 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (749 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell748_product_upper
  have hD : (2364313350419 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (187 / 200 : ℝ) - (749 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell748_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell748_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (187 / 200 : ℝ) - (749 / 3200 : ℝ)) ≤
      (1 / (2364313350419 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2364313350419 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((749 / 3200 : ℝ) - Real.pi * Real.exp (187 / 200 : ℝ)) ≤
      (2 / (2364313350419 / 1000000000 : ℝ) : ℝ) := by
    rw [show (749 / 3200 : ℝ) - Real.pi * Real.exp (187 / 200 : ℝ) =
      -(Real.pi * Real.exp (187 / 200 : ℝ) - (749 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16024634216037083 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (16024634216037083 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell748_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (187 / 400 : ℝ) (749 / 1600 : ℝ)) :
    (871271899 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1770193921 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell748_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell748_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell749_leftExp :
    (25503994653 / 10000000000 : ℝ) ≤ Real.exp (749 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (749 / 800 : ℝ) (1029690027217 / 1000000000000 : ℝ)
    (25503994653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell749_rightExp :
    Real.exp (15 / 16 : ℝ) ≤ (12767947291 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15 / 16 : ℝ) (1029730250271 / 1000000000000 : ℝ)
    (12767947291 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell749_denomUpper :
    Real.exp (38941381333774563 / 5000000000000000 : ℝ) ≤ (4824312165957 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38941381333774563 / 5000000000000000 : ℝ) (127555787679
    / 100000000000 : ℝ) (4824312165957 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell749_denomLower :
    (23873507491817 / 10000000000 : ℝ) ≤ Real.exp (9722424446238447 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9722424446238447 / 1250000000000000 : ℝ) (1275145909843
    / 1000000000000 : ℝ) (23873507491817 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell749_product_lower :
    (10015393196238447 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (749 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell749_leftExp
    (by norm_num : (0 : ℝ) ≤ (25503994653 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell749_product_upper :
    Real.pi * Real.exp (15 / 16 : ℝ) ≤ (40111693833774563 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell749_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell749_endpointLower :
    (1730525253 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (749 / 1600 : ℝ) (15 / 32 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10015393196238447 / 1250000000000000 : ℝ) (Real.pi * Real.exp (749 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell749_product_lower
  have hD : Real.exp (Real.pi * Real.exp (15 / 16 : ℝ) - (749 / 3200 : ℝ)) ≤
      (4824312165957 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell749_denomUpper
    linarith [hpThetaJensenCell749_product_upper]
  have hi : (1 / (4824312165957 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (15 / 16 : ℝ) - (749 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4824312165957 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4824312165957 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((749 / 3200 : ℝ) - Real.pi * Real.exp (15 / 16 : ℝ)) := by
    rw [show (749 / 3200 : ℝ) - Real.pi * Real.exp (15 / 16 : ℝ) =
      -(Real.pi * Real.exp (15 / 16 : ℝ) - (749 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (749 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (749 / 800 : ℝ)) := by
    have h := hpThetaJensenCell749_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4824312165957 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell749_endpointUpper :
    hpThetaJensenKernelEndpointUpper (749 / 1600 : ℝ) (15 / 32 : ℝ) ≤ (879002953 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (15 / 16 : ℝ)) (40111693833774563 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (15 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell749_product_upper
  have hD : (23873507491817 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (749 / 800 : ℝ) - (15 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell749_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell749_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (749 / 800 : ℝ) - (15 / 64 : ℝ)) ≤
      (1 / (23873507491817 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23873507491817 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((15 / 64 : ℝ) - Real.pi * Real.exp (749 / 800 : ℝ)) ≤
      (2 / (23873507491817 / 10000000000 : ℝ) : ℝ) := by
    rw [show (15 / 64 : ℝ) - Real.pi * Real.exp (749 / 800 : ℝ) =
      -(Real.pi * Real.exp (749 / 800 : ℝ) - (15 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40111693833774563 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (40111693833774563 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell749_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (749 / 1600 : ℝ) (15 / 32 : ℝ)) :
    (1730525253 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (879002953 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell749_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell749_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell750_leftExp :
    (1276794729 / 500000000 : ℝ) ≤ Real.exp (15 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15 / 16 : ℝ) (102973025027 / 100000000000 : ℝ)
    (1276794729 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell750_rightExp :
    Real.exp (751 / 800 : ℝ) ≤ (3195979301 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (751 / 800 : ℝ) (514885237447 / 500000000000 : ℝ)
    (3195979301 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell750_denomUpper :
    Real.exp (9747497450166493 / 1250000000000000 : ℝ) ≤ (6089301707679 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9747497450166493 / 1250000000000000 : ℝ) (255189090773 /
    200000000000 : ℝ) (6089301707679 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell750_denomLower :
    (24106427990559 / 10000000000 : ℝ) ≤ Real.exp (486728044533571 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (486728044533571 / 62500000000000 : ℝ) (63776643099 /
    50000000000 : ℝ) (24106427990559 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell750_product_lower :
    (501396013283571 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (15 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell750_leftExp
    (by norm_num : (0 : ℝ) ≤ (1276794729 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell750_product_upper :
    Real.pi * Real.exp (751 / 800 : ℝ) ≤ (10040466200166493 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell750_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell750_endpointLower :
    (17185673 / 100000000 : ℝ) ≤ hpThetaTraceEndpointLower (15 / 32 : ℝ) (751 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (501396013283571 / 62500000000000 : ℝ) (Real.pi * Real.exp (15 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell750_product_lower
  have hD : Real.exp (Real.pi * Real.exp (751 / 800 : ℝ) - (15 / 64 : ℝ)) ≤
      (6089301707679 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell750_denomUpper
    linarith [hpThetaJensenCell750_product_upper]
  have hi : (1 / (6089301707679 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (751 / 800 : ℝ) - (15 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6089301707679 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6089301707679 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((15 / 64 : ℝ) - Real.pi * Real.exp (751 / 800 : ℝ)) := by
    rw [show (15 / 64 : ℝ) - Real.pi * Real.exp (751 / 800 : ℝ) =
      -(Real.pi * Real.exp (751 / 800 : ℝ) - (15 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (15 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (15 / 16 : ℝ)) := by
    have h := hpThetaJensenCell750_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6089301707679 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell750_endpointUpper :
    hpThetaJensenKernelEndpointUpper (15 / 32 : ℝ) (751 / 1600 : ℝ) ≤ (872939589 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (751 / 800 : ℝ)) (10040466200166493 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (751 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell750_product_upper
  have hD : (24106427990559 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (15 / 16 : ℝ) - (751 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell750_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell750_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (15 / 16 : ℝ) - (751 / 3200 : ℝ)) ≤
      (1 / (24106427990559 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (24106427990559 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((751 / 3200 : ℝ) - Real.pi * Real.exp (15 / 16 : ℝ)) ≤
      (2 / (24106427990559 / 10000000000 : ℝ) : ℝ) := by
    rw [show (751 / 3200 : ℝ) - Real.pi * Real.exp (15 / 16 : ℝ) =
      -(Real.pi * Real.exp (15 / 16 : ℝ) - (751 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10040466200166493 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (10040466200166493 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell750_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (15 / 32 : ℝ) (751 / 1600 : ℝ)) :
    (17185673 / 100000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (872939589 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell750_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell750_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell751_leftExp :
    (12783917203 / 5000000000 : ℝ) ≤ Real.exp (751 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (751 / 800 : ℝ) (1029770474893 / 1000000000000 : ℝ)
    (12783917203 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell751_rightExp :
    Real.exp (47 / 50 : ℝ) ≤ (3199976773 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 50 : ℝ) (1029810701089 / 1000000000000 : ℝ)
    (3199976773 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell751_denomUpper :
    Real.exp (9759665255219389 / 1250000000000000 : ℝ) ≤ (12297731785013 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9759665255219389 / 1250000000000000 : ℝ) (255266729859 /
    200000000000 : ℝ) (12297731785013 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell751_denomLower :
    (24341926080143 / 10000000000 : ℝ) ≤ Real.exp (4873356501700897 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4873356501700897 / 625000000000000 : ℝ) (39872513479 /
    31250000000 : ℝ) (24341926080143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell751_product_lower :
    (5020231501700897 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (751 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell751_leftExp
    (by norm_num : (0 : ℝ) ≤ (12783917203 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell751_product_upper :
    Real.pi * Real.exp (47 / 50 : ℝ) ≤ (10053024630219389 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell751_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell751_endpointLower :
    (853334901 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (751 / 1600 : ℝ) (47 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5020231501700897 / 625000000000000 : ℝ) (Real.pi * Real.exp (751 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell751_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 50 : ℝ) - (751 / 3200 : ℝ)) ≤
      (12297731785013 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell751_denomUpper
    linarith [hpThetaJensenCell751_product_upper]
  have hi : (1 / (12297731785013 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 50 : ℝ) - (751 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12297731785013 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12297731785013 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((751 / 3200 : ℝ) - Real.pi * Real.exp (47 / 50 : ℝ)) := by
    rw [show (751 / 3200 : ℝ) - Real.pi * Real.exp (47 / 50 : ℝ) =
      -(Real.pi * Real.exp (47 / 50 : ℝ) - (751 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (751 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (751 / 800 : ℝ)) := by
    have h := hpThetaJensenCell751_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12297731785013 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell751_endpointUpper :
    hpThetaJensenKernelEndpointUpper (751 / 1600 : ℝ) (47 / 100 : ℝ) ≤ (1733813603 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 50 : ℝ)) (10053024630219389 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell751_product_upper
  have hD : (24341926080143 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (751 / 800 : ℝ) - (47 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell751_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell751_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (751 / 800 : ℝ) - (47 / 200 : ℝ)) ≤
      (1 / (24341926080143 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (24341926080143 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 200 : ℝ) - Real.pi * Real.exp (751 / 800 : ℝ)) ≤
      (2 / (24341926080143 / 10000000000 : ℝ) : ℝ) := by
    rw [show (47 / 200 : ℝ) - Real.pi * Real.exp (751 / 800 : ℝ) =
      -(Real.pi * Real.exp (751 / 800 : ℝ) - (47 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10053024630219389 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (10053024630219389 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell751_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (751 / 1600 : ℝ) (47 / 100 : ℝ)) :
    (853334901 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1733813603 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell751_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell751_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell752_leftExp :
    (12799907091 / 5000000000 : ℝ) ≤ Real.exp (47 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 50 : ℝ) (32181584409 / 31250000000 : ℝ)
    (12799907091 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell752_rightExp :
    Real.exp (753 / 800 : ℝ) ≤ (640795849 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (753 / 800 : ℝ) (205970185771 / 200000000000 : ℝ)
    (640795849 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell752_denomUpper :
    Real.exp (1954369753647457 / 250000000000000 : ℝ) ≤ (3104545372907 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1954369753647457 / 250000000000000 : ℝ) (319180616049 /
    250000000000 : ℝ) (3104545372907 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell752_denomLower :
    (384063019797 / 156250000 : ℝ) ≤ Real.exp (4879440402228609 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4879440402228609 / 625000000000000 : ℝ) (159538577377 /
    125000000000 : ℝ) (384063019797 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell752_product_lower :
    (5026510714728609 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell752_leftExp
    (by norm_num : (0 : ℝ) ≤ (12799907091 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell752_product_upper :
    Real.pi * Real.exp (753 / 800 : ℝ) ≤ (2013119753647457 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell752_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell752_endpointLower :
    (1694832623 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 100 : ℝ) (753 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5026510714728609 / 625000000000000 : ℝ) (Real.pi * Real.exp (47 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell752_product_lower
  have hD : Real.exp (Real.pi * Real.exp (753 / 800 : ℝ) - (47 / 200 : ℝ)) ≤
      (3104545372907 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell752_denomUpper
    linarith [hpThetaJensenCell752_product_upper]
  have hi : (1 / (3104545372907 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (753 / 800 : ℝ) - (47 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3104545372907 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3104545372907 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 200 : ℝ) - Real.pi * Real.exp (753 / 800 : ℝ)) := by
    rw [show (47 / 200 : ℝ) - Real.pi * Real.exp (753 / 800 : ℝ) =
      -(Real.pi * Real.exp (753 / 800 : ℝ) - (47 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 50 : ℝ)) := by
    have h := hpThetaJensenCell752_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3104545372907 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell752_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 100 : ℝ) (753 / 1600 : ℝ) ≤ (1721809043 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (753 / 800 : ℝ)) (2013119753647457 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (753 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell752_product_upper
  have hD : (384063019797 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 50 : ℝ) - (753 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell752_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell752_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 50 : ℝ) - (753 / 3200 : ℝ)) ≤
      (1 / (384063019797 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (384063019797 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((753 / 3200 : ℝ) - Real.pi * Real.exp (47 / 50 : ℝ)) ≤
      (2 / (384063019797 / 156250000 : ℝ) : ℝ) := by
    rw [show (753 / 3200 : ℝ) - Real.pi * Real.exp (47 / 50 : ℝ) =
      -(Real.pi * Real.exp (47 / 50 : ℝ) - (753 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2013119753647457 / 250000000000000 : ℝ) ^ 2 - 6 *
      (2013119753647457 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell752_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 100 : ℝ) (753 / 1600 : ℝ)) :
    (1694832623 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1721809043 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell752_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell752_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell753_leftExp :
    (12815916979 / 5000000000 : ℝ) ≤ Real.exp (753 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (753 / 800 : ℝ) (514925464427 / 500000000000 : ℝ)
    (12815916979 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell753_rightExp :
    Real.exp (377 / 400 : ℝ) ≤ (12831946893 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (377 / 400 : ℝ) (1029891158193 / 1000000000000 : ℝ)
    (12831946893 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell753_denomUpper :
    Real.exp (39136192035420549 / 5000000000000000 : ℝ) ≤ (25079937433933 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39136192035420549 / 5000000000000000 : ℝ) (319277974923
    / 250000000000 : ℝ) (25079937433933 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell753_denomLower :
    (24820781470333 / 10000000000 : ℝ) ≤ Real.exp (4885532156736321 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4885532156736321 / 625000000000000 : ℝ) (638348713083 /
    500000000000 : ℝ) (24820781470333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell753_product_lower :
    (5032797781736321 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (753 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell753_leftExp
    (by norm_num : (0 : ℝ) ≤ (12815916979 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell753_product_upper :
    Real.pi * Real.exp (377 / 400 : ℝ) ≤ (40312754535420549 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell753_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell753_endpointLower :
    (420763907 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (753 / 1600 : ℝ) (377 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5032797781736321 / 625000000000000 : ℝ) (Real.pi * Real.exp (753 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell753_product_lower
  have hD : Real.exp (Real.pi * Real.exp (377 / 400 : ℝ) - (753 / 3200 : ℝ)) ≤
      (25079937433933 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell753_denomUpper
    linarith [hpThetaJensenCell753_product_upper]
  have hi : (1 / (25079937433933 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (377 / 400 : ℝ) - (753 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (25079937433933 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (25079937433933 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((753 / 3200 : ℝ) - Real.pi * Real.exp (377 / 400 : ℝ)) := by
    rw [show (753 / 3200 : ℝ) - Real.pi * Real.exp (377 / 400 : ℝ) =
      -(Real.pi * Real.exp (377 / 400 : ℝ) - (753 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (753 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (753 / 800 : ℝ)) := by
    have h := hpThetaJensenCell753_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (25079937433933 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell753_endpointUpper :
    hpThetaJensenKernelEndpointUpper (753 / 1600 : ℝ) (377 / 800 : ℝ) ≤ (854932681 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (377 / 400 : ℝ)) (40312754535420549 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (377 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell753_product_upper
  have hD : (24820781470333 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (753 / 800 : ℝ) - (377 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell753_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell753_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (753 / 800 : ℝ) - (377 / 1600 : ℝ)) ≤
      (1 / (24820781470333 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (24820781470333 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((377 / 1600 : ℝ) - Real.pi * Real.exp (753 / 800 : ℝ)) ≤
      (2 / (24820781470333 / 10000000000 : ℝ) : ℝ) := by
    rw [show (377 / 1600 : ℝ) - Real.pi * Real.exp (753 / 800 : ℝ) =
      -(Real.pi * Real.exp (753 / 800 : ℝ) - (377 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40312754535420549 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (40312754535420549 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell753_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (753 / 1600 : ℝ) (377 / 800 : ℝ)) :
    (420763907 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (854932681 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell753_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell753_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell754_leftExp :
    (3207986723 / 1250000000 : ℝ) ≤ Real.exp (377 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (377 / 400 : ℝ) (64368197387 / 62500000000 : ℝ)
    (3207986723 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell754_rightExp :
    Real.exp (151 / 160 : ℝ) ≤ (25695993711 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (151 / 160 : ℝ) (514965694551 / 500000000000 : ℝ)
    (25695993711 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell754_denomUpper :
    Real.exp (78370103970521623 / 10000000000000000 : ℝ) ≤ (5065243941041 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (78370103970521623 / 10000000000000000 : ℝ) (319375489223
    / 250000000000 : ℝ) (5065243941041 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell754_denomLower :
    (12532101514809 / 5000000000 : ℝ) ≤ Real.exp (1222907943760377 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1222907943760377 / 156250000000000 : ℝ) (159635856737 /
    125000000000 : ℝ) (12532101514809 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell754_product_lower :
    (1259773178135377 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (377 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell754_leftExp
    (by norm_num : (0 : ℝ) ≤ (3207986723 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell754_product_upper :
    Real.pi * Real.exp (151 / 160 : ℝ) ≤ (80726353970521623 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell754_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell754_endpointLower :
    (835669339 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (377 / 800 : ℝ) (151 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1259773178135377 / 156250000000000 : ℝ) (Real.pi * Real.exp (377 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell754_product_lower
  have hD : Real.exp (Real.pi * Real.exp (151 / 160 : ℝ) - (377 / 1600 : ℝ)) ≤
      (5065243941041 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell754_denomUpper
    linarith [hpThetaJensenCell754_product_upper]
  have hi : (1 / (5065243941041 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (151 / 160 : ℝ) - (377 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5065243941041 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5065243941041 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((377 / 1600 : ℝ) - Real.pi * Real.exp (151 / 160 : ℝ)) := by
    rw [show (377 / 1600 : ℝ) - Real.pi * Real.exp (151 / 160 : ℝ) =
      -(Real.pi * Real.exp (151 / 160 : ℝ) - (377 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (377 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (377 / 400 : ℝ)) := by
    have h := hpThetaJensenCell754_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5065243941041 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell754_endpointUpper :
    hpThetaJensenKernelEndpointUpper (377 / 800 : ℝ) (151 / 320 : ℝ) ≤ (848991211 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (151 / 160 : ℝ)) (80726353970521623 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (151 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell754_product_upper
  have hD : (12532101514809 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (377 / 400 : ℝ) - (151 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell754_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell754_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (377 / 400 : ℝ) - (151 / 640 : ℝ)) ≤
      (1 / (12532101514809 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12532101514809 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((151 / 640 : ℝ) - Real.pi * Real.exp (377 / 400 : ℝ)) ≤
      (2 / (12532101514809 / 5000000000 : ℝ) : ℝ) := by
    rw [show (151 / 640 : ℝ) - Real.pi * Real.exp (377 / 400 : ℝ) =
      -(Real.pi * Real.exp (377 / 400 : ℝ) - (151 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (80726353970521623 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (80726353970521623 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell754_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (377 / 800 : ℝ) (151 / 320 : ℝ)) :
    (835669339 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (848991211 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell754_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell754_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell755_leftExp :
    (25695993709 / 10000000000 : ℝ) ≤ Real.exp (151 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (151 / 160 : ℝ) (1029931389101 / 1000000000000 : ℝ)
    (25695993709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell755_rightExp :
    Real.exp (189 / 200 : ℝ) ≤ (25728133787 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (189 / 200 : ℝ) (1029971621583 / 1000000000000 : ℝ)
    (25728133787 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell755_denomUpper :
    Real.exp (78467950008302691 / 10000000000000000 : ℝ) ≤ (2557524304069 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (78467950008302691 / 10000000000000000 : ℝ) (255578527389
    / 200000000000 : ℝ) (2557524304069 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell755_denomLower :
    (5062066141857 / 2000000000 : ℝ) ≤ Real.exp (9795478533530591 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9795478533530591 / 1250000000000000 : ℝ) (638738451659 /
    500000000000 : ℝ) (5062066141857 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell755_product_lower :
    (10090791033530591 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (151 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell755_leftExp
    (by norm_num : (0 : ℝ) ≤ (25695993709 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell755_product_upper :
    Real.pi * Real.exp (189 / 200 : ℝ) ≤ (80827325008302691 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell755_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell755_endpointLower :
    (414920409 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (151 / 320 : ℝ) (189 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10090791033530591 / 1250000000000000 : ℝ) (Real.pi * Real.exp (151 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell755_product_lower
  have hD : Real.exp (Real.pi * Real.exp (189 / 200 : ℝ) - (151 / 640 : ℝ)) ≤
      (2557524304069 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell755_denomUpper
    linarith [hpThetaJensenCell755_product_upper]
  have hi : (1 / (2557524304069 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (189 / 200 : ℝ) - (151 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2557524304069 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2557524304069 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((151 / 640 : ℝ) - Real.pi * Real.exp (189 / 200 : ℝ)) := by
    rw [show (151 / 640 : ℝ) - Real.pi * Real.exp (189 / 200 : ℝ) =
      -(Real.pi * Real.exp (189 / 200 : ℝ) - (151 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (151 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (151 / 160 : ℝ)) := by
    have h := hpThetaJensenCell755_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2557524304069 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell755_endpointUpper :
    hpThetaJensenKernelEndpointUpper (151 / 320 : ℝ) (189 / 400 : ℝ) ≤ (1686160083 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (189 / 200 : ℝ)) (80827325008302691 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (189 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell755_product_upper
  have hD : (5062066141857 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (151 / 160 : ℝ) - (189 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell755_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell755_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (151 / 160 : ℝ) - (189 / 800 : ℝ)) ≤
      (1 / (5062066141857 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5062066141857 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((189 / 800 : ℝ) - Real.pi * Real.exp (151 / 160 : ℝ)) ≤
      (2 / (5062066141857 / 2000000000 : ℝ) : ℝ) := by
    rw [show (189 / 800 : ℝ) - Real.pi * Real.exp (151 / 160 : ℝ) =
      -(Real.pi * Real.exp (151 / 160 : ℝ) - (189 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (80827325008302691 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (80827325008302691 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell755_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (151 / 320 : ℝ) (189 / 400 : ℝ)) :
    (414920409 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1686160083 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell755_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell755_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell756_leftExp :
    (5145626757 / 2000000000 : ℝ) ≤ Real.exp (189 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (189 / 200 : ℝ) (514985810791 / 500000000000 : ℝ)
    (5145626757 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell756_rightExp :
    Real.exp (757 / 800 : ℝ) ≤ (25760314063 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (757 / 800 : ℝ) (206002371127 / 200000000000 : ℝ)
    (25760314063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell756_denomUpper :
    Real.exp (78565922338122359 / 10000000000000000 : ℝ) ≤ (25827041103377 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (78565922338122359 / 10000000000000000 : ℝ) (255656788193
    / 200000000000 : ℝ) (25827041103377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell756_denomLower :
    (2555919773209 / 1000000000 : ℝ) ≤ Real.exp (1961541856847143 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1961541856847143 / 250000000000000 : ℝ) (1277867575581 /
    1000000000000 : ℝ) (2555919773209 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell756_product_lower :
    (2020682481847143 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (189 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell756_leftExp
    (by norm_num : (0 : ℝ) ≤ (5145626757 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell756_product_upper :
    Real.pi * Real.exp (757 / 800 : ℝ) ≤ (80928422338122359 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell756_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell756_endpointLower :
    (1648084361 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (189 / 400 : ℝ) (757 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2020682481847143 / 250000000000000 : ℝ) (Real.pi * Real.exp (189 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell756_product_lower
  have hD : Real.exp (Real.pi * Real.exp (757 / 800 : ℝ) - (189 / 800 : ℝ)) ≤
      (25827041103377 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell756_denomUpper
    linarith [hpThetaJensenCell756_product_upper]
  have hi : (1 / (25827041103377 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (757 / 800 : ℝ) - (189 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (25827041103377 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (25827041103377 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((189 / 800 : ℝ) - Real.pi * Real.exp (757 / 800 : ℝ)) := by
    rw [show (189 / 800 : ℝ) - Real.pi * Real.exp (757 / 800 : ℝ) =
      -(Real.pi * Real.exp (757 / 800 : ℝ) - (189 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (189 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (189 / 200 : ℝ)) := by
    have h := hpThetaJensenCell756_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (25827041103377 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell756_endpointUpper :
    hpThetaJensenKernelEndpointUpper (189 / 400 : ℝ) (757 / 1600 : ℝ) ≤ (837199103 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (757 / 800 : ℝ)) (80928422338122359 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (757 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell756_product_upper
  have hD : (2555919773209 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (189 / 200 : ℝ) - (757 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell756_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell756_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (189 / 200 : ℝ) - (757 / 3200 : ℝ)) ≤
      (1 / (2555919773209 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2555919773209 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((757 / 3200 : ℝ) - Real.pi * Real.exp (189 / 200 : ℝ)) ≤
      (2 / (2555919773209 / 1000000000 : ℝ) : ℝ) := by
    rw [show (757 / 3200 : ℝ) - Real.pi * Real.exp (189 / 200 : ℝ) =
      -(Real.pi * Real.exp (189 / 200 : ℝ) - (757 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (80928422338122359 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (80928422338122359 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell756_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (189 / 400 : ℝ) (757 / 1600 : ℝ)) :
    (1648084361 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (837199103 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell756_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell756_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell757_leftExp :
    (25760314061 / 10000000000 : ℝ) ≤ Real.exp (757 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (757 / 800 : ℝ) (515005927817 / 500000000000 : ℝ)
    (25760314061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell757_rightExp :
    Real.exp (379 / 400 : ℝ) ≤ (25792534589 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (379 / 400 : ℝ) (1030052091259 / 1000000000000 : ℝ)
    (25792534589 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell757_denomUpper :
    Real.exp (78664021117060277 / 10000000000000000 : ℝ) ≤ (26081648012807 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (78664021117060277 / 10000000000000000 : ℝ) (1997931047 /
    1562500000 : ℝ) (26081648012807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell757_denomLower :
    (12905418869947 / 5000000000 : ℝ) ≤ Real.exp (9819955821440639 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9819955821440639 / 1250000000000000 : ℝ) (1278258871799
    / 1000000000000 : ℝ) (12905418869947 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell757_product_lower :
    (10116049571440639 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (757 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell757_leftExp
    (by norm_num : (0 : ℝ) ≤ (25760314061 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell757_product_upper :
    Real.pi * Real.exp (379 / 400 : ℝ) ≤ (81029646117060277 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell757_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell757_endpointLower :
    (327309343 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (757 / 1600 : ℝ) (379 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10116049571440639 / 1250000000000000 : ℝ) (Real.pi * Real.exp (757 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell757_product_lower
  have hD : Real.exp (Real.pi * Real.exp (379 / 400 : ℝ) - (757 / 3200 : ℝ)) ≤
      (26081648012807 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell757_denomUpper
    linarith [hpThetaJensenCell757_product_upper]
  have hi : (1 / (26081648012807 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (379 / 400 : ℝ) - (757 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26081648012807 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26081648012807 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((757 / 3200 : ℝ) - Real.pi * Real.exp (379 / 400 : ℝ)) := by
    rw [show (757 / 3200 : ℝ) - Real.pi * Real.exp (379 / 400 : ℝ) =
      -(Real.pi * Real.exp (379 / 400 : ℝ) - (757 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (757 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (757 / 800 : ℝ)) := by
    have h := hpThetaJensenCell757_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26081648012807 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell757_endpointUpper :
    hpThetaJensenKernelEndpointUpper (757 / 1600 : ℝ) (379 / 800 : ℝ) ≤ (33253933 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (379 / 400 : ℝ)) (81029646117060277 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (379 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell757_product_upper
  have hD : (12905418869947 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (757 / 800 : ℝ) - (379 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell757_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell757_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (757 / 800 : ℝ) - (379 / 1600 : ℝ)) ≤
      (1 / (12905418869947 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12905418869947 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((379 / 1600 : ℝ) - Real.pi * Real.exp (757 / 800 : ℝ)) ≤
      (2 / (12905418869947 / 5000000000 : ℝ) : ℝ) := by
    rw [show (379 / 1600 : ℝ) - Real.pi * Real.exp (757 / 800 : ℝ) =
      -(Real.pi * Real.exp (757 / 800 : ℝ) - (379 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (81029646117060277 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (81029646117060277 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell757_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (757 / 1600 : ℝ) (379 / 800 : ℝ)) :
    (327309343 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (33253933 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell757_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell757_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell758_leftExp :
    (25792534587 / 10000000000 : ℝ) ≤ Real.exp (379 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (379 / 400 : ℝ) (515026045629 / 500000000000 : ℝ)
    (25792534587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell758_rightExp :
    Real.exp (759 / 800 : ℝ) ≤ (3228099427 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (759 / 800 : ℝ) (206018465691 / 200000000000 : ℝ)
    (3228099427 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell758_denomUpper :
    Real.exp (9845280813167211 / 1250000000000000 : ℝ) ≤ (5267819670241 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9845280813167211 / 1250000000000000 : ℝ) (1279068425431
    / 1000000000000 : ℝ) (5267819670241 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell758_denomLower :
    (13032642414761 / 5000000000 : ℝ) ≤ Real.exp (9832218164780313 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9832218164780313 / 1250000000000000 : ℝ) (639325396549 /
    500000000000 : ℝ) (13032642414761 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell758_product_lower :
    (10128702539780313 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (379 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell758_leftExp
    (by norm_num : (0 : ℝ) ≤ (25792534587 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell758_product_upper :
    Real.pi * Real.exp (759 / 800 : ℝ) ≤ (10141374563167211 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell758_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell758_endpointLower :
    (325013711 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (379 / 800 : ℝ) (759 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10128702539780313 / 1250000000000000 : ℝ) (Real.pi * Real.exp (379 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell758_product_lower
  have hD : Real.exp (Real.pi * Real.exp (759 / 800 : ℝ) - (379 / 1600 : ℝ)) ≤
      (5267819670241 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell758_denomUpper
    linarith [hpThetaJensenCell758_product_upper]
  have hi : (1 / (5267819670241 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (759 / 800 : ℝ) - (379 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5267819670241 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5267819670241 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((379 / 1600 : ℝ) - Real.pi * Real.exp (759 / 800 : ℝ)) := by
    rw [show (379 / 1600 : ℝ) - Real.pi * Real.exp (759 / 800 : ℝ) =
      -(Real.pi * Real.exp (759 / 800 : ℝ) - (379 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (379 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (379 / 400 : ℝ)) := by
    have h := hpThetaJensenCell758_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5267819670241 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell758_endpointUpper :
    hpThetaJensenKernelEndpointUpper (379 / 800 : ℝ) (759 / 1600 : ℝ) ≤ (825527637 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (759 / 800 : ℝ)) (10141374563167211 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (759 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell758_product_upper
  have hD : (13032642414761 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (379 / 400 : ℝ) - (759 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell758_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell758_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (379 / 400 : ℝ) - (759 / 3200 : ℝ)) ≤
      (1 / (13032642414761 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13032642414761 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((759 / 3200 : ℝ) - Real.pi * Real.exp (379 / 400 : ℝ)) ≤
      (2 / (13032642414761 / 5000000000 : ℝ) : ℝ) := by
    rw [show (759 / 3200 : ℝ) - Real.pi * Real.exp (379 / 400 : ℝ) =
      -(Real.pi * Real.exp (379 / 400 : ℝ) - (759 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10141374563167211 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (10141374563167211 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell758_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (379 / 800 : ℝ) (759 / 1600 : ℝ)) :
    (325013711 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (825527637 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell758_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell758_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell759_leftExp :
    (12912397707 / 5000000000 : ℝ) ≤ Real.exp (759 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (759 / 800 : ℝ) (515046164227 / 500000000000 : ℝ)
    (12912397707 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell759_rightExp :
    Real.exp (19 / 20 : ℝ) ≤ (12928548297 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 20 : ℝ) (515066283611 / 500000000000 : ℝ)
    (12928548297 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell759_denomUpper :
    Real.exp (39430299330017121 / 5000000000000000 : ℝ) ≤ (13299713577523 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39430299330017121 / 5000000000000000 : ℝ) (1279461608149
    / 1000000000000 : ℝ) (13299713577523 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell759_denomLower :
    (1052902942511 / 400000000 : ℝ) ≤ Real.exp (4922248167141193 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4922248167141193 / 625000000000000 : ℝ) (1279043340621 /
    1000000000000 : ℝ) (1052902942511 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell759_product_lower :
    (5070685667141193 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (759 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell759_leftExp
    (by norm_num : (0 : ℝ) ≤ (12912397707 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell759_product_upper :
    Real.pi * Real.exp (19 / 20 : ℝ) ≤ (40616236830017121 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell759_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell759_endpointLower :
    (80682487 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (759 / 1600 : ℝ) (19 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5070685667141193 / 625000000000000 : ℝ) (Real.pi * Real.exp (759 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell759_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 20 : ℝ) - (759 / 3200 : ℝ)) ≤
      (13299713577523 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell759_denomUpper
    linarith [hpThetaJensenCell759_product_upper]
  have hi : (1 / (13299713577523 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 20 : ℝ) - (759 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13299713577523 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13299713577523 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((759 / 3200 : ℝ) - Real.pi * Real.exp (19 / 20 : ℝ)) := by
    rw [show (759 / 3200 : ℝ) - Real.pi * Real.exp (19 / 20 : ℝ) =
      -(Real.pi * Real.exp (19 / 20 : ℝ) - (759 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (759 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (759 / 800 : ℝ)) := by
    have h := hpThetaJensenCell759_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13299713577523 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell759_endpointUpper :
    hpThetaJensenKernelEndpointUpper (759 / 1600 : ℝ) (19 / 40 : ℝ) ≤ (819736967 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 20 : ℝ)) (40616236830017121 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell759_product_upper
  have hD : (1052902942511 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (759 / 800 : ℝ) - (19 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell759_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell759_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (759 / 800 : ℝ) - (19 / 80 : ℝ)) ≤
      (1 / (1052902942511 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1052902942511 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 80 : ℝ) - Real.pi * Real.exp (759 / 800 : ℝ)) ≤
      (2 / (1052902942511 / 400000000 : ℝ) : ℝ) := by
    rw [show (19 / 80 : ℝ) - Real.pi * Real.exp (759 / 800 : ℝ) =
      -(Real.pi * Real.exp (759 / 800 : ℝ) - (19 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40616236830017121 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (40616236830017121 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell759_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (759 / 1600 : ℝ) (19 / 40 : ℝ)) :
    (80682487 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (819736967 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell759_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell759_endpointUpper

def hpThetaJensenCellsBatch037Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1840889257 / 10000000000 : ℝ)
  | 1 => (914190627 / 5000000000 : ℝ)
  | 2 => (453983721 / 2500000000 : ℝ)
  | 3 => (901775011 / 5000000000 : ℝ)
  | 4 => (895613269 / 5000000000 : ℝ)
  | 5 => (111185269 / 625000000 : ℝ)
  | 6 => (1766763191 / 10000000000 : ℝ)
  | 7 => (877311533 / 5000000000 : ℝ)
  | 8 => (871271899 / 5000000000 : ℝ)
  | 9 => (1730525253 / 10000000000 : ℝ)
  | 10 => (17185673 / 100000000 : ℝ)
  | 11 => (853334901 / 5000000000 : ℝ)
  | 12 => (1694832623 / 10000000000 : ℝ)
  | 13 => (420763907 / 2500000000 : ℝ)
  | 14 => (835669339 / 5000000000 : ℝ)
  | 15 => (414920409 / 2500000000 : ℝ)
  | 16 => (1648084361 / 10000000000 : ℝ)
  | 17 => (327309343 / 2000000000 : ℝ)
  | 18 => (325013711 / 2000000000 : ℝ)
  | 19 => (80682487 / 500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch037Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (58435009 / 312500000 : ℝ)
  | 1 => (1857237223 / 10000000000 : ℝ)
  | 2 => (461154123 / 2500000000 : ℝ)
  | 3 => (114503623 / 625000000 : ℝ)
  | 4 => (909780761 / 5000000000 : ℝ)
  | 5 => (903563513 / 5000000000 : ℝ)
  | 6 => (448688587 / 2500000000 : ℝ)
  | 7 => (1782443357 / 10000000000 : ℝ)
  | 8 => (1770193921 / 10000000000 : ℝ)
  | 9 => (879002953 / 5000000000 : ℝ)
  | 10 => (872939589 / 5000000000 : ℝ)
  | 11 => (1733813603 / 10000000000 : ℝ)
  | 12 => (1721809043 / 10000000000 : ℝ)
  | 13 => (854932681 / 5000000000 : ℝ)
  | 14 => (848991211 / 5000000000 : ℝ)
  | 15 => (1686160083 / 10000000000 : ℝ)
  | 16 => (837199103 / 5000000000 : ℝ)
  | 17 => (33253933 / 200000000 : ℝ)
  | 18 => (825527637 / 5000000000 : ℝ)
  | 19 => (819736967 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch037_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch037Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch037Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell740_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell741_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell742_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell743_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell744_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell745_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell746_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell747_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell748_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell749_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell750_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell751_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell752_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell753_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell754_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell755_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell756_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell757_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell758_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell759_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper] at h ⊢
    exact h

end HodgeProofHP
