import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1240_leftExp :
    (46010451 / 9765625 : ℝ) ≤ Real.exp (31 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 20 : ℝ) (1049629767909 / 1000000000000 : ℝ)
    (46010451 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1240_rightExp :
    Real.exp (1241 / 800 : ℝ) ≤ (11793408007 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1241 / 800 : ℝ) (524835384937 / 500000000000 : ℝ)
    (11793408007 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1240_denomUpper :
    Real.exp (36081338040935151 / 2500000000000000 : ℝ) ≤ (18534053160205467 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (36081338040935151 / 2500000000000000 : ℝ) (1569907539381
    / 1000000000000 : ℝ) (18534053160205467 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1240_denomLower :
    (18188309786608539 / 10000000000 : ℝ) ≤ Real.exp (281517666665359 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (281517666665359 / 19531250000000 : ℝ) (1568983985163 /
    1000000000000 : ℝ) (18188309786608539 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1240_product_lower :
    (18068258097249 / 1220703125000 : ℝ) ≤ Real.pi * Real.exp (31 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1240_leftExp
    (by norm_num : (0 : ℝ) ≤ (46010451 / 9765625 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1240_product_upper :
    Real.pi * Real.exp (1241 / 800 : ℝ) ≤ (37050088040935151 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1240_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1240_endpointLower :
    (42491 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 40 : ℝ) (1241 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18068258097249 / 1220703125000 : ℝ) (Real.pi * Real.exp (31 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell1240_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1241 / 800 : ℝ) - (31 / 80 : ℝ)) ≤
      (18534053160205467 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1240_denomUpper
    linarith [hpThetaJensenCell1240_product_upper]
  have hi : (1 / (18534053160205467 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1241 / 800 : ℝ) - (31 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18534053160205467 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18534053160205467 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 80 : ℝ) - Real.pi * Real.exp (1241 / 800 : ℝ)) := by
    rw [show (31 / 80 : ℝ) - Real.pi * Real.exp (1241 / 800 : ℝ) =
      -(Real.pi * Real.exp (1241 / 800 : ℝ) - (31 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 20 : ℝ)) := by
    have h := hpThetaJensenCell1240_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18534053160205467 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1240_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 40 : ℝ) (1241 / 1600 : ℝ) ≤ (2176379 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1241 / 800 : ℝ)) (37050088040935151 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1241 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1240_product_upper
  have hD : (18188309786608539 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 20 : ℝ) - (1241 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1240_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1240_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 20 : ℝ) - (1241 / 3200 : ℝ)) ≤
      (1 / (18188309786608539 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18188309786608539 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1241 / 3200 : ℝ) - Real.pi * Real.exp (31 / 20 : ℝ)) ≤
      (2 / (18188309786608539 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1241 / 3200 : ℝ) - Real.pi * Real.exp (31 / 20 : ℝ) =
      -(Real.pi * Real.exp (31 / 20 : ℝ) - (1241 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37050088040935151 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (37050088040935151 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1240_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 40 : ℝ) (1241 / 1600 : ℝ)) :
    (42491 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2176379 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1240_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1240_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1241_leftExp :
    (23586816013 / 5000000000 : ℝ) ≤ Real.exp (1241 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1241 / 800 : ℝ) (1049670769873 / 1000000000000 : ℝ)
    (23586816013 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1241_rightExp :
    Real.exp (621 / 400 : ℝ) ≤ (23616317969 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (621 / 400 : ℝ) (1049711773439 / 1000000000000 : ℝ)
    (23616317969 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1241_denomUpper :
    Real.exp (72253796717184617 / 5000000000000000 : ℝ) ≤ (1179682289723241 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (72253796717184617 / 5000000000000000 : ℝ) (785400931297
    / 500000000000 : ℝ) (1179682289723241 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1241_denomLower :
    (18522385606921591 / 10000000000 : ℝ) ≤ Real.exp (9019940936489087 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9019940936489087 / 625000000000000 : ℝ) (392469161491 /
    250000000000 : ℝ) (18522385606921591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1241_product_lower :
    (9262519061489087 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1241 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1241_leftExp
    (by norm_num : (0 : ℝ) ≤ (23586816013 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1241_product_upper :
    Real.pi * Real.exp (621 / 400 : ℝ) ≤ (74192859217184617 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1241_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1241_endpointLower :
    (8366797 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1241 / 1600 : ℝ) (621 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9262519061489087 / 625000000000000 : ℝ) (Real.pi * Real.exp (1241 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1241_product_lower
  have hD : Real.exp (Real.pi * Real.exp (621 / 400 : ℝ) - (1241 / 3200 : ℝ)) ≤
      (1179682289723241 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1241_denomUpper
    linarith [hpThetaJensenCell1241_product_upper]
  have hi : (1 / (1179682289723241 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (621 / 400 : ℝ) - (1241 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1179682289723241 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1179682289723241 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1241 / 3200 : ℝ) - Real.pi * Real.exp (621 / 400 : ℝ)) := by
    rw [show (1241 / 3200 : ℝ) - Real.pi * Real.exp (621 / 400 : ℝ) =
      -(Real.pi * Real.exp (621 / 400 : ℝ) - (1241 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1241 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1241 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1241_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1179682289723241 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1241_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1241 / 1600 : ℝ) (621 / 800 : ℝ) ≤ (267847 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (621 / 400 : ℝ)) (74192859217184617 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (621 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1241_product_upper
  have hD : (18522385606921591 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1241 / 800 : ℝ) - (621 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1241_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1241_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1241 / 800 : ℝ) - (621 / 1600 : ℝ)) ≤
      (1 / (18522385606921591 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18522385606921591 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((621 / 1600 : ℝ) - Real.pi * Real.exp (1241 / 800 : ℝ)) ≤
      (2 / (18522385606921591 / 10000000000 : ℝ) : ℝ) := by
    rw [show (621 / 1600 : ℝ) - Real.pi * Real.exp (1241 / 800 : ℝ) =
      -(Real.pi * Real.exp (1241 / 800 : ℝ) - (621 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (74192859217184617 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (74192859217184617 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1241_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1241 / 1600 : ℝ) (621 / 800 : ℝ)) :
    (8366797 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (267847 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1241_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1241_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1242_leftExp :
    (9446527187 / 2000000000 : ℝ) ≤ Real.exp (621 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (621 / 400 : ℝ) (524855886719 / 500000000000 : ℝ)
    (9446527187 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1242_rightExp :
    Real.exp (1243 / 800 : ℝ) ≤ (2955732103 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1243 / 800 : ℝ) (524876389303 / 500000000000 : ℝ)
    (2955732103 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1242_denomUpper :
    Real.exp (9043129159660079 / 625000000000000 : ℝ) ≤ (19222494667029389 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (9043129159660079 / 625000000000000 : ℝ) (314339566803 /
    200000000000 : ℝ) (19222494667029389 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1242_denomLower :
    (9431517192568727 / 5000000000 : ℝ) ≤ Real.exp (3612532404807713 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3612532404807713 / 250000000000000 : ℝ) (785385475637 /
    500000000000 : ℝ) (9431517192568727 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1242_product_lower :
    (3709641779807713 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (621 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1242_leftExp
    (by norm_num : (0 : ℝ) ≤ (9446527187 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1242_product_upper :
    Real.pi * Real.exp (1243 / 800 : ℝ) ≤ (9285707284660079 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1242_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1242_endpointLower :
    (8237233 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (621 / 800 : ℝ) (1243 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3709641779807713 / 250000000000000 : ℝ) (Real.pi * Real.exp (621 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1242_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1243 / 800 : ℝ) - (621 / 1600 : ℝ)) ≤
      (19222494667029389 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1242_denomUpper
    linarith [hpThetaJensenCell1242_product_upper]
  have hi : (1 / (19222494667029389 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1243 / 800 : ℝ) - (621 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19222494667029389 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19222494667029389 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((621 / 1600 : ℝ) - Real.pi * Real.exp (1243 / 800 : ℝ)) := by
    rw [show (621 / 1600 : ℝ) - Real.pi * Real.exp (1243 / 800 : ℝ) =
      -(Real.pi * Real.exp (1243 / 800 : ℝ) - (621 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (621 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (621 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1242_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19222494667029389 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1242_endpointUpper :
    hpThetaJensenKernelEndpointUpper (621 / 800 : ℝ) (1243 / 1600 : ℝ) ≤ (843857 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1243 / 800 : ℝ)) (9285707284660079 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1243 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1242_product_upper
  have hD : (9431517192568727 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (621 / 400 : ℝ) - (1243 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1242_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1242_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (621 / 400 : ℝ) - (1243 / 3200 : ℝ)) ≤
      (1 / (9431517192568727 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9431517192568727 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1243 / 3200 : ℝ) - Real.pi * Real.exp (621 / 400 : ℝ)) ≤
      (2 / (9431517192568727 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1243 / 3200 : ℝ) - Real.pi * Real.exp (621 / 400 : ℝ) =
      -(Real.pi * Real.exp (621 / 400 : ℝ) - (1243 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9285707284660079 / 625000000000000 : ℝ) ^ 2 - 6 *
      (9285707284660079 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1242_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (621 / 800 : ℝ) (1243 / 1600 : ℝ)) :
    (8237233 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (843857 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1242_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1242_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1243_leftExp :
    (23645856823 / 5000000000 : ℝ) ≤ Real.exp (1243 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1243 / 800 : ℝ) (209950555721 / 200000000000 : ℝ)
    (23645856823 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1243_rightExp :
    Real.exp (311 / 200 : ℝ) ≤ (47350865253 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (311 / 200 : ℝ) (8398350283 / 8000000000 : ℝ)
    (47350865253 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1243_denomUpper :
    Real.exp (144872771822768029 / 10000000000000000 : ℝ) ≤ (9788463875847323 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (144872771822768029 / 10000000000000000 : ℝ)
    (1572595457349 / 1000000000000 : ℝ) (9788463875847323 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1243_denomLower :
    (19210393499452377 / 10000000000 : ℝ) ≤ Real.exp (9042735578535277 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9042735578535277 / 625000000000000 : ℝ) (392916726197 /
    250000000000 : ℝ) (19210393499452377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1243_product_lower :
    (9285704328535277 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1243 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1243_leftExp
    (by norm_num : (0 : ℝ) ≤ (23645856823 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1243_product_upper :
    Real.pi * Real.exp (311 / 200 : ℝ) ≤ (148757146822768029 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1243_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1243_endpointLower :
    (4054743 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1243 / 1600 : ℝ) (311 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9285704328535277 / 625000000000000 : ℝ) (Real.pi * Real.exp (1243 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1243_product_lower
  have hD : Real.exp (Real.pi * Real.exp (311 / 200 : ℝ) - (1243 / 3200 : ℝ)) ≤
      (9788463875847323 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1243_denomUpper
    linarith [hpThetaJensenCell1243_product_upper]
  have hi : (1 / (9788463875847323 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (311 / 200 : ℝ) - (1243 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9788463875847323 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9788463875847323 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1243 / 3200 : ℝ) - Real.pi * Real.exp (311 / 200 : ℝ)) := by
    rw [show (1243 / 3200 : ℝ) - Real.pi * Real.exp (311 / 200 : ℝ) =
      -(Real.pi * Real.exp (311 / 200 : ℝ) - (1243 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1243 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1243 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1243_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9788463875847323 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1243_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1243 / 1600 : ℝ) (311 / 400 : ℝ) ≤ (8307891 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (311 / 200 : ℝ)) (148757146822768029 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (311 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1243_product_upper
  have hD : (19210393499452377 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1243 / 800 : ℝ) - (311 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1243_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1243_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1243 / 800 : ℝ) - (311 / 800 : ℝ)) ≤
      (1 / (19210393499452377 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19210393499452377 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((311 / 800 : ℝ) - Real.pi * Real.exp (1243 / 800 : ℝ)) ≤
      (2 / (19210393499452377 / 10000000000 : ℝ) : ℝ) := by
    rw [show (311 / 800 : ℝ) - Real.pi * Real.exp (1243 / 800 : ℝ) =
      -(Real.pi * Real.exp (1243 / 800 : ℝ) - (311 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (148757146822768029 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (148757146822768029 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1243_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1243 / 1600 : ℝ) (311 / 400 : ℝ)) :
    (4054743 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8307891 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1243_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1243_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1244_leftExp :
    (189403461 / 40000000 : ℝ) ≤ Real.exp (311 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (311 / 200 : ℝ) (524896892687 / 500000000000 : ℝ)
    (189403461 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1244_rightExp :
    Real.exp (249 / 160 : ℝ) ≤ (47410090843 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (249 / 160 : ℝ) (524917396873 / 500000000000 : ℝ)
    (47410090843 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1244_denomUpper :
    Real.exp (145055709521732899 / 10000000000000000 : ℝ) ≤ (9969179728896247 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (145055709521732899 / 10000000000000000 : ℝ)
    (196686842029 / 125000000000 : ℝ) (9969179728896247 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1244_denomLower :
    (19564603335553389 / 10000000000 : ℝ) ≤ Real.exp (72433237231239 / 5000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (72433237231239 / 5000000000000 : ℝ) (196570563769 /
    125000000000 : ℝ) (19564603335553389 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1244_product_lower :
    (74378549731239 / 5000000000000 : ℝ) ≤ Real.pi * Real.exp (311 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1244_leftExp
    (by norm_num : (0 : ℝ) ≤ (189403461 / 40000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1244_product_upper :
    Real.pi * Real.exp (249 / 160 : ℝ) ≤ (148943209521732899 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1244_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1244_endpointLower :
    (1995883 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (311 / 400 : ℝ) (249 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (74378549731239 / 5000000000000 : ℝ) (Real.pi * Real.exp (311 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1244_product_lower
  have hD : Real.exp (Real.pi * Real.exp (249 / 160 : ℝ) - (311 / 800 : ℝ)) ≤
      (9969179728896247 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1244_denomUpper
    linarith [hpThetaJensenCell1244_product_upper]
  have hi : (1 / (9969179728896247 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (249 / 160 : ℝ) - (311 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9969179728896247 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9969179728896247 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((311 / 800 : ℝ) - Real.pi * Real.exp (249 / 160 : ℝ)) := by
    rw [show (311 / 800 : ℝ) - Real.pi * Real.exp (249 / 160 : ℝ) =
      -(Real.pi * Real.exp (249 / 160 : ℝ) - (311 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (311 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (311 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1244_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9969179728896247 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1244_endpointUpper :
    hpThetaJensenKernelEndpointUpper (311 / 400 : ℝ) (249 / 320 : ℝ) ≤ (1635809 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (249 / 160 : ℝ)) (148943209521732899 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (249 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1244_product_upper
  have hD : (19564603335553389 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (311 / 200 : ℝ) - (249 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1244_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1244_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (311 / 200 : ℝ) - (249 / 640 : ℝ)) ≤
      (1 / (19564603335553389 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19564603335553389 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((249 / 640 : ℝ) - Real.pi * Real.exp (311 / 200 : ℝ)) ≤
      (2 / (19564603335553389 / 10000000000 : ℝ) : ℝ) := by
    rw [show (249 / 640 : ℝ) - Real.pi * Real.exp (311 / 200 : ℝ) =
      -(Real.pi * Real.exp (311 / 200 : ℝ) - (249 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (148943209521732899 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (148943209521732899 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1244_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (311 / 400 : ℝ) (249 / 320 : ℝ)) :
    (1995883 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1635809 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1244_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1244_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1245_leftExp :
    (47410090841 / 10000000000 : ℝ) ≤ Real.exp (249 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (249 / 160 : ℝ) (209966958749 / 200000000000 : ℝ)
    (47410090841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1245_rightExp :
    Real.exp (623 / 400 : ℝ) ≤ (4746939051 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (623 / 400 : ℝ) (524937901859 / 500000000000 : ℝ)
    (4746939051 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1245_denomUpper :
    Real.exp (14523887994048243 / 1000000000000000 : ℝ) ≤ (20306936538753847 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (14523887994048243 / 1000000000000000 : ℝ) (78719783717 /
    50000000000 : ℝ) (20306936538753847 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1245_denomLower :
    (19925807394866867 / 10000000000 : ℝ) ≤ Real.exp (18131176513169859 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18131176513169859 / 1250000000000000 : ℝ) (786731885531
    / 500000000000 : ℝ) (19925807394866867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1245_product_lower :
    (18617895263169859 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (249 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1245_leftExp
    (by norm_num : (0 : ℝ) ≤ (47410090841 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1245_product_upper :
    Real.pi * Real.exp (623 / 400 : ℝ) ≤ (14912950494048243 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1245_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1245_endpointLower :
    (7859351 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (249 / 320 : ℝ) (623 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18617895263169859 / 1250000000000000 : ℝ) (Real.pi * Real.exp (249 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1245_product_lower
  have hD : Real.exp (Real.pi * Real.exp (623 / 400 : ℝ) - (249 / 640 : ℝ)) ≤
      (20306936538753847 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1245_denomUpper
    linarith [hpThetaJensenCell1245_product_upper]
  have hi : (1 / (20306936538753847 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (623 / 400 : ℝ) - (249 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (20306936538753847 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (20306936538753847 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((249 / 640 : ℝ) - Real.pi * Real.exp (623 / 400 : ℝ)) := by
    rw [show (249 / 640 : ℝ) - Real.pi * Real.exp (623 / 400 : ℝ) =
      -(Real.pi * Real.exp (623 / 400 : ℝ) - (249 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (249 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (249 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1245_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (20306936538753847 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1245_endpointUpper :
    hpThetaJensenKernelEndpointUpper (249 / 320 : ℝ) (623 / 800 : ℝ) ≤ (1006501 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (623 / 400 : ℝ)) (14912950494048243 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (623 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1245_product_upper
  have hD : (19925807394866867 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (249 / 160 : ℝ) - (623 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1245_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1245_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (249 / 160 : ℝ) - (623 / 1600 : ℝ)) ≤
      (1 / (19925807394866867 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19925807394866867 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((623 / 1600 : ℝ) - Real.pi * Real.exp (249 / 160 : ℝ)) ≤
      (2 / (19925807394866867 / 10000000000 : ℝ) : ℝ) := by
    rw [show (623 / 1600 : ℝ) - Real.pi * Real.exp (249 / 160 : ℝ) =
      -(Real.pi * Real.exp (249 / 160 : ℝ) - (623 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14912950494048243 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (14912950494048243 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1245_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (249 / 320 : ℝ) (623 / 800 : ℝ)) :
    (7859351 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1006501 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1245_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1245_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1246_leftExp :
    (11867347627 / 2500000000 : ℝ) ≤ Real.exp (623 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (623 / 400 : ℝ) (1049875803717 / 1000000000000 : ℝ)
    (11867347627 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1246_rightExp :
    Real.exp (1247 / 800 : ℝ) ≤ (950575287 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1247 / 800 : ℝ) (1049916815293 / 1000000000000 : ℝ)
    (950575287 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1246_denomUpper :
    Real.exp (2908445667612191 / 200000000000000 : ℝ) ≤ (20682809020121249 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (2908445667612191 / 200000000000000 : ℝ) (787649137709 /
    500000000000 : ℝ) (20682809020121249 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1246_denomLower :
    (2029415232001151 / 1000000000 : ℝ) ≤ Real.exp (4538518202025273 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4538518202025273 / 312500000000000 : ℝ) (393591172787 /
    250000000000 : ℝ) (2029415232001151 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1246_product_lower :
    (4660295545775273 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (623 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1246_leftExp
    (by norm_num : (0 : ℝ) ≤ (11867347627 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1246_product_upper :
    Real.pi * Real.exp (1247 / 800 : ℝ) ≤ (2986320667612191 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1246_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1246_endpointLower :
    (7736919 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (623 / 800 : ℝ) (1247 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4660295545775273 / 312500000000000 : ℝ) (Real.pi * Real.exp (623 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1246_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1247 / 800 : ℝ) - (623 / 1600 : ℝ)) ≤
      (20682809020121249 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1246_denomUpper
    linarith [hpThetaJensenCell1246_product_upper]
  have hi : (1 / (20682809020121249 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1247 / 800 : ℝ) - (623 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (20682809020121249 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (20682809020121249 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((623 / 1600 : ℝ) - Real.pi * Real.exp (1247 / 800 : ℝ)) := by
    rw [show (623 / 1600 : ℝ) - Real.pi * Real.exp (1247 / 800 : ℝ) =
      -(Real.pi * Real.exp (1247 / 800 : ℝ) - (623 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (623 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (623 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1246_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (20682809020121249 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1246_endpointUpper :
    hpThetaJensenKernelEndpointUpper (623 / 800 : ℝ) (1247 / 1600 : ℝ) ≤ (3963379 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1247 / 800 : ℝ)) (2986320667612191 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1247 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1246_product_upper
  have hD : (2029415232001151 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (623 / 400 : ℝ) - (1247 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1246_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1246_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (623 / 400 : ℝ) - (1247 / 3200 : ℝ)) ≤
      (1 / (2029415232001151 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2029415232001151 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1247 / 3200 : ℝ) - Real.pi * Real.exp (623 / 400 : ℝ)) ≤
      (2 / (2029415232001151 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1247 / 3200 : ℝ) - Real.pi * Real.exp (623 / 400 : ℝ) =
      -(Real.pi * Real.exp (623 / 400 : ℝ) - (1247 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2986320667612191 / 200000000000000 : ℝ) ^ 2 - 6 *
      (2986320667612191 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1246_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (623 / 800 : ℝ) (1247 / 1600 : ℝ)) :
    (7736919 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3963379 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1246_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1246_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1247_leftExp :
    (11882191087 / 2500000000 : ℝ) ≤ Real.exp (1247 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1247 / 800 : ℝ) (262479203823 / 250000000000 : ℝ)
    (11882191087 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1247_rightExp :
    Real.exp (39 / 25 : ℝ) ≤ (11897053113 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 25 : ℝ) (1049957828469 / 1000000000000 : ℝ)
    (11897053113 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1247_denomUpper :
    Real.exp (36401480030429009 / 2500000000000000 : ℝ) ≤ (21066130204934503 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (36401480030429009 / 2500000000000000 : ℝ) (1576202543111
    / 1000000000000 : ℝ) (21066130204934503 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1247_denomLower :
    (20669788048354179 / 10000000000 : ℝ) ≤ Real.exp (4544249557673813 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4544249557673813 / 312500000000000 : ℝ) (1575267274171 /
    1000000000000 : ℝ) (20669788048354179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1247_product_lower :
    (4666124557673813 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1247 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1247_leftExp
    (by norm_num : (0 : ℝ) ≤ (11882191087 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1247_product_upper :
    Real.pi * Real.exp (39 / 25 : ℝ) ≤ (37375698780429009 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1247_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1247_endpointLower :
    (1523243 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1247 / 1600 : ℝ) (39 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4666124557673813 / 312500000000000 : ℝ) (Real.pi * Real.exp (1247 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1247_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 25 : ℝ) - (1247 / 3200 : ℝ)) ≤
      (21066130204934503 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1247_denomUpper
    linarith [hpThetaJensenCell1247_product_upper]
  have hi : (1 / (21066130204934503 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 25 : ℝ) - (1247 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (21066130204934503 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (21066130204934503 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1247 / 3200 : ℝ) - Real.pi * Real.exp (39 / 25 : ℝ)) := by
    rw [show (1247 / 3200 : ℝ) - Real.pi * Real.exp (39 / 25 : ℝ) =
      -(Real.pi * Real.exp (39 / 25 : ℝ) - (1247 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1247 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1247 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1247_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (21066130204934503 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1247_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1247 / 1600 : ℝ) (39 / 50 : ℝ) ≤ (3901637 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 25 : ℝ)) (37375698780429009 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1247_product_upper
  have hD : (20669788048354179 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1247 / 800 : ℝ) - (39 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell1247_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1247_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1247 / 800 : ℝ) - (39 / 100 : ℝ)) ≤
      (1 / (20669788048354179 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20669788048354179 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 100 : ℝ) - Real.pi * Real.exp (1247 / 800 : ℝ)) ≤
      (2 / (20669788048354179 / 10000000000 : ℝ) : ℝ) := by
    rw [show (39 / 100 : ℝ) - Real.pi * Real.exp (1247 / 800 : ℝ) =
      -(Real.pi * Real.exp (1247 / 800 : ℝ) - (39 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37375698780429009 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (37375698780429009 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1247_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1247 / 1600 : ℝ) (39 / 50 : ℝ)) :
    (1523243 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3901637 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1247_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1247_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1248_leftExp :
    (47588212449 / 10000000000 : ℝ) ≤ Real.exp (39 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 25 : ℝ) (262489457117 / 250000000000 : ℝ)
    (47588212449 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1248_rightExp :
    Real.exp (1249 / 800 : ℝ) ≤ (372247929 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1249 / 800 : ℝ) (65624927703 / 62500000000 : ℝ)
    (372247929 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1248_denomUpper :
    Real.exp (1138982738010897 / 78125000000000 : ℝ) ≤ (2145705684220653 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1138982738010897 / 78125000000000 : ℝ) (1577108481183 /
    1000000000000 : ℝ) (2145705684220653 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1248_denomLower :
    (10526433889956103 / 5000000000 : ℝ) ≤ Real.exp (18199952815509851 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18199952815509851 / 1250000000000000 : ℝ) (1576171523761
    / 1000000000000 : ℝ) (10526433889956103 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1248_product_lower :
    (18687843440509851 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1248_leftExp
    (by norm_num : (0 : ℝ) ≤ (47588212449 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1248_product_upper :
    Real.pi * Real.exp (1249 / 800 : ℝ) ≤ (1169451488010897 / 78125000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1248_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1248_endpointLower :
    (3748609 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 50 : ℝ) (1249 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18687843440509851 / 1250000000000000 : ℝ) (Real.pi * Real.exp (39 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1248_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1249 / 800 : ℝ) - (39 / 100 : ℝ)) ≤
      (2145705684220653 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1248_denomUpper
    linarith [hpThetaJensenCell1248_product_upper]
  have hi : (1 / (2145705684220653 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1249 / 800 : ℝ) - (39 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2145705684220653 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2145705684220653 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 100 : ℝ) - Real.pi * Real.exp (1249 / 800 : ℝ)) := by
    rw [show (39 / 100 : ℝ) - Real.pi * Real.exp (1249 / 800 : ℝ) =
      -(Real.pi * Real.exp (1249 / 800 : ℝ) - (39 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1248_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2145705684220653 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1248_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 50 : ℝ) (1249 / 1600 : ℝ) ≤ (1920383 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1249 / 800 : ℝ)) (1169451488010897 / 78125000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1249 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1248_product_upper
  have hD : (10526433889956103 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 25 : ℝ) - (1249 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1248_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1248_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 25 : ℝ) - (1249 / 3200 : ℝ)) ≤
      (1 / (10526433889956103 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10526433889956103 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1249 / 3200 : ℝ) - Real.pi * Real.exp (39 / 25 : ℝ)) ≤
      (2 / (10526433889956103 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1249 / 3200 : ℝ) - Real.pi * Real.exp (39 / 25 : ℝ) =
      -(Real.pi * Real.exp (39 / 25 : ℝ) - (1249 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1169451488010897 / 78125000000000 : ℝ) ^ 2 - 6 *
      (1169451488010897 / 78125000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1248_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 50 : ℝ) (1249 / 1600 : ℝ)) :
    (3748609 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1920383 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1248_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1248_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1249_leftExp :
    (47647734909 / 10000000000 : ℝ) ≤ Real.exp (1249 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1249 / 800 : ℝ) (1049998843247 / 1000000000000 : ℝ)
    (47647734909 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1249_rightExp :
    Real.exp (25 / 16 : ℝ) ≤ (47707331821 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25 / 16 : ℝ) (1050039859629 / 1000000000000 : ℝ)
    (47707331821 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1249_denomUpper :
    Real.exp (145973894697530853 / 10000000000000000 : ℝ) ≤ (21855749125174129 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (145973894697530853 / 10000000000000000 : ℝ) (63120643733
    / 40000000000 : ℝ) (21855749125174129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1249_denomLower :
    (5360887044297483 / 2500000000 : ℝ) ≤ Real.exp (18222936601029391 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18222936601029391 / 1250000000000000 : ℝ) (1577077443711
    / 1000000000000 : ℝ) (5360887044297483 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1249_product_lower :
    (18711217851029391 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1249 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1249_leftExp
    (by norm_num : (0 : ℝ) ≤ (47647734909 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1249_product_upper :
    Real.pi * Real.exp (25 / 16 : ℝ) ≤ (149877019697530853 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1249_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1249_endpointLower :
    (3689953 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1249 / 1600 : ℝ) (25 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18711217851029391 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1249 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1249_product_lower
  have hD : Real.exp (Real.pi * Real.exp (25 / 16 : ℝ) - (1249 / 3200 : ℝ)) ≤
      (21855749125174129 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1249_denomUpper
    linarith [hpThetaJensenCell1249_product_upper]
  have hi : (1 / (21855749125174129 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (25 / 16 : ℝ) - (1249 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (21855749125174129 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (21855749125174129 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1249 / 3200 : ℝ) - Real.pi * Real.exp (25 / 16 : ℝ)) := by
    rw [show (1249 / 3200 : ℝ) - Real.pi * Real.exp (25 / 16 : ℝ) =
      -(Real.pi * Real.exp (25 / 16 : ℝ) - (1249 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1249 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1249 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1249_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (21855749125174129 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1249_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1249 / 1600 : ℝ) (25 / 32 : ℝ) ≤ (7561511 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (25 / 16 : ℝ)) (149877019697530853 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (25 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1249_product_upper
  have hD : (5360887044297483 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1249 / 800 : ℝ) - (25 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell1249_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1249_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1249 / 800 : ℝ) - (25 / 64 : ℝ)) ≤
      (1 / (5360887044297483 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5360887044297483 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((25 / 64 : ℝ) - Real.pi * Real.exp (1249 / 800 : ℝ)) ≤
      (2 / (5360887044297483 / 2500000000 : ℝ) : ℝ) := by
    rw [show (25 / 64 : ℝ) - Real.pi * Real.exp (1249 / 800 : ℝ) =
      -(Real.pi * Real.exp (1249 / 800 : ℝ) - (25 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (149877019697530853 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (149877019697530853 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1249_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1249 / 1600 : ℝ) (25 / 32 : ℝ)) :
    (3689953 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7561511 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1249_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1249_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1250_leftExp :
    (23853665909 / 5000000000 : ℝ) ≤ Real.exp (25 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (25 / 16 : ℝ) (262509964907 / 250000000000 : ℝ)
    (23853665909 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1250_rightExp :
    Real.exp (1251 / 800 : ℝ) ≤ (5970875409 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1251 / 800 : ℝ) (262520219403 / 250000000000 : ℝ)
    (5970875409 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1250_denomUpper :
    Real.exp (18269779138786537 / 1250000000000000 : ℝ) ≤ (22262370821034777 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (18269779138786537 / 1250000000000000 : ℝ) (157892538327
    / 100000000000 : ℝ) (22262370821034777 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1250_denomLower :
    (10920994663075557 / 5000000000 : ℝ) ≤ Real.exp (9122974811298391 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9122974811298391 / 625000000000000 : ℝ) (1577985037697 /
    1000000000000 : ℝ) (10920994663075557 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1250_product_lower :
    (9367310748798391 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (25 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1250_leftExp
    (by norm_num : (0 : ℝ) ≤ (23853665909 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1250_product_upper :
    Real.pi * Real.exp (1251 / 800 : ℝ) ≤ (18758060388786537 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1250_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1250_endpointLower :
    (3632129 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (25 / 32 : ℝ) (1251 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9367310748798391 / 625000000000000 : ℝ) (Real.pi * Real.exp (25 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell1250_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1251 / 800 : ℝ) - (25 / 64 : ℝ)) ≤
      (22262370821034777 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1250_denomUpper
    linarith [hpThetaJensenCell1250_product_upper]
  have hi : (1 / (22262370821034777 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1251 / 800 : ℝ) - (25 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22262370821034777 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22262370821034777 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((25 / 64 : ℝ) - Real.pi * Real.exp (1251 / 800 : ℝ)) := by
    rw [show (25 / 64 : ℝ) - Real.pi * Real.exp (1251 / 800 : ℝ) =
      -(Real.pi * Real.exp (1251 / 800 : ℝ) - (25 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (25 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (25 / 16 : ℝ)) := by
    have h := hpThetaJensenCell1250_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22262370821034777 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1250_endpointUpper :
    hpThetaJensenKernelEndpointUpper (25 / 32 : ℝ) (1251 / 1600 : ℝ) ≤ (744319 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1251 / 800 : ℝ)) (18758060388786537 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1251 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1250_product_upper
  have hD : (10920994663075557 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (25 / 16 : ℝ) - (1251 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1250_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1250_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (25 / 16 : ℝ) - (1251 / 3200 : ℝ)) ≤
      (1 / (10920994663075557 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10920994663075557 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1251 / 3200 : ℝ) - Real.pi * Real.exp (25 / 16 : ℝ)) ≤
      (2 / (10920994663075557 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1251 / 3200 : ℝ) - Real.pi * Real.exp (25 / 16 : ℝ) =
      -(Real.pi * Real.exp (25 / 16 : ℝ) - (1251 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18758060388786537 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (18758060388786537 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1250_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (25 / 32 : ℝ) (1251 / 1600 : ℝ)) :
    (3632129 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (744319 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1250_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1250_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1251_leftExp :
    (4776700327 / 1000000000 : ℝ) ≤ Real.exp (1251 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1251 / 800 : ℝ) (1050080877611 / 1000000000000 : ℝ)
    (4776700327 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1251_rightExp :
    Real.exp (313 / 200 : ℝ) ≤ (47826749361 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (313 / 200 : ℝ) (525060948599 / 500000000000 : ℝ)
    (47826749361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1251_denomUpper :
    Real.exp (146342806005272073 / 10000000000000000 : ℝ) ≤ (226770893607753 / 100000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (146342806005272073 / 10000000000000000 : ℝ)
    (315967270961 / 200000000000 : ℝ) (226770893607753 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1251_denomLower :
    (1390522181123827 / 625000000 : ℝ) ≤ Real.exp (1826899191712573 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1826899191712573 / 125000000000000 : ℝ) (394723577367 /
    250000000000 : ℝ) (1390522181123827 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1251_product_lower :
    (1875805441712573 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1251 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1251_leftExp
    (by norm_num : (0 : ℝ) ≤ (4776700327 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1251_product_upper :
    Real.pi * Real.exp (313 / 200 : ℝ) ≤ (150252181005272073 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1251_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1251_endpointLower :
    (7150253 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1251 / 1600 : ℝ) (313 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1875805441712573 / 125000000000000 : ℝ) (Real.pi * Real.exp (1251 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1251_product_lower
  have hD : Real.exp (Real.pi * Real.exp (313 / 200 : ℝ) - (1251 / 3200 : ℝ)) ≤
      (226770893607753 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1251_denomUpper
    linarith [hpThetaJensenCell1251_product_upper]
  have hi : (1 / (226770893607753 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (313 / 200 : ℝ) - (1251 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (226770893607753 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (226770893607753 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1251 / 3200 : ℝ) - Real.pi * Real.exp (313 / 200 : ℝ)) := by
    rw [show (1251 / 3200 : ℝ) - Real.pi * Real.exp (313 / 200 : ℝ) =
      -(Real.pi * Real.exp (313 / 200 : ℝ) - (1251 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1251 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1251 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1251_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (226770893607753 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1251_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1251 / 1600 : ℝ) (313 / 400 : ℝ) ≤ (1831637 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (313 / 200 : ℝ)) (150252181005272073 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (313 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1251_product_upper
  have hD : (1390522181123827 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1251 / 800 : ℝ) - (313 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1251_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1251_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1251 / 800 : ℝ) - (313 / 800 : ℝ)) ≤
      (1 / (1390522181123827 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1390522181123827 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((313 / 800 : ℝ) - Real.pi * Real.exp (1251 / 800 : ℝ)) ≤
      (2 / (1390522181123827 / 625000000 : ℝ) : ℝ) := by
    rw [show (313 / 800 : ℝ) - Real.pi * Real.exp (1251 / 800 : ℝ) =
      -(Real.pi * Real.exp (1251 / 800 : ℝ) - (313 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (150252181005272073 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (150252181005272073 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1251_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1251 / 1600 : ℝ) (313 / 400 : ℝ)) :
    (7150253 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1831637 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1251_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1251_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1252_leftExp :
    (23913374679 / 5000000000 : ℝ) ≤ Real.exp (313 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (313 / 200 : ℝ) (1050121897197 / 1000000000000 : ℝ)
    (23913374679 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1252_rightExp :
    Real.exp (1253 / 800 : ℝ) ≤ (23943285089 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1253 / 800 : ℝ) (525081459193 / 500000000000 : ℝ)
    (23943285089 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1252_denomUpper :
    Real.exp (73263806832606777 / 5000000000000000 : ℝ) ≤ (23100075861085117 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (73263806832606777 / 5000000000000000 : ℝ) (98796813227 /
    62500000000 : ℝ) (23100075861085117 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1252_denomLower :
    (177053220292237 / 78125000 : ℝ) ≤ Real.exp (9146031760568621 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9146031760568621 / 625000000000000 : ℝ) (315961052553 /
    200000000000 : ℝ) (177053220292237 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1252_product_lower :
    (9390758323068621 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (313 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1252_leftExp
    (by norm_num : (0 : ℝ) ≤ (23913374679 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1252_product_upper :
    Real.pi * Real.exp (1253 / 800 : ℝ) ≤ (75220056832606777 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1252_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1252_endpointLower :
    (7037871 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (313 / 400 : ℝ) (1253 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9390758323068621 / 625000000000000 : ℝ) (Real.pi * Real.exp (313 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1252_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1253 / 800 : ℝ) - (313 / 800 : ℝ)) ≤
      (23100075861085117 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1252_denomUpper
    linarith [hpThetaJensenCell1252_product_upper]
  have hi : (1 / (23100075861085117 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1253 / 800 : ℝ) - (313 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23100075861085117 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23100075861085117 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((313 / 800 : ℝ) - Real.pi * Real.exp (1253 / 800 : ℝ)) := by
    rw [show (313 / 800 : ℝ) - Real.pi * Real.exp (1253 / 800 : ℝ) =
      -(Real.pi * Real.exp (1253 / 800 : ℝ) - (313 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (313 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (313 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1252_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23100075861085117 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1252_endpointUpper :
    hpThetaJensenKernelEndpointUpper (313 / 400 : ℝ) (1253 / 1600 : ℝ) ≤ (7211563 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1253 / 800 : ℝ)) (75220056832606777 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1253 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1252_product_upper
  have hD : (177053220292237 / 78125000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (313 / 200 : ℝ) - (1253 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1252_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1252_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (313 / 200 : ℝ) - (1253 / 3200 : ℝ)) ≤
      (1 / (177053220292237 / 78125000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (177053220292237 / 78125000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1253 / 3200 : ℝ) - Real.pi * Real.exp (313 / 200 : ℝ)) ≤
      (2 / (177053220292237 / 78125000 : ℝ) : ℝ) := by
    rw [show (1253 / 3200 : ℝ) - Real.pi * Real.exp (313 / 200 : ℝ) =
      -(Real.pi * Real.exp (313 / 200 : ℝ) - (1253 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (75220056832606777 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (75220056832606777 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1252_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (313 / 400 : ℝ) (1253 / 1600 : ℝ)) :
    (7037871 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7211563 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1252_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1252_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1253_leftExp :
    (1915462807 / 400000000 : ℝ) ≤ Real.exp (1253 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1253 / 800 : ℝ) (210032583677 / 200000000000 : ℝ)
    (1915462807 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1253_rightExp :
    Real.exp (627 / 400 : ℝ) ≤ (47946465817 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (627 / 400 : ℝ) (131275492647 / 125000000000 : ℝ)
    (47946465817 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1253_denomUpper :
    Real.exp (146712656385426481 / 10000000000000000 : ℝ) ≤ (1470719080144979 / 625000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (146712656385426481 / 10000000000000000 : ℝ) (63266534301
    / 40000000000 : ℝ) (1470719080144979 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1253_denomLower :
    (1154276612677459 / 500000000 : ℝ) ≤ Real.exp (732606578846093 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (732606578846093 / 50000000000000 : ℝ) (316143580267 /
    200000000000 : ℝ) (1154276612677459 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1253_product_lower :
    (752200328846093 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1253 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1253_leftExp
    (by norm_num : (0 : ℝ) ≤ (1915462807 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1253_product_upper :
    Real.pi * Real.exp (627 / 400 : ℝ) ≤ (150628281385426481 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1253_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1253_endpointLower :
    (6927091 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1253 / 1600 : ℝ) (627 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (752200328846093 / 50000000000000 : ℝ) (Real.pi * Real.exp (1253 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1253_product_lower
  have hD : Real.exp (Real.pi * Real.exp (627 / 400 : ℝ) - (1253 / 3200 : ℝ)) ≤
      (1470719080144979 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1253_denomUpper
    linarith [hpThetaJensenCell1253_product_upper]
  have hi : (1 / (1470719080144979 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (627 / 400 : ℝ) - (1253 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1470719080144979 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1470719080144979 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1253 / 3200 : ℝ) - Real.pi * Real.exp (627 / 400 : ℝ)) := by
    rw [show (1253 / 3200 : ℝ) - Real.pi * Real.exp (627 / 400 : ℝ) =
      -(Real.pi * Real.exp (627 / 400 : ℝ) - (1253 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1253 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1253 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1253_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1470719080144979 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1253_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1253 / 1600 : ℝ) (627 / 800 : ℝ) ≤ (1419643 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (627 / 400 : ℝ)) (150628281385426481 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (627 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1253_product_upper
  have hD : (1154276612677459 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1253 / 800 : ℝ) - (627 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1253_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1253_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1253 / 800 : ℝ) - (627 / 1600 : ℝ)) ≤
      (1 / (1154276612677459 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1154276612677459 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((627 / 1600 : ℝ) - Real.pi * Real.exp (1253 / 800 : ℝ)) ≤
      (2 / (1154276612677459 / 500000000 : ℝ) : ℝ) := by
    rw [show (627 / 1600 : ℝ) - Real.pi * Real.exp (1253 / 800 : ℝ) =
      -(Real.pi * Real.exp (1253 / 800 : ℝ) - (627 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (150628281385426481 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (150628281385426481 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1253_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1253 / 1600 : ℝ) (627 / 800 : ℝ)) :
    (6927091 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1419643 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1253_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1253_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1254_leftExp :
    (9589293163 / 2000000000 : ℝ) ≤ Real.exp (627 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (627 / 400 : ℝ) (42008157647 / 40000000000 : ℝ)
    (9589293163 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1254_rightExp :
    Real.exp (251 / 160 : ℝ) ≤ (12001609093 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (251 / 160 : ℝ) (16410077587 / 15625000000 : ℝ)
    (12001609093 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1254_denomUpper :
    Real.exp (36724483615305149 / 2500000000000000 : ℝ) ≤ (11985778243955029 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (36724483615305149 / 2500000000000000 : ℝ) (1582579396263
    / 1000000000000 : ℝ) (11985778243955029 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1254_denomLower :
    (23516689916383357 / 10000000000 : ℝ) ≤ Real.exp (3667658960816937 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3667658960816937 / 250000000000000 : ℝ) (1581632228951 /
    1000000000000 : ℝ) (23516689916383357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1254_product_lower :
    (3765705835816937 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (627 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1254_leftExp
    (by norm_num : (0 : ℝ) ≤ (9589293163 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1254_product_upper :
    Real.pi * Real.exp (251 / 160 : ℝ) ≤ (37704171115305149 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1254_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1254_endpointLower :
    (6817893 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (627 / 800 : ℝ) (251 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3765705835816937 / 250000000000000 : ℝ) (Real.pi * Real.exp (627 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1254_product_lower
  have hD : Real.exp (Real.pi * Real.exp (251 / 160 : ℝ) - (627 / 1600 : ℝ)) ≤
      (11985778243955029 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1254_denomUpper
    linarith [hpThetaJensenCell1254_product_upper]
  have hi : (1 / (11985778243955029 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (251 / 160 : ℝ) - (627 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11985778243955029 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11985778243955029 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((627 / 1600 : ℝ) - Real.pi * Real.exp (251 / 160 : ℝ)) := by
    rw [show (627 / 1600 : ℝ) - Real.pi * Real.exp (251 / 160 : ℝ) =
      -(Real.pi * Real.exp (251 / 160 : ℝ) - (627 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (627 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (627 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1254_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11985778243955029 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1254_endpointUpper :
    hpThetaJensenKernelEndpointUpper (627 / 800 : ℝ) (251 / 320 : ℝ) ≤ (3493241 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (251 / 160 : ℝ)) (37704171115305149 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (251 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1254_product_upper
  have hD : (23516689916383357 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (627 / 400 : ℝ) - (251 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1254_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1254_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (627 / 400 : ℝ) - (251 / 640 : ℝ)) ≤
      (1 / (23516689916383357 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23516689916383357 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((251 / 640 : ℝ) - Real.pi * Real.exp (627 / 400 : ℝ)) ≤
      (2 / (23516689916383357 / 10000000000 : ℝ) : ℝ) := by
    rw [show (251 / 640 : ℝ) - Real.pi * Real.exp (627 / 400 : ℝ) =
      -(Real.pi * Real.exp (627 / 400 : ℝ) - (251 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37704171115305149 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (37704171115305149 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1254_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (627 / 800 : ℝ) (251 / 320 : ℝ)) :
    (6817893 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3493241 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1254_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1254_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1255_leftExp :
    (4800643637 / 1000000000 : ℝ) ≤ Real.exp (251 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (251 / 160 : ℝ) (1050244965567 / 1000000000000 : ℝ)
    (4800643637 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1255_rightExp :
    Real.exp (157 / 100 : ℝ) ≤ (48066481939 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (157 / 100 : ℝ) (262571497891 / 250000000000 : ℝ)
    (48066481939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1255_denomUpper :
    Real.exp (147083448194188827 / 10000000000000000 : ℝ) ≤ (24420412353899169 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (147083448194188827 / 10000000000000000 : ℝ)
    (1583497131667 / 1000000000000 : ℝ) (24420412353899169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1255_denomLower :
    (11978231961699837 / 5000000000 : ℝ) ≤ Real.exp (1836145455606263 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1836145455606263 / 125000000000000 : ℝ) (395637062341 /
    250000000000 : ℝ) (11978231961699837 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1255_product_lower :
    (1885207955606263 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (251 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1255_leftExp
    (by norm_num : (0 : ℝ) ≤ (4800643637 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1255_product_upper :
    Real.pi * Real.exp (157 / 100 : ℝ) ≤ (151005323194188827 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1255_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1255_endpointLower :
    (6710257 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (251 / 320 : ℝ) (157 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1885207955606263 / 125000000000000 : ℝ) (Real.pi * Real.exp (251 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1255_product_lower
  have hD : Real.exp (Real.pi * Real.exp (157 / 100 : ℝ) - (251 / 640 : ℝ)) ≤
      (24420412353899169 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1255_denomUpper
    linarith [hpThetaJensenCell1255_product_upper]
  have hi : (1 / (24420412353899169 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (157 / 100 : ℝ) - (251 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24420412353899169 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24420412353899169 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((251 / 640 : ℝ) - Real.pi * Real.exp (157 / 100 : ℝ)) := by
    rw [show (251 / 640 : ℝ) - Real.pi * Real.exp (157 / 100 : ℝ) =
      -(Real.pi * Real.exp (157 / 100 : ℝ) - (251 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (251 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (251 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1255_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24420412353899169 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1255_endpointUpper :
    hpThetaJensenKernelEndpointUpper (251 / 320 : ℝ) (157 / 200 : ℝ) ≤ (3438173 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (157 / 100 : ℝ)) (151005323194188827 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (157 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1255_product_upper
  have hD : (11978231961699837 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (251 / 160 : ℝ) - (157 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1255_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1255_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (251 / 160 : ℝ) - (157 / 400 : ℝ)) ≤
      (1 / (11978231961699837 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11978231961699837 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((157 / 400 : ℝ) - Real.pi * Real.exp (251 / 160 : ℝ)) ≤
      (2 / (11978231961699837 / 5000000000 : ℝ) : ℝ) := by
    rw [show (157 / 400 : ℝ) - Real.pi * Real.exp (251 / 160 : ℝ) =
      -(Real.pi * Real.exp (251 / 160 : ℝ) - (157 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (151005323194188827 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (151005323194188827 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1255_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (251 / 320 : ℝ) (157 / 200 : ℝ)) :
    (6710257 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3438173 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1255_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1255_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1256_leftExp :
    (48066481937 / 10000000000 : ℝ) ≤ Real.exp (157 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157 / 100 : ℝ) (1050285991563 / 1000000000000 : ℝ)
    (48066481937 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1256_rightExp :
    Real.exp (1257 / 800 : ℝ) ≤ (4812660261 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1257 / 800 : ℝ) (525163509581 / 500000000000 : ℝ)
    (4812660261 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1256_denomUpper :
    Real.exp (14726919787335773 / 1000000000000000 : ℝ) ≤ (24878259816872127 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (14726919787335773 / 1000000000000000 : ℝ) (792208283753
    / 500000000000 : ℝ) (24878259816872127 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1256_denomLower :
    (6101259260602591 / 2500000000 : ℝ) ≤ Real.exp (18384643765177963 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18384643765177963 / 1250000000000000 : ℝ) (158346596641
    / 100000000000 : ℝ) (6101259260602591 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1256_product_lower :
    (18875659390177963 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (157 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1256_leftExp
    (by norm_num : (0 : ℝ) ≤ (48066481937 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1256_product_upper :
    Real.pi * Real.exp (1257 / 800 : ℝ) ≤ (15119419787335773 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1256_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1256_endpointLower :
    (1651041 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (157 / 200 : ℝ) (1257 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18875659390177963 / 1250000000000000 : ℝ) (Real.pi * Real.exp (157 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1256_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1257 / 800 : ℝ) - (157 / 400 : ℝ)) ≤
      (24878259816872127 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1256_denomUpper
    linarith [hpThetaJensenCell1256_product_upper]
  have hi : (1 / (24878259816872127 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1257 / 800 : ℝ) - (157 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24878259816872127 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24878259816872127 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((157 / 400 : ℝ) - Real.pi * Real.exp (1257 / 800 : ℝ)) := by
    rw [show (157 / 400 : ℝ) - Real.pi * Real.exp (1257 / 800 : ℝ) =
      -(Real.pi * Real.exp (1257 / 800 : ℝ) - (157 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (157 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (157 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1256_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24878259816872127 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1256_endpointUpper :
    hpThetaJensenKernelEndpointUpper (157 / 200 : ℝ) (1257 / 1600 : ℝ) ≤ (845973 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1257 / 800 : ℝ)) (15119419787335773 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1257 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1256_product_upper
  have hD : (6101259260602591 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (157 / 100 : ℝ) - (1257 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1256_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1256_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (157 / 100 : ℝ) - (1257 / 3200 : ℝ)) ≤
      (1 / (6101259260602591 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6101259260602591 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1257 / 3200 : ℝ) - Real.pi * Real.exp (157 / 100 : ℝ)) ≤
      (2 / (6101259260602591 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1257 / 3200 : ℝ) - Real.pi * Real.exp (157 / 100 : ℝ) =
      -(Real.pi * Real.exp (157 / 100 : ℝ) - (1257 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15119419787335773 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (15119419787335773 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1256_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (157 / 200 : ℝ) (1257 / 1600 : ℝ)) :
    (1651041 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (845973 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1256_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1256_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1257_leftExp :
    (48126602607 / 10000000000 : ℝ) ≤ Real.exp (1257 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1257 / 800 : ℝ) (1050327019161 / 1000000000000 : ℝ)
    (48126602607 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1257_rightExp :
    Real.exp (629 / 400 : ℝ) ≤ (48186798477 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (629 / 400 : ℝ) (525184024181 / 500000000000 : ℝ)
    (48186798477 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1257_denomUpper :
    Real.exp (147455183787753861 / 10000000000000000 : ℝ) ≤ (1267264499818297 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (147455183787753861 / 10000000000000000 : ℝ)
    (792668853777 / 500000000000 : ℝ) (1267264499818297 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1257_denomLower :
    (3107824510395369 / 1250000000 : ℝ) ≤ Real.exp (18407862467166293 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18407862467166293 / 1250000000000000 : ℝ) (9902408649 /
    6250000000 : ℝ) (3107824510395369 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1257_product_lower :
    (18899268717166293 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1257 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1257_leftExp
    (by norm_num : (0 : ℝ) ≤ (48126602607 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1257_product_upper :
    Real.pi * Real.exp (629 / 400 : ℝ) ≤ (151383308787753861 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1257_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1257_endpointLower :
    (812449 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1257 / 1600 : ℝ) (629 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18899268717166293 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1257 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1257_product_lower
  have hD : Real.exp (Real.pi * Real.exp (629 / 400 : ℝ) - (1257 / 3200 : ℝ)) ≤
      (1267264499818297 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1257_denomUpper
    linarith [hpThetaJensenCell1257_product_upper]
  have hi : (1 / (1267264499818297 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (629 / 400 : ℝ) - (1257 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1267264499818297 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1267264499818297 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1257 / 3200 : ℝ) - Real.pi * Real.exp (629 / 400 : ℝ)) := by
    rw [show (1257 / 3200 : ℝ) - Real.pi * Real.exp (629 / 400 : ℝ) =
      -(Real.pi * Real.exp (629 / 400 : ℝ) - (1257 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1257 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1257 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1257_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1267264499818297 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1257_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1257 / 1600 : ℝ) (629 / 800 : ℝ) ≤ (3330389 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (629 / 400 : ℝ)) (151383308787753861 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (629 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1257_product_upper
  have hD : (3107824510395369 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1257 / 800 : ℝ) - (629 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1257_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1257_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1257 / 800 : ℝ) - (629 / 1600 : ℝ)) ≤
      (1 / (3107824510395369 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3107824510395369 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((629 / 1600 : ℝ) - Real.pi * Real.exp (1257 / 800 : ℝ)) ≤
      (2 / (3107824510395369 / 1250000000 : ℝ) : ℝ) := by
    rw [show (629 / 1600 : ℝ) - Real.pi * Real.exp (1257 / 800 : ℝ) =
      -(Real.pi * Real.exp (1257 / 800 : ℝ) - (629 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (151383308787753861 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (151383308787753861 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1257_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1257 / 1600 : ℝ) (629 / 800 : ℝ)) :
    (812449 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3330389 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1257_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1257_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1258_leftExp :
    (24093399237 / 5000000000 : ℝ) ≤ Real.exp (629 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (629 / 400 : ℝ) (1050368048361 / 1000000000000 : ℝ)
    (24093399237 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1258_rightExp :
    Real.exp (1259 / 800 : ℝ) ≤ (12061767409 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1259 / 800 : ℝ) (210081815833 / 200000000000 : ℝ)
    (12061767409 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1258_denomUpper :
    Real.exp (36910351559742537 / 2500000000000000 : ℝ) ≤ (1613856145491593 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36910351559742537 / 2500000000000000 : ℝ) (1586260555657
    / 1000000000000 : ℝ) (1613856145491593 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1258_denomLower :
    (25329332060629031 / 10000000000 : ℝ) ≤ Real.exp (9215555349470663 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9215555349470663 / 625000000000000 : ℝ) (79265325273 /
    50000000000 : ℝ) (25329332060629031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1258_product_lower :
    (9461453786970663 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (629 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1258_leftExp
    (by norm_num : (0 : ℝ) ≤ (24093399237 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1258_product_upper :
    Real.pi * Real.exp (1259 / 800 : ℝ) ≤ (37893164059742537 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1258_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1258_endpointLower :
    (255861 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (629 / 800 : ℝ) (1259 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9461453786970663 / 625000000000000 : ℝ) (Real.pi * Real.exp (629 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1258_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1259 / 800 : ℝ) - (629 / 1600 : ℝ)) ≤
      (1613856145491593 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1258_denomUpper
    linarith [hpThetaJensenCell1258_product_upper]
  have hi : (1 / (1613856145491593 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1259 / 800 : ℝ) - (629 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1613856145491593 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1613856145491593 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((629 / 1600 : ℝ) - Real.pi * Real.exp (1259 / 800 : ℝ)) := by
    rw [show (629 / 1600 : ℝ) - Real.pi * Real.exp (1259 / 800 : ℝ) =
      -(Real.pi * Real.exp (1259 / 800 : ℝ) - (629 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (629 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (629 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1258_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1613856145491593 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1258_endpointUpper :
    hpThetaJensenKernelEndpointUpper (629 / 800 : ℝ) (1259 / 1600 : ℝ) ≤ (1638827 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1259 / 800 : ℝ)) (37893164059742537 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1259 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1258_product_upper
  have hD : (25329332060629031 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (629 / 400 : ℝ) - (1259 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1258_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1258_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (629 / 400 : ℝ) - (1259 / 3200 : ℝ)) ≤
      (1 / (25329332060629031 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (25329332060629031 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1259 / 3200 : ℝ) - Real.pi * Real.exp (629 / 400 : ℝ)) ≤
      (2 / (25329332060629031 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1259 / 3200 : ℝ) - Real.pi * Real.exp (629 / 400 : ℝ) =
      -(Real.pi * Real.exp (629 / 400 : ℝ) - (1259 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37893164059742537 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (37893164059742537 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1258_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (629 / 800 : ℝ) (1259 / 1600 : ℝ)) :
    (255861 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1638827 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1258_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1258_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1259_leftExp :
    (24123534817 / 5000000000 : ℝ) ≤ Real.exp (1259 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1259 / 800 : ℝ) (262602269791 / 250000000000 : ℝ)
    (24123534817 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1259_rightExp :
    Real.exp (63 / 40 : ℝ) ≤ (24153708091 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 40 : ℝ) (1050450111571 / 1000000000000 : ℝ)
    (24153708091 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1259_denomUpper :
    Real.exp (73913932762728963 / 5000000000000000 : ℝ) ≤ (13153842312819189 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (73913932762728963 / 5000000000000000 : ℝ) (198398139457
    / 125000000000 : ℝ) (13153842312819189 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1259_denomLower :
    (12902720144022161 / 5000000000 : ℝ) ≤ Real.exp (9227194249101083 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9227194249101083 / 625000000000000 : ℝ) (1586229335117 /
    1000000000000 : ℝ) (12902720144022161 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1259_product_lower :
    (9473287999101083 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1259 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1259_leftExp
    (by norm_num : (0 : ℝ) ≤ (24123534817 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1259_product_upper :
    Real.pi * Real.exp (63 / 40 : ℝ) ≤ (75881120262728963 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1259_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1259_endpointLower :
    (6294941 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1259 / 1600 : ℝ) (63 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9473287999101083 / 625000000000000 : ℝ) (Real.pi * Real.exp (1259 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1259_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 40 : ℝ) - (1259 / 3200 : ℝ)) ≤
      (13153842312819189 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1259_denomUpper
    linarith [hpThetaJensenCell1259_product_upper]
  have hi : (1 / (13153842312819189 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 40 : ℝ) - (1259 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13153842312819189 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13153842312819189 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1259 / 3200 : ℝ) - Real.pi * Real.exp (63 / 40 : ℝ)) := by
    rw [show (1259 / 3200 : ℝ) - Real.pi * Real.exp (63 / 40 : ℝ) =
      -(Real.pi * Real.exp (63 / 40 : ℝ) - (1259 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1259 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1259 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1259_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13153842312819189 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1259_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1259 / 1600 : ℝ) (63 / 80 : ℝ) ≤ (1290271 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 40 : ℝ)) (75881120262728963 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1259_product_upper
  have hD : (12902720144022161 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1259 / 800 : ℝ) - (63 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1259_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1259_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1259 / 800 : ℝ) - (63 / 160 : ℝ)) ≤
      (1 / (12902720144022161 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12902720144022161 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 160 : ℝ) - Real.pi * Real.exp (1259 / 800 : ℝ)) ≤
      (2 / (12902720144022161 / 5000000000 : ℝ) : ℝ) := by
    rw [show (63 / 160 : ℝ) - Real.pi * Real.exp (1259 / 800 : ℝ) =
      -(Real.pi * Real.exp (1259 / 800 : ℝ) - (63 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (75881120262728963 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (75881120262728963 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1259_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1259 / 1600 : ℝ) (63 / 80 : ℝ)) :
    (6294941 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1290271 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1259_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1259_endpointUpper

def hpThetaJensenCellsBatch062Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (42491 / 50000000 : ℝ)
  | 1 => (8366797 / 10000000000 : ℝ)
  | 2 => (8237233 / 10000000000 : ℝ)
  | 3 => (4054743 / 5000000000 : ℝ)
  | 4 => (1995883 / 2500000000 : ℝ)
  | 5 => (7859351 / 10000000000 : ℝ)
  | 6 => (7736919 / 10000000000 : ℝ)
  | 7 => (1523243 / 2000000000 : ℝ)
  | 8 => (3748609 / 5000000000 : ℝ)
  | 9 => (3689953 / 5000000000 : ℝ)
  | 10 => (3632129 / 5000000000 : ℝ)
  | 11 => (7150253 / 10000000000 : ℝ)
  | 12 => (7037871 / 10000000000 : ℝ)
  | 13 => (6927091 / 10000000000 : ℝ)
  | 14 => (6817893 / 10000000000 : ℝ)
  | 15 => (6710257 / 10000000000 : ℝ)
  | 16 => (1651041 / 2500000000 : ℝ)
  | 17 => (812449 / 1250000000 : ℝ)
  | 18 => (255861 / 400000000 : ℝ)
  | 19 => (6294941 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch062Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2176379 / 2500000000 : ℝ)
  | 1 => (267847 / 312500000 : ℝ)
  | 2 => (843857 / 1000000000 : ℝ)
  | 3 => (8307891 / 10000000000 : ℝ)
  | 4 => (1635809 / 2000000000 : ℝ)
  | 5 => (1006501 / 1250000000 : ℝ)
  | 6 => (3963379 / 5000000000 : ℝ)
  | 7 => (3901637 / 5000000000 : ℝ)
  | 8 => (1920383 / 2500000000 : ℝ)
  | 9 => (7561511 / 10000000000 : ℝ)
  | 10 => (744319 / 1000000000 : ℝ)
  | 11 => (1831637 / 2500000000 : ℝ)
  | 12 => (7211563 / 10000000000 : ℝ)
  | 13 => (1419643 / 2000000000 : ℝ)
  | 14 => (3493241 / 5000000000 : ℝ)
  | 15 => (3438173 / 5000000000 : ℝ)
  | 16 => (845973 / 1250000000 : ℝ)
  | 17 => (3330389 / 5000000000 : ℝ)
  | 18 => (1638827 / 2500000000 : ℝ)
  | 19 => (1290271 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch062_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch062Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch062Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1240_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1241_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1242_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1243_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1244_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1245_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1246_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1247_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1248_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1249_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1250_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1251_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1252_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1253_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1254_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1255_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1256_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1257_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1258_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1259_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper] at h ⊢
    exact h

end HodgeProofHP
