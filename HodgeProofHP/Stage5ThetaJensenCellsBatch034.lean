import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell680_leftExp :
    (11698234259 / 5000000000 : ℝ) ≤ Real.exp (17 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 20 : ℝ) (1026918427657 / 1000000000000 : ℝ)
    (11698234259 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell680_rightExp :
    Real.exp (681 / 800 : ℝ) ≤ (2928216549 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (681 / 800 : ℝ) (1026958542443 / 1000000000000 : ℝ)
    (2928216549 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell680_denomUpper :
    Real.exp (8933639612822557 / 1250000000000000 : ℝ) ≤ (12701771911023 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8933639612822557 / 1250000000000000 : ℝ) (312561705781 /
    250000000000 : ℝ) (12701771911023 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell680_denomLower :
    (12581571279263 / 10000000000 : ℝ) ≤ Real.exp (4460877082775041 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4460877082775041 / 625000000000000 : ℝ) (624937692371 /
    500000000000 : ℝ) (12581571279263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell680_product_lower :
    (4593884895275041 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell680_leftExp
    (by norm_num : (0 : ℝ) ≤ (11698234259 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell680_product_upper :
    Real.pi * Real.exp (681 / 800 : ℝ) ≤ (9199264612822557 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell680_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell680_endpointLower :
    (2708305539 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 40 : ℝ) (681 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4593884895275041 / 625000000000000 : ℝ) (Real.pi * Real.exp (17 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell680_product_lower
  have hD : Real.exp (Real.pi * Real.exp (681 / 800 : ℝ) - (17 / 80 : ℝ)) ≤
      (12701771911023 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell680_denomUpper
    linarith [hpThetaJensenCell680_product_upper]
  have hi : (1 / (12701771911023 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (681 / 800 : ℝ) - (17 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12701771911023 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12701771911023 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 80 : ℝ) - Real.pi * Real.exp (681 / 800 : ℝ)) := by
    rw [show (17 / 80 : ℝ) - Real.pi * Real.exp (681 / 800 : ℝ) =
      -(Real.pi * Real.exp (681 / 800 : ℝ) - (17 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 20 : ℝ)) := by
    have h := hpThetaJensenCell680_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12701771911023 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell680_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 40 : ℝ) (681 / 1600 : ℝ) ≤ (1374562349 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (681 / 800 : ℝ)) (9199264612822557 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (681 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell680_product_upper
  have hD : (12581571279263 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 20 : ℝ) - (681 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell680_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell680_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 20 : ℝ) - (681 / 3200 : ℝ)) ≤
      (1 / (12581571279263 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12581571279263 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((681 / 3200 : ℝ) - Real.pi * Real.exp (17 / 20 : ℝ)) ≤
      (2 / (12581571279263 / 10000000000 : ℝ) : ℝ) := by
    rw [show (681 / 3200 : ℝ) - Real.pi * Real.exp (17 / 20 : ℝ) =
      -(Real.pi * Real.exp (17 / 20 : ℝ) - (681 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9199264612822557 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (9199264612822557 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell680_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 40 : ℝ) (681 / 1600 : ℝ)) :
    (2708305539 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1374562349 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell680_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell680_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell681_leftExp :
    (2342573239 / 1000000000 : ℝ) ≤ Real.exp (681 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (681 / 800 : ℝ) (513479271221 / 500000000000 : ℝ)
    (2342573239 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell681_rightExp :
    Real.exp (341 / 400 : ℝ) ≤ (11727516433 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (341 / 400 : ℝ) (513499329397 / 500000000000 : ℝ)
    (11727516433 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell681_denomUpper :
    Real.exp (35779021033297769 / 5000000000000000 : ℝ) ≤ (12815226325871 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35779021033297769 / 5000000000000000 : ℝ) (625297151957
    / 500000000000 : ℝ) (12815226325871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell681_denomLower :
    (12693806039497 / 10000000000 : ℝ) ≤ Real.exp (893285543382061 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (893285543382061 / 125000000000000 : ℝ) (1250222312931 /
    1000000000000 : ℝ) (12693806039497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell681_product_lower :
    (919926168382061 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (681 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell681_leftExp
    (by norm_num : (0 : ℝ) ≤ (2342573239 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell681_product_upper :
    Real.pi * Real.exp (341 / 400 : ℝ) ≤ (36843083533297769 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell681_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell681_endpointLower :
    (538381963 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (681 / 1600 : ℝ) (341 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (919926168382061 / 125000000000000 : ℝ) (Real.pi * Real.exp (681 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell681_product_lower
  have hD : Real.exp (Real.pi * Real.exp (341 / 400 : ℝ) - (681 / 3200 : ℝ)) ≤
      (12815226325871 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell681_denomUpper
    linarith [hpThetaJensenCell681_product_upper]
  have hi : (1 / (12815226325871 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (341 / 400 : ℝ) - (681 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12815226325871 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12815226325871 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((681 / 3200 : ℝ) - Real.pi * Real.exp (341 / 400 : ℝ)) := by
    rw [show (681 / 3200 : ℝ) - Real.pi * Real.exp (341 / 400 : ℝ) =
      -(Real.pi * Real.exp (341 / 400 : ℝ) - (681 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (681 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (681 / 800 : ℝ)) := by
    have h := hpThetaJensenCell681_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12815226325871 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell681_endpointUpper :
    hpThetaJensenKernelEndpointUpper (681 / 1600 : ℝ) (341 / 800 : ℝ) ≤ (546502383 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (341 / 400 : ℝ)) (36843083533297769 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (341 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell681_product_upper
  have hD : (12693806039497 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (681 / 800 : ℝ) - (341 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell681_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell681_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (681 / 800 : ℝ) - (341 / 1600 : ℝ)) ≤
      (1 / (12693806039497 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12693806039497 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((341 / 1600 : ℝ) - Real.pi * Real.exp (681 / 800 : ℝ)) ≤
      (2 / (12693806039497 / 10000000000 : ℝ) : ℝ) := by
    rw [show (341 / 1600 : ℝ) - Real.pi * Real.exp (681 / 800 : ℝ) =
      -(Real.pi * Real.exp (681 / 800 : ℝ) - (341 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36843083533297769 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (36843083533297769 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell681_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (681 / 1600 : ℝ) (341 / 800 : ℝ)) :
    (538381963 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (546502383 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell681_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell681_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell682_leftExp :
    (732969777 / 312500000 : ℝ) ≤ Real.exp (341 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (341 / 400 : ℝ) (1026998658793 / 1000000000000 : ℝ)
    (732969777 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell682_rightExp :
    Real.exp (683 / 800 : ℝ) ≤ (23484369989 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (683 / 800 : ℝ) (1027038776713 / 1000000000000 : ℝ)
    (23484369989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell682_denomUpper :
    Real.exp (71647082366852477 / 10000000000000000 : ℝ) ≤ (12929843003871 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (71647082366852477 / 10000000000000000 : ℝ) (125094233137
    / 100000000000 : ℝ) (12929843003871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell682_denomLower :
    (12807189264159 / 10000000000 : ℝ) ≤ Real.exp (279499096114373 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (279499096114373 / 39062500000000 : ℝ) (625284893397 /
    500000000000 : ℝ) (12807189264159 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell682_product_lower :
    (287836498458123 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (341 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell682_leftExp
    (by norm_num : (0 : ℝ) ≤ (732969777 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell682_product_upper :
    Real.pi * Real.exp (683 / 800 : ℝ) ≤ (73778332366852477 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell682_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell682_endpointLower :
    (1337790599 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (341 / 800 : ℝ) (683 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (287836498458123 / 39062500000000 : ℝ) (Real.pi * Real.exp (341 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell682_product_lower
  have hD : Real.exp (Real.pi * Real.exp (683 / 800 : ℝ) - (341 / 1600 : ℝ)) ≤
      (12929843003871 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell682_denomUpper
    linarith [hpThetaJensenCell682_product_upper]
  have hi : (1 / (12929843003871 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (683 / 800 : ℝ) - (341 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12929843003871 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12929843003871 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((341 / 1600 : ℝ) - Real.pi * Real.exp (683 / 800 : ℝ)) := by
    rw [show (341 / 1600 : ℝ) - Real.pi * Real.exp (683 / 800 : ℝ) =
      -(Real.pi * Real.exp (683 / 800 : ℝ) - (341 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (341 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (341 / 400 : ℝ)) := by
    have h := hpThetaJensenCell682_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12929843003871 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell682_endpointUpper :
    hpThetaJensenKernelEndpointUpper (341 / 800 : ℝ) (683 / 1600 : ℝ) ≤ (271596693 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (683 / 800 : ℝ)) (73778332366852477 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (683 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell682_product_upper
  have hD : (12807189264159 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (341 / 400 : ℝ) - (683 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell682_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell682_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (341 / 400 : ℝ) - (683 / 3200 : ℝ)) ≤
      (1 / (12807189264159 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12807189264159 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((683 / 3200 : ℝ) - Real.pi * Real.exp (341 / 400 : ℝ)) ≤
      (2 / (12807189264159 / 10000000000 : ℝ) : ℝ) := by
    rw [show (683 / 3200 : ℝ) - Real.pi * Real.exp (341 / 400 : ℝ) =
      -(Real.pi * Real.exp (341 / 400 : ℝ) - (683 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (73778332366852477 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (73778332366852477 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell682_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (341 / 800 : ℝ) (683 / 1600 : ℝ)) :
    (1337790599 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (271596693 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell682_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell682_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell683_leftExp :
    (5871092497 / 2500000000 : ℝ) ≤ Real.exp (683 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (683 / 800 : ℝ) (128379847089 / 125000000000 : ℝ)
    (5871092497 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell683_rightExp :
    Real.exp (171 / 200 : ℝ) ≤ (23513743807 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (171 / 200 : ℝ) (1027078896199 / 1000000000000 : ℝ)
    (23513743807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell683_denomUpper :
    Real.exp (71736237947864551 / 10000000000000000 : ℝ) ≤ (13045635179481 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (71736237947864551 / 10000000000000000 : ℝ)
    (1251290906459 / 1000000000000 : ℝ) (13045635179481 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell683_denomLower :
    (12921734026613 / 10000000000 : ℝ) ≤ Real.exp (2238775277479403 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2238775277479403 / 312500000000000 : ℝ) (50036712293 /
    40000000000 : ℝ) (12921734026613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell683_product_lower :
    (2305572152479403 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (683 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell683_leftExp
    (by norm_num : (0 : ℝ) ≤ (5871092497 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell683_product_upper :
    Real.pi * Real.exp (171 / 200 : ℝ) ≤ (73870612947864551 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell683_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell683_endpointLower :
    (1329659819 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (683 / 1600 : ℝ) (171 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2305572152479403 / 312500000000000 : ℝ) (Real.pi * Real.exp (683 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell683_product_lower
  have hD : Real.exp (Real.pi * Real.exp (171 / 200 : ℝ) - (683 / 3200 : ℝ)) ≤
      (13045635179481 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell683_denomUpper
    linarith [hpThetaJensenCell683_product_upper]
  have hi : (1 / (13045635179481 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (171 / 200 : ℝ) - (683 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13045635179481 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13045635179481 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((683 / 3200 : ℝ) - Real.pi * Real.exp (171 / 200 : ℝ)) := by
    rw [show (683 / 3200 : ℝ) - Real.pi * Real.exp (171 / 200 : ℝ) =
      -(Real.pi * Real.exp (171 / 200 : ℝ) - (683 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (683 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (683 / 800 : ℝ)) := by
    have h := hpThetaJensenCell683_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13045635179481 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell683_endpointUpper :
    hpThetaJensenKernelEndpointUpper (683 / 1600 : ℝ) (171 / 400 : ℝ) ≤ (269948969 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (171 / 200 : ℝ)) (73870612947864551 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (171 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell683_product_upper
  have hD : (12921734026613 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (683 / 800 : ℝ) - (171 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell683_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell683_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (683 / 800 : ℝ) - (171 / 800 : ℝ)) ≤
      (1 / (12921734026613 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12921734026613 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((171 / 800 : ℝ) - Real.pi * Real.exp (683 / 800 : ℝ)) ≤
      (2 / (12921734026613 / 10000000000 : ℝ) : ℝ) := by
    rw [show (171 / 800 : ℝ) - Real.pi * Real.exp (683 / 800 : ℝ) =
      -(Real.pi * Real.exp (683 / 800 : ℝ) - (171 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (73870612947864551 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (73870612947864551 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell683_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (683 / 1600 : ℝ) (171 / 400 : ℝ)) :
    (1329659819 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (269948969 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell683_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell683_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell684_leftExp :
    (4702748761 / 2000000000 : ℝ) ≤ Real.exp (171 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (171 / 200 : ℝ) (513539448099 / 500000000000 : ℝ)
    (4702748761 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell684_rightExp :
    Real.exp (137 / 160 : ℝ) ≤ (5885788591 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (137 / 160 : ℝ) (256779754313 / 250000000000 : ℝ)
    (5885788591 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell684_denomUpper :
    Real.exp (17956377236965463 / 2500000000000000 : ℝ) ≤ (13162616243263 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17956377236965463 / 2500000000000000 : ℝ) (10013120241 /
    8000000000 : ℝ) (13162616243263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell684_denomLower :
    (1629681692557 / 1250000000 : ℝ) ≤ Real.exp (1793249110695939 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1793249110695939 / 250000000000000 : ℝ) (1251266375453 /
    1000000000000 : ℝ) (1629681692557 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell684_product_lower :
    (1846764735695939 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (171 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell684_leftExp
    (by norm_num : (0 : ℝ) ≤ (4702748761 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell684_product_upper :
    Real.pi * Real.exp (137 / 160 : ℝ) ≤ (18490752236965463 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell684_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell684_endpointLower :
    (2643125081 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (171 / 400 : ℝ) (137 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1846764735695939 / 250000000000000 : ℝ) (Real.pi * Real.exp (171 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell684_product_lower
  have hD : Real.exp (Real.pi * Real.exp (137 / 160 : ℝ) - (171 / 800 : ℝ)) ≤
      (13162616243263 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell684_denomUpper
    linarith [hpThetaJensenCell684_product_upper]
  have hi : (1 / (13162616243263 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (137 / 160 : ℝ) - (171 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13162616243263 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13162616243263 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((171 / 800 : ℝ) - Real.pi * Real.exp (137 / 160 : ℝ)) := by
    rw [show (171 / 800 : ℝ) - Real.pi * Real.exp (137 / 160 : ℝ) =
      -(Real.pi * Real.exp (137 / 160 : ℝ) - (171 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (171 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (171 / 200 : ℝ)) := by
    have h := hpThetaJensenCell684_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13162616243263 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell684_endpointUpper :
    hpThetaJensenKernelEndpointUpper (171 / 400 : ℝ) (137 / 320 : ℝ) ≤ (167692509 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (137 / 160 : ℝ)) (18490752236965463 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (137 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell684_product_upper
  have hD : (1629681692557 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (171 / 200 : ℝ) - (137 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell684_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell684_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (171 / 200 : ℝ) - (137 / 640 : ℝ)) ≤
      (1 / (1629681692557 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1629681692557 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((137 / 640 : ℝ) - Real.pi * Real.exp (171 / 200 : ℝ)) ≤
      (2 / (1629681692557 / 1250000000 : ℝ) : ℝ) := by
    rw [show (137 / 640 : ℝ) - Real.pi * Real.exp (171 / 200 : ℝ) =
      -(Real.pi * Real.exp (171 / 200 : ℝ) - (137 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18490752236965463 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (18490752236965463 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell684_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (171 / 400 : ℝ) (137 / 320 : ℝ)) :
    (2643125081 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (167692509 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell684_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell684_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell685_leftExp :
    (23543154363 / 10000000000 : ℝ) ≤ Real.exp (137 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (137 / 160 : ℝ) (1027119017251 / 1000000000000 : ℝ)
    (23543154363 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell685_rightExp :
    Real.exp (343 / 400 : ℝ) ≤ (5893150427 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (343 / 400 : ℝ) (32098723121 / 31250000000 : ℝ)
    (5893150427 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell685_denomUpper :
    Real.exp (17978723879410211 / 2500000000000000 : ℝ) ≤ (13280799768839 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17978723879410211 / 2500000000000000 : ℝ) (1251989703363
    / 1000000000000 : ℝ) (13280799768839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell685_denomLower :
    (2630872240889 / 2000000000 : ℝ) ≤ Real.exp (8977404425195737 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8977404425195737 / 1250000000000000 : ℝ) (312903873043 /
    250000000000 : ℝ) (2630872240889 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell685_product_lower :
    (9245373175195737 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (137 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell685_leftExp
    (by norm_num : (0 : ℝ) ≤ (23543154363 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell685_product_upper :
    Real.pi * Real.exp (343 / 400 : ℝ) ≤ (18513880129410211 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell685_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell685_endpointLower :
    (82093671 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (137 / 320 : ℝ) (343 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9245373175195737 / 1250000000000000 : ℝ) (Real.pi * Real.exp (137 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell685_product_lower
  have hD : Real.exp (Real.pi * Real.exp (343 / 400 : ℝ) - (137 / 640 : ℝ)) ≤
      (13280799768839 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell685_denomUpper
    linarith [hpThetaJensenCell685_product_upper]
  have hi : (1 / (13280799768839 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (343 / 400 : ℝ) - (137 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13280799768839 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13280799768839 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((137 / 640 : ℝ) - Real.pi * Real.exp (343 / 400 : ℝ)) := by
    rw [show (137 / 640 : ℝ) - Real.pi * Real.exp (343 / 400 : ℝ) =
      -(Real.pi * Real.exp (343 / 400 : ℝ) - (137 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (137 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (137 / 160 : ℝ)) := by
    have h := hpThetaJensenCell685_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13280799768839 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell685_endpointUpper :
    hpThetaJensenKernelEndpointUpper (137 / 320 : ℝ) (343 / 800 : ℝ) ≤ (2666738237 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (343 / 400 : ℝ)) (18513880129410211 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (343 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell685_product_upper
  have hD : (2630872240889 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (137 / 160 : ℝ) - (343 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell685_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell685_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (137 / 160 : ℝ) - (343 / 1600 : ℝ)) ≤
      (1 / (2630872240889 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2630872240889 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((343 / 1600 : ℝ) - Real.pi * Real.exp (137 / 160 : ℝ)) ≤
      (2 / (2630872240889 / 2000000000 : ℝ) : ℝ) := by
    rw [show (343 / 1600 : ℝ) - Real.pi * Real.exp (137 / 160 : ℝ) =
      -(Real.pi * Real.exp (137 / 160 : ℝ) - (343 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18513880129410211 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (18513880129410211 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell685_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (137 / 320 : ℝ) (343 / 800 : ℝ)) :
    (82093671 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2666738237 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell685_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell685_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell686_leftExp :
    (11786300853 / 5000000000 : ℝ) ≤ Real.exp (343 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (343 / 400 : ℝ) (1027159139871 / 1000000000000 : ℝ)
    (11786300853 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell686_rightExp :
    Real.exp (687 / 800 : ℝ) ≤ (5900521471 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (687 / 800 : ℝ) (51359963203 / 50000000000 : ℝ)
    (5900521471 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell686_denomUpper :
    Real.exp (18001099449643303 / 2500000000000000 : ℝ) ≤ (13400199486393 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18001099449643303 / 2500000000000000 : ℝ) (1252339927133
    / 1000000000000 : ℝ) (13400199486393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell686_denomLower :
    (663623528347 / 500000000 : ℝ) ≤ Real.exp (4494288871172247 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4494288871172247 / 625000000000000 : ℝ) (1251965158427 /
    1000000000000 : ℝ) (663623528347 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell686_product_lower :
    (4628468558672247 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (343 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell686_leftExp
    (by norm_num : (0 : ℝ) ≤ (11786300853 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell686_product_upper :
    Real.pi * Real.exp (687 / 800 : ℝ) ≤ (18537036949643303 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell686_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell686_endpointLower :
    (652734189 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (343 / 800 : ℝ) (687 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4628468558672247 / 625000000000000 : ℝ) (Real.pi * Real.exp (343 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell686_product_lower
  have hD : Real.exp (Real.pi * Real.exp (687 / 800 : ℝ) - (343 / 1600 : ℝ)) ≤
      (13400199486393 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell686_denomUpper
    linarith [hpThetaJensenCell686_product_upper]
  have hi : (1 / (13400199486393 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (687 / 800 : ℝ) - (343 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13400199486393 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13400199486393 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((343 / 1600 : ℝ) - Real.pi * Real.exp (687 / 800 : ℝ)) := by
    rw [show (343 / 1600 : ℝ) - Real.pi * Real.exp (687 / 800 : ℝ) =
      -(Real.pi * Real.exp (687 / 800 : ℝ) - (343 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (343 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (343 / 400 : ℝ)) := by
    have h := hpThetaJensenCell686_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13400199486393 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell686_endpointUpper :
    hpThetaJensenKernelEndpointUpper (343 / 800 : ℝ) (687 / 1600 : ℝ) ≤ (530092783 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (687 / 800 : ℝ)) (18537036949643303 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (687 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell686_product_upper
  have hD : (663623528347 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (343 / 400 : ℝ) - (687 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell686_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell686_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (343 / 400 : ℝ) - (687 / 3200 : ℝ)) ≤
      (1 / (663623528347 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (663623528347 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((687 / 3200 : ℝ) - Real.pi * Real.exp (343 / 400 : ℝ)) ≤
      (2 / (663623528347 / 500000000 : ℝ) : ℝ) := by
    rw [show (687 / 3200 : ℝ) - Real.pi * Real.exp (343 / 400 : ℝ) =
      -(Real.pi * Real.exp (343 / 400 : ℝ) - (687 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18537036949643303 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (18537036949643303 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell686_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (343 / 800 : ℝ) (687 / 1600 : ℝ)) :
    (652734189 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (530092783 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell686_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell686_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell687_leftExp :
    (11801042941 / 5000000000 : ℝ) ≤ Real.exp (687 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (687 / 800 : ℝ) (1027199264059 / 1000000000000 : ℝ)
    (11801042941 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell687_rightExp :
    Real.exp (43 / 50 : ℝ) ≤ (11815803469 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 50 : ℝ) (205447877963 / 200000000000 : ℝ)
    (11815803469 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell687_denomUpper :
    Real.exp (36047007967586117 / 5000000000000000 : ℝ) ≤ (1352082930063 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36047007967586117 / 5000000000000000 : ℝ) (1252690702407
    / 1000000000000 : ℝ) (1352082930063 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell687_denomLower :
    (13391795361949 / 10000000000 : ℝ) ≤ Real.exp (4499882761887759 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4499882761887759 / 625000000000000 : ℝ) (250463075043 /
    200000000000 : ℝ) (13391795361949 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell687_product_lower :
    (4634257761887759 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (687 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell687_leftExp
    (by norm_num : (0 : ℝ) ≤ (11801042941 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell687_product_upper :
    Real.pi * Real.exp (43 / 50 : ℝ) ≤ (37120445467586117 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell687_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell687_endpointLower :
    (20759543 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (687 / 1600 : ℝ) (43 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4634257761887759 / 625000000000000 : ℝ) (Real.pi * Real.exp (687 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell687_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 50 : ℝ) - (687 / 3200 : ℝ)) ≤
      (1352082930063 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell687_denomUpper
    linarith [hpThetaJensenCell687_product_upper]
  have hi : (1 / (1352082930063 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 50 : ℝ) - (687 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1352082930063 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1352082930063 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((687 / 3200 : ℝ) - Real.pi * Real.exp (43 / 50 : ℝ)) := by
    rw [show (687 / 3200 : ℝ) - Real.pi * Real.exp (43 / 50 : ℝ) =
      -(Real.pi * Real.exp (43 / 50 : ℝ) - (687 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (687 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (687 / 800 : ℝ)) := by
    have h := hpThetaJensenCell687_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1352082930063 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell687_endpointUpper :
    hpThetaJensenKernelEndpointUpper (687 / 1600 : ℝ) (43 / 100 : ℝ) ≤ (16464107 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 50 : ℝ)) (37120445467586117 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell687_product_upper
  have hD : (13391795361949 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (687 / 800 : ℝ) - (43 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell687_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell687_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (687 / 800 : ℝ) - (43 / 200 : ℝ)) ≤
      (1 / (13391795361949 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13391795361949 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 200 : ℝ) - Real.pi * Real.exp (687 / 800 : ℝ)) ≤
      (2 / (13391795361949 / 10000000000 : ℝ) : ℝ) := by
    rw [show (43 / 200 : ℝ) - Real.pi * Real.exp (687 / 800 : ℝ) =
      -(Real.pi * Real.exp (687 / 800 : ℝ) - (43 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37120445467586117 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (37120445467586117 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell687_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (687 / 1600 : ℝ) (43 / 100 : ℝ)) :
    (20759543 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16464107 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell687_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell687_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell688_leftExp :
    (2953950867 / 1250000000 : ℝ) ≤ Real.exp (43 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 50 : ℝ) (513619694907 / 500000000000 : ℝ)
    (2953950867 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell688_rightExp :
    Real.exp (689 / 800 : ℝ) ≤ (5915291229 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (689 / 800 : ℝ) (1027279517137 / 1000000000000 : ℝ)
    (5915291229 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell688_denomUpper :
    Real.exp (18045937517987797 / 2500000000000000 : ℝ) ≤ (13642703290431 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18045937517987797 / 2500000000000000 : ℝ) (1253042030161
    / 1000000000000 : ℝ) (13642703290431 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell688_denomLower :
    (84452184261 / 62500000 : ℝ) ≤ Real.exp (1126370973395033 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1126370973395033 / 156250000000000 : ℝ) (1252666143497 /
    1000000000000 : ℝ) (84452184261 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell688_product_lower :
    (1160013551520033 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell688_leftExp
    (by norm_num : (0 : ℝ) ≤ (2953950867 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell688_product_upper :
    Real.pi * Real.exp (689 / 800 : ℝ) ≤ (18583437517987797 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell688_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell688_endpointLower :
    (257901577 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 100 : ℝ) (689 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1160013551520033 / 156250000000000 : ℝ) (Real.pi * Real.exp (43 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell688_product_lower
  have hD : Real.exp (Real.pi * Real.exp (689 / 800 : ℝ) - (43 / 200 : ℝ)) ≤
      (13642703290431 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell688_denomUpper
    linarith [hpThetaJensenCell688_product_upper]
  have hi : (1 / (13642703290431 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (689 / 800 : ℝ) - (43 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13642703290431 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13642703290431 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 200 : ℝ) - Real.pi * Real.exp (689 / 800 : ℝ)) := by
    rw [show (43 / 200 : ℝ) - Real.pi * Real.exp (689 / 800 : ℝ) =
      -(Real.pi * Real.exp (689 / 800 : ℝ) - (43 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 50 : ℝ)) := by
    have h := hpThetaJensenCell688_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13642703290431 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell688_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 100 : ℝ) (689 / 1600 : ℝ) ≤ (2618117793 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (689 / 800 : ℝ)) (18583437517987797 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (689 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell688_product_upper
  have hD : (84452184261 / 62500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 50 : ℝ) - (689 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell688_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell688_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 50 : ℝ) - (689 / 3200 : ℝ)) ≤
      (1 / (84452184261 / 62500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (84452184261 / 62500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((689 / 3200 : ℝ) - Real.pi * Real.exp (43 / 50 : ℝ)) ≤
      (2 / (84452184261 / 62500000 : ℝ) : ℝ) := by
    rw [show (689 / 3200 : ℝ) - Real.pi * Real.exp (43 / 50 : ℝ) =
      -(Real.pi * Real.exp (43 / 50 : ℝ) - (689 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18583437517987797 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (18583437517987797 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell688_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 100 : ℝ) (689 / 1600 : ℝ)) :
    (257901577 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2618117793 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell688_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell688_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell689_leftExp :
    (4732232983 / 2000000000 : ℝ) ≤ Real.exp (689 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (689 / 800 : ℝ) (64204969821 / 62500000000 : ℝ)
    (4732232983 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell689_rightExp :
    Real.exp (69 / 80 : ℝ) ≤ (11845379933 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 80 : ℝ) (1027319646027 / 1000000000000 : ℝ)
    (11845379933 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell689_denomUpper :
    Real.exp (36136800179853269 / 5000000000000000 : ℝ) ≤ (137658357179 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36136800179853269 / 5000000000000000 : ℝ) (626696955697
    / 500000000000 : ℝ) (137658357179 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell689_denomLower :
    (13634147000259 / 10000000000 : ℝ) ≤ Real.exp (1804436910191117 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1804436910191117 / 250000000000000 : ℝ) (62650873213 /
    50000000000 : ℝ) (13634147000259 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell689_product_lower :
    (1858343160191117 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (689 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell689_leftExp
    (by norm_num : (0 : ℝ) ≤ (4732232983 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell689_product_upper :
    Real.pi * Real.exp (69 / 80 : ℝ) ≤ (37213362679853269 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell689_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell689_endpointLower :
    (128157769 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (689 / 1600 : ℝ) (69 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1858343160191117 / 250000000000000 : ℝ) (Real.pi * Real.exp (689 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell689_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 80 : ℝ) - (689 / 3200 : ℝ)) ≤
      (137658357179 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell689_denomUpper
    linarith [hpThetaJensenCell689_product_upper]
  have hi : (1 / (137658357179 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 80 : ℝ) - (689 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (137658357179 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (137658357179 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((689 / 3200 : ℝ) - Real.pi * Real.exp (69 / 80 : ℝ)) := by
    rw [show (689 / 3200 : ℝ) - Real.pi * Real.exp (69 / 80 : ℝ) =
      -(Real.pi * Real.exp (69 / 80 : ℝ) - (689 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (689 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (689 / 800 : ℝ)) := by
    have h := hpThetaJensenCell689_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (137658357179 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell689_endpointUpper :
    hpThetaJensenKernelEndpointUpper (689 / 1600 : ℝ) (69 / 160 : ℝ) ≤ (20816367 / 80000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 80 : ℝ)) (37213362679853269 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell689_product_upper
  have hD : (13634147000259 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (689 / 800 : ℝ) - (69 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell689_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell689_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (689 / 800 : ℝ) - (69 / 320 : ℝ)) ≤
      (1 / (13634147000259 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13634147000259 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 320 : ℝ) - Real.pi * Real.exp (689 / 800 : ℝ)) ≤
      (2 / (13634147000259 / 10000000000 : ℝ) : ℝ) := by
    rw [show (69 / 320 : ℝ) - Real.pi * Real.exp (689 / 800 : ℝ) =
      -(Real.pi * Real.exp (689 / 800 : ℝ) - (69 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37213362679853269 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (37213362679853269 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell689_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (689 / 1600 : ℝ) (69 / 160 : ℝ)) :
    (128157769 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (20816367 / 80000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell689_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell689_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell690_leftExp :
    (2961344983 / 1250000000 : ℝ) ≤ Real.exp (69 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 80 : ℝ) (513659823013 / 500000000000 : ℝ)
    (2961344983 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell690_rightExp :
    Real.exp (691 / 800 : ℝ) ≤ (23720391831 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (691 / 800 : ℝ) (256839944121 / 250000000000 : ℝ)
    (23720391831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell690_denomUpper :
    Real.exp (72363566933526783 / 10000000000000000 : ℝ) ≤ (13890241001973 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (72363566933526783 / 10000000000000000 : ℝ) (626873173523
    / 500000000000 : ℝ) (13890241001973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell690_denomLower :
    (13757202157713 / 10000000000 : ℝ) ≤ Real.exp (1129176979104117 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1129176979104117 / 156250000000000 : ℝ) (626684669233 /
    500000000000 : ℝ) (13757202157713 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell690_product_lower :
    (1162917213479117 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell690_leftExp
    (by norm_num : (0 : ℝ) ≤ (2961344983 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell690_product_upper :
    Real.pi * Real.exp (691 / 800 : ℝ) ≤ (74519816933526783 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell690_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell690_endpointLower :
    (636840411 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 160 : ℝ) (691 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1162917213479117 / 156250000000000 : ℝ) (Real.pi * Real.exp (69 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell690_product_lower
  have hD : Real.exp (Real.pi * Real.exp (691 / 800 : ℝ) - (69 / 320 : ℝ)) ≤
      (13890241001973 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell690_denomUpper
    linarith [hpThetaJensenCell690_product_upper]
  have hi : (1 / (13890241001973 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (691 / 800 : ℝ) - (69 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13890241001973 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13890241001973 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 320 : ℝ) - Real.pi * Real.exp (691 / 800 : ℝ)) := by
    rw [show (69 / 320 : ℝ) - Real.pi * Real.exp (691 / 800 : ℝ) =
      -(Real.pi * Real.exp (691 / 800 : ℝ) - (69 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 80 : ℝ)) := by
    have h := hpThetaJensenCell690_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13890241001973 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell690_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 160 : ℝ) (691 / 1600 : ℝ) ≤ (1293020653 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (691 / 800 : ℝ)) (74519816933526783 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (691 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell690_product_upper
  have hD : (13757202157713 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 80 : ℝ) - (691 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell690_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell690_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 80 : ℝ) - (691 / 3200 : ℝ)) ≤
      (1 / (13757202157713 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13757202157713 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((691 / 3200 : ℝ) - Real.pi * Real.exp (69 / 80 : ℝ)) ≤
      (2 / (13757202157713 / 10000000000 : ℝ) : ℝ) := by
    rw [show (691 / 3200 : ℝ) - Real.pi * Real.exp (69 / 80 : ℝ) =
      -(Real.pi * Real.exp (69 / 80 : ℝ) - (691 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (74519816933526783 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (74519816933526783 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell690_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 160 : ℝ) (691 / 1600 : ℝ)) :
    (636840411 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1293020653 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell690_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell690_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell691_leftExp :
    (2372039183 / 1000000000 : ℝ) ≤ Real.exp (691 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (691 / 800 : ℝ) (1027359776483 / 1000000000000 : ℝ)
    (2372039183 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell691_rightExp :
    Real.exp (173 / 200 : ℝ) ≤ (1187503043 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (173 / 200 : ℝ) (1027399908509 / 1000000000000 : ℝ)
    (1187503043 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell691_denomUpper :
    Real.exp (3622682497367499 / 500000000000000 : ℝ) ≤ (7007966884261 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3622682497367499 / 500000000000000 : ℝ) (627049669067 /
    500000000000 : ℝ) (7007966884261 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell691_denomLower :
    (13881529381497 / 10000000000 : ℝ) ≤ Real.exp (904466165124917 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (904466165124917 / 125000000000000 : ℝ) (250744353421 /
    200000000000 : ℝ) (13881529381497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell691_product_lower :
    (931497415124917 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (691 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell691_leftExp
    (by norm_num : (0 : ℝ) ≤ (2372039183 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell691_product_upper :
    Real.pi * Real.exp (173 / 200 : ℝ) ≤ (3730651247367499 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell691_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell691_endpointLower :
    (1265817249 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (691 / 1600 : ℝ) (173 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (931497415124917 / 125000000000000 : ℝ) (Real.pi * Real.exp (691 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell691_product_lower
  have hD : Real.exp (Real.pi * Real.exp (173 / 200 : ℝ) - (691 / 3200 : ℝ)) ≤
      (7007966884261 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell691_denomUpper
    linarith [hpThetaJensenCell691_product_upper]
  have hi : (1 / (7007966884261 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (173 / 200 : ℝ) - (691 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7007966884261 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7007966884261 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((691 / 3200 : ℝ) - Real.pi * Real.exp (173 / 200 : ℝ)) := by
    rw [show (691 / 3200 : ℝ) - Real.pi * Real.exp (173 / 200 : ℝ) =
      -(Real.pi * Real.exp (173 / 200 : ℝ) - (691 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (691 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (691 / 800 : ℝ)) := by
    have h := hpThetaJensenCell691_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7007966884261 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell691_endpointUpper :
    hpThetaJensenKernelEndpointUpper (691 / 1600 : ℝ) (173 / 400 : ℝ) ≤ (2570104021 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (173 / 200 : ℝ)) (3730651247367499 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (173 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell691_product_upper
  have hD : (13881529381497 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (691 / 800 : ℝ) - (173 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell691_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell691_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (691 / 800 : ℝ) - (173 / 800 : ℝ)) ≤
      (1 / (13881529381497 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13881529381497 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((173 / 800 : ℝ) - Real.pi * Real.exp (691 / 800 : ℝ)) ≤
      (2 / (13881529381497 / 10000000000 : ℝ) : ℝ) := by
    rw [show (173 / 800 : ℝ) - Real.pi * Real.exp (691 / 800 : ℝ) =
      -(Real.pi * Real.exp (691 / 800 : ℝ) - (173 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3730651247367499 / 500000000000000 : ℝ) ^ 2 - 6 *
      (3730651247367499 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell691_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (691 / 1600 : ℝ) (173 / 400 : ℝ)) :
    (1265817249 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2570104021 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell691_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell691_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell692_leftExp :
    (23750060859 / 10000000000 : ℝ) ≤ Real.exp (173 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (173 / 200 : ℝ) (256849977127 / 250000000000 : ℝ)
    (23750060859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell692_rightExp :
    Real.exp (693 / 800 : ℝ) ≤ (23779766999 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (693 / 800 : ℝ) (513720021051 / 500000000000 : ℝ)
    (23779766999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell692_denomUpper :
    Real.exp (72543849545689407 / 10000000000000000 : ℝ) ≤ (14142928812101 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (72543849545689407 / 10000000000000000 : ℝ) (313613221409
    / 250000000000 : ℝ) (14142928812101 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell692_denomLower :
    (7003571637477 / 5000000000 : ℝ) ≤ Real.exp (9055922024268441 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9055922024268441 / 1250000000000000 : ℝ) (313518687789 /
    250000000000 : ℝ) (7003571637477 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell692_product_lower :
    (9326625149268441 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (173 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell692_leftExp
    (by norm_num : (0 : ℝ) ≤ (23750060859 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell692_product_upper :
    Real.pi * Real.exp (693 / 800 : ℝ) ≤ (74706349545689407 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell692_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell692_endpointLower :
    (628993469 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (173 / 400 : ℝ) (693 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9326625149268441 / 1250000000000000 : ℝ) (Real.pi * Real.exp (173 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell692_product_lower
  have hD : Real.exp (Real.pi * Real.exp (693 / 800 : ℝ) - (173 / 800 : ℝ)) ≤
      (14142928812101 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell692_denomUpper
    linarith [hpThetaJensenCell692_product_upper]
  have hi : (1 / (14142928812101 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (693 / 800 : ℝ) - (173 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14142928812101 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14142928812101 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((173 / 800 : ℝ) - Real.pi * Real.exp (693 / 800 : ℝ)) := by
    rw [show (173 / 800 : ℝ) - Real.pi * Real.exp (693 / 800 : ℝ) =
      -(Real.pi * Real.exp (693 / 800 : ℝ) - (173 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (173 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (173 / 200 : ℝ)) := by
    have h := hpThetaJensenCell692_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14142928812101 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell692_endpointUpper :
    hpThetaJensenKernelEndpointUpper (173 / 400 : ℝ) (693 / 1600 : ℝ) ≤ (638558489 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (693 / 800 : ℝ)) (74706349545689407 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (693 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell692_product_upper
  have hD : (7003571637477 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (173 / 200 : ℝ) - (693 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell692_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell692_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (173 / 200 : ℝ) - (693 / 3200 : ℝ)) ≤
      (1 / (7003571637477 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7003571637477 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((693 / 3200 : ℝ) - Real.pi * Real.exp (173 / 200 : ℝ)) ≤
      (2 / (7003571637477 / 5000000000 : ℝ) : ℝ) := by
    rw [show (693 / 3200 : ℝ) - Real.pi * Real.exp (173 / 200 : ℝ) =
      -(Real.pi * Real.exp (173 / 200 : ℝ) - (693 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (74706349545689407 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (74706349545689407 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell692_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (173 / 400 : ℝ) (693 / 1600 : ℝ)) :
    (628993469 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (638558489 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell692_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell692_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell693_leftExp :
    (23779766997 / 10000000000 : ℝ) ≤ Real.exp (693 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (693 / 800 : ℝ) (1027440042101 / 1000000000000 : ℝ)
    (23779766997 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell693_rightExp :
    Real.exp (347 / 400 : ℝ) ≤ (11904755147 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (347 / 400 : ℝ) (1027480177263 / 1000000000000 : ℝ)
    (11904755147 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell693_denomUpper :
    Real.exp (36317082936529171 / 5000000000000000 : ℝ) ≤ (3567810278447 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36317082936529171 / 5000000000000000 : ℝ) (250961398107
    / 200000000000 : ℝ) (3567810278447 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell693_denomLower :
    (14134058623593 / 10000000000 : ℝ) ≤ Real.exp (9067196969954903 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9067196969954903 / 1250000000000000 : ℝ) (627214145799 /
    500000000000 : ℝ) (14134058623593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell693_product_lower :
    (9338290719954903 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (693 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell693_leftExp
    (by norm_num : (0 : ℝ) ≤ (23779766997 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell693_product_upper :
    Real.pi * Real.exp (347 / 400 : ℝ) ≤ (37399895436529171 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell693_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell693_endpointLower :
    (1250189857 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (693 / 1600 : ℝ) (347 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9338290719954903 / 1250000000000000 : ℝ) (Real.pi * Real.exp (693 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell693_product_lower
  have hD : Real.exp (Real.pi * Real.exp (347 / 400 : ℝ) - (693 / 3200 : ℝ)) ≤
      (3567810278447 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell693_denomUpper
    linarith [hpThetaJensenCell693_product_upper]
  have hi : (1 / (3567810278447 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (347 / 400 : ℝ) - (693 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3567810278447 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3567810278447 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((693 / 3200 : ℝ) - Real.pi * Real.exp (347 / 400 : ℝ)) := by
    rw [show (693 / 3200 : ℝ) - Real.pi * Real.exp (347 / 400 : ℝ) =
      -(Real.pi * Real.exp (347 / 400 : ℝ) - (693 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (693 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (693 / 800 : ℝ)) := by
    have h := hpThetaJensenCell693_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3567810278447 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell693_endpointUpper :
    hpThetaJensenKernelEndpointUpper (693 / 1600 : ℝ) (347 / 800 : ℝ) ≤ (317303881 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (347 / 400 : ℝ)) (37399895436529171 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (347 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell693_product_upper
  have hD : (14134058623593 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (693 / 800 : ℝ) - (347 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell693_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell693_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (693 / 800 : ℝ) - (347 / 1600 : ℝ)) ≤
      (1 / (14134058623593 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14134058623593 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((347 / 1600 : ℝ) - Real.pi * Real.exp (693 / 800 : ℝ)) ≤
      (2 / (14134058623593 / 10000000000 : ℝ) : ℝ) := by
    rw [show (347 / 1600 : ℝ) - Real.pi * Real.exp (693 / 800 : ℝ) =
      -(Real.pi * Real.exp (693 / 800 : ℝ) - (347 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37399895436529171 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (37399895436529171 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell693_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (693 / 1600 : ℝ) (347 / 800 : ℝ)) :
    (1250189857 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (317303881 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell693_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell693_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell694_leftExp :
    (5952377573 / 2500000000 : ℝ) ≤ Real.exp (347 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (347 / 400 : ℝ) (513740088631 / 500000000000 : ℝ)
    (5952377573 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell694_rightExp :
    Real.exp (139 / 160 : ℝ) ≤ (2383929079 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (139 / 160 : ℝ) (1027520313991 / 1000000000000 : ℝ)
    (2383929079 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell694_denomUpper :
    Real.exp (7272459907082847 / 1000000000000000 : ℝ) ≤ (7200442918199 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7272459907082847 / 1000000000000000 : ℝ) (1255161653799
    / 1000000000000 : ℝ) (7200442918199 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell694_denomLower :
    (891393150459 / 625000000 : ℝ) ≤ Real.exp (2269621626789527 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2269621626789527 / 312500000000000 : ℝ) (1254782389437 /
    1000000000000 : ℝ) (891393150459 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell694_product_lower :
    (2337492720539527 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (347 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell694_leftExp
    (by norm_num : (0 : ℝ) ≤ (5952377573 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell694_product_upper :
    Real.pi * Real.exp (139 / 160 : ℝ) ≤ (7489334907082847 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell694_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell694_endpointLower :
    (310606493 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (347 / 800 : ℝ) (139 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2337492720539527 / 312500000000000 : ℝ) (Real.pi * Real.exp (347 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell694_product_lower
  have hD : Real.exp (Real.pi * Real.exp (139 / 160 : ℝ) - (347 / 1600 : ℝ)) ≤
      (7200442918199 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell694_denomUpper
    linarith [hpThetaJensenCell694_product_upper]
  have hi : (1 / (7200442918199 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (139 / 160 : ℝ) - (347 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7200442918199 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7200442918199 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((347 / 1600 : ℝ) - Real.pi * Real.exp (139 / 160 : ℝ)) := by
    rw [show (347 / 1600 : ℝ) - Real.pi * Real.exp (139 / 160 : ℝ) =
      -(Real.pi * Real.exp (139 / 160 : ℝ) - (347 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (347 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (347 / 400 : ℝ)) := by
    have h := hpThetaJensenCell694_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7200442918199 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell694_endpointUpper :
    hpThetaJensenKernelEndpointUpper (347 / 800 : ℝ) (139 / 320 : ℝ) ≤ (100907809 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (139 / 160 : ℝ)) (7489334907082847 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (139 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell694_product_upper
  have hD : (891393150459 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (347 / 400 : ℝ) - (139 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell694_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell694_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (347 / 400 : ℝ) - (139 / 640 : ℝ)) ≤
      (1 / (891393150459 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (891393150459 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((139 / 640 : ℝ) - Real.pi * Real.exp (347 / 400 : ℝ)) ≤
      (2 / (891393150459 / 625000000 : ℝ) : ℝ) := by
    rw [show (139 / 640 : ℝ) - Real.pi * Real.exp (347 / 400 : ℝ) =
      -(Real.pi * Real.exp (347 / 400 : ℝ) - (139 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7489334907082847 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (7489334907082847 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell694_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (347 / 800 : ℝ) (139 / 320 : ℝ)) :
    (310606493 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (100907809 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell694_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell694_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell695_leftExp :
    (23839290789 / 10000000000 : ℝ) ≤ Real.exp (139 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (139 / 160 : ℝ) (102752031399 / 100000000000 : ℝ)
    (23839290789 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell695_rightExp :
    Real.exp (87 / 100 : ℝ) ≤ (2983638567 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87 / 100 : ℝ) (1027560452287 / 1000000000000 : ℝ)
    (2983638567 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell695_denomUpper :
    Real.exp (9101893661617231 / 1250000000000000 : ℝ) ≤ (1453187835267 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9101893661617231 / 1250000000000000 : ℝ) (1255516876451
    / 1000000000000 : ℝ) (1453187835267 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell695_denomLower :
    (14391853780713 / 10000000000 : ℝ) ≤ Real.exp (9089790653549511 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9089790653549511 / 1250000000000000 : ℝ) (313784261411 /
    250000000000 : ℝ) (14391853780713 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell695_product_lower :
    (9361665653549511 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (139 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell695_leftExp
    (by norm_num : (0 : ℝ) ≤ (23839290789 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell695_product_upper :
    Real.pi * Real.exp (87 / 100 : ℝ) ≤ (9373378036617231 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell695_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell695_endpointLower :
    (493878099 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (139 / 320 : ℝ) (87 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9361665653549511 / 1250000000000000 : ℝ) (Real.pi * Real.exp (139 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell695_product_lower
  have hD : Real.exp (Real.pi * Real.exp (87 / 100 : ℝ) - (139 / 640 : ℝ)) ≤
      (1453187835267 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell695_denomUpper
    linarith [hpThetaJensenCell695_product_upper]
  have hi : (1 / (1453187835267 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (87 / 100 : ℝ) - (139 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1453187835267 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1453187835267 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((139 / 640 : ℝ) - Real.pi * Real.exp (87 / 100 : ℝ)) := by
    rw [show (139 / 640 : ℝ) - Real.pi * Real.exp (87 / 100 : ℝ) =
      -(Real.pi * Real.exp (87 / 100 : ℝ) - (139 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (139 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (139 / 160 : ℝ)) := by
    have h := hpThetaJensenCell695_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1453187835267 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell695_endpointUpper :
    hpThetaJensenKernelEndpointUpper (139 / 320 : ℝ) (87 / 200 : ℝ) ≤ (2507026423 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (87 / 100 : ℝ)) (9373378036617231 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (87 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell695_product_upper
  have hD : (14391853780713 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (139 / 160 : ℝ) - (87 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell695_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell695_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (139 / 160 : ℝ) - (87 / 400 : ℝ)) ≤
      (1 / (14391853780713 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14391853780713 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((87 / 400 : ℝ) - Real.pi * Real.exp (139 / 160 : ℝ)) ≤
      (2 / (14391853780713 / 10000000000 : ℝ) : ℝ) := by
    rw [show (87 / 400 : ℝ) - Real.pi * Real.exp (139 / 160 : ℝ) =
      -(Real.pi * Real.exp (139 / 160 : ℝ) - (87 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9373378036617231 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (9373378036617231 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell695_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (139 / 320 : ℝ) (87 / 200 : ℝ)) :
    (493878099 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2507026423 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell695_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell695_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell696_leftExp :
    (11934554267 / 5000000000 : ℝ) ≤ Real.exp (87 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87 / 100 : ℝ) (513780226143 / 500000000000 : ℝ)
    (11934554267 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell696_rightExp :
    Real.exp (697 / 800 : ℝ) ≤ (23898963577 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (697 / 800 : ℝ) (1027600592151 / 1000000000000 : ℝ)
    (23898963577 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell696_denomUpper :
    Real.exp (72905816680758161 / 10000000000000000 : ℝ) ≤ (14664234208727 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (72905816680758161 / 10000000000000000 : ℝ) (627936329731
    / 500000000000 : ℝ) (14664234208727 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell696_denomLower :
    (14522764092121 / 10000000000 : ℝ) ≤ Real.exp (4550554713596633 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4550554713596633 / 625000000000000 : ℝ) (627746130601 /
    500000000000 : ℝ) (14522764092121 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell696_product_lower :
    (4686687526096633 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (87 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell696_leftExp
    (by norm_num : (0 : ℝ) ≤ (11934554267 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell696_product_upper :
    Real.pi * Real.exp (697 / 800 : ℝ) ≤ (75080816680758161 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell696_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell696_endpointLower :
    (1226997649 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 200 : ℝ) (697 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4686687526096633 / 625000000000000 : ℝ) (Real.pi * Real.exp (87 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell696_product_lower
  have hD : Real.exp (Real.pi * Real.exp (697 / 800 : ℝ) - (87 / 400 : ℝ)) ≤
      (14664234208727 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell696_denomUpper
    linarith [hpThetaJensenCell696_product_upper]
  have hi : (1 / (14664234208727 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (697 / 800 : ℝ) - (87 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14664234208727 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14664234208727 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((87 / 400 : ℝ) - Real.pi * Real.exp (697 / 800 : ℝ)) := by
    rw [show (87 / 400 : ℝ) - Real.pi * Real.exp (697 / 800 : ℝ) =
      -(Real.pi * Real.exp (697 / 800 : ℝ) - (87 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (87 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (87 / 100 : ℝ)) := by
    have h := hpThetaJensenCell696_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14664234208727 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell696_endpointUpper :
    hpThetaJensenKernelEndpointUpper (87 / 200 : ℝ) (697 / 1600 : ℝ) ≤ (249142457 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (697 / 800 : ℝ)) (75080816680758161 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (697 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell696_product_upper
  have hD : (14522764092121 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (87 / 100 : ℝ) - (697 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell696_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell696_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (87 / 100 : ℝ) - (697 / 3200 : ℝ)) ≤
      (1 / (14522764092121 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14522764092121 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((697 / 3200 : ℝ) - Real.pi * Real.exp (87 / 100 : ℝ)) ≤
      (2 / (14522764092121 / 10000000000 : ℝ) : ℝ) := by
    rw [show (697 / 3200 : ℝ) - Real.pi * Real.exp (87 / 100 : ℝ) =
      -(Real.pi * Real.exp (87 / 100 : ℝ) - (697 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (75080816680758161 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (75080816680758161 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell696_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (87 / 200 : ℝ) (697 / 1600 : ℝ)) :
    (1226997649 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (249142457 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell696_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell696_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell697_leftExp :
    (955958543 / 400000000 : ℝ) ≤ Real.exp (697 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (697 / 800 : ℝ) (20552011843 / 20000000000 : ℝ)
    (955958543 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell697_rightExp :
    Real.exp (349 / 400 : ℝ) ≤ (23928855961 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (349 / 400 : ℝ) (64227545849 / 62500000000 : ℝ)
    (23928855961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell697_denomUpper :
    Real.exp (72996601385085873 / 10000000000000000 : ℝ) ≤ (7398984580809 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (72996601385085873 / 10000000000000000 : ℝ) (628114501923
    / 500000000000 : ℝ) (7398984580809 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell697_denomLower :
    (14655036892247 / 10000000000 : ℝ) ≤ Real.exp (364497713877557 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (364497713877557 / 50000000000000 : ℝ) (1255848037121 /
    1000000000000 : ℝ) (14655036892247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell697_product_lower :
    (375403963877557 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (697 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell697_leftExp
    (by norm_num : (0 : ℝ) ≤ (955958543 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell697_product_upper :
    Real.pi * Real.exp (349 / 400 : ℝ) ≤ (75174726385085873 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell697_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell697_endpointLower :
    (60966657 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (697 / 1600 : ℝ) (349 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (375403963877557 / 50000000000000 : ℝ) (Real.pi * Real.exp (697 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell697_product_lower
  have hD : Real.exp (Real.pi * Real.exp (349 / 400 : ℝ) - (697 / 3200 : ℝ)) ≤
      (7398984580809 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell697_denomUpper
    linarith [hpThetaJensenCell697_product_upper]
  have hi : (1 / (7398984580809 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (349 / 400 : ℝ) - (697 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7398984580809 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7398984580809 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((697 / 3200 : ℝ) - Real.pi * Real.exp (349 / 400 : ℝ)) := by
    rw [show (697 / 3200 : ℝ) - Real.pi * Real.exp (349 / 400 : ℝ) =
      -(Real.pi * Real.exp (349 / 400 : ℝ) - (697 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (697 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (697 / 800 : ℝ)) := by
    have h := hpThetaJensenCell697_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7398984580809 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell697_endpointUpper :
    hpThetaJensenKernelEndpointUpper (697 / 1600 : ℝ) (349 / 800 : ℝ) ≤ (495177919 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (349 / 400 : ℝ)) (75174726385085873 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (349 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell697_product_upper
  have hD : (14655036892247 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (697 / 800 : ℝ) - (349 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell697_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell697_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (697 / 800 : ℝ) - (349 / 1600 : ℝ)) ≤
      (1 / (14655036892247 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14655036892247 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((349 / 1600 : ℝ) - Real.pi * Real.exp (697 / 800 : ℝ)) ≤
      (2 / (14655036892247 / 10000000000 : ℝ) : ℝ) := by
    rw [show (349 / 1600 : ℝ) - Real.pi * Real.exp (697 / 800 : ℝ) =
      -(Real.pi * Real.exp (697 / 800 : ℝ) - (349 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (75174726385085873 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (75174726385085873 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell697_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (697 / 1600 : ℝ) (349 / 800 : ℝ)) :
    (60966657 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (495177919 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell697_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell697_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell698_leftExp :
    (23928855959 / 10000000000 : ℝ) ≤ Real.exp (349 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (349 / 400 : ℝ) (1027640733583 / 1000000000000 : ℝ)
    (23928855959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell698_rightExp :
    Real.exp (699 / 800 : ℝ) ≤ (23958785733 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (699 / 800 : ℝ) (128460109573 / 125000000000 : ℝ)
    (23958785733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell698_denomUpper :
    Real.exp (73087503547292669 / 10000000000000000 : ℝ) ≤ (2986619830141 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73087503547292669 / 10000000000000000 : ℝ) (78536619411
    / 62500000000 : ℝ) (2986619830141 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell698_denomLower :
    (14788687923107 / 10000000000 : ℝ) ≤ Real.exp (9123790931243341 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9123790931243341 / 1250000000000000 : ℝ) (1256204374401
    / 1000000000000 : ℝ) (14788687923107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell698_product_lower :
    (9396837806243341 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (349 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell698_leftExp
    (by norm_num : (0 : ℝ) ≤ (23928855959 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell698_product_upper :
    Real.pi * Real.exp (699 / 800 : ℝ) ≤ (75268753547292669 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell698_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell698_endpointLower :
    (242340337 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (349 / 800 : ℝ) (699 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9396837806243341 / 1250000000000000 : ℝ) (Real.pi * Real.exp (349 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell698_product_lower
  have hD : Real.exp (Real.pi * Real.exp (699 / 800 : ℝ) - (349 / 1600 : ℝ)) ≤
      (2986619830141 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell698_denomUpper
    linarith [hpThetaJensenCell698_product_upper]
  have hi : (1 / (2986619830141 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (699 / 800 : ℝ) - (349 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2986619830141 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2986619830141 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((349 / 1600 : ℝ) - Real.pi * Real.exp (699 / 800 : ℝ)) := by
    rw [show (349 / 1600 : ℝ) - Real.pi * Real.exp (699 / 800 : ℝ) =
      -(Real.pi * Real.exp (699 / 800 : ℝ) - (349 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (349 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (349 / 400 : ℝ)) := by
    have h := hpThetaJensenCell698_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2986619830141 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell698_endpointUpper :
    hpThetaJensenKernelEndpointUpper (349 / 800 : ℝ) (699 / 1600 : ℝ) ≤ (2460421423 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (699 / 800 : ℝ)) (75268753547292669 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (699 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell698_product_upper
  have hD : (14788687923107 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (349 / 400 : ℝ) - (699 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell698_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell698_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (349 / 400 : ℝ) - (699 / 3200 : ℝ)) ≤
      (1 / (14788687923107 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14788687923107 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((699 / 3200 : ℝ) - Real.pi * Real.exp (349 / 400 : ℝ)) ≤
      (2 / (14788687923107 / 10000000000 : ℝ) : ℝ) := by
    rw [show (699 / 3200 : ℝ) - Real.pi * Real.exp (349 / 400 : ℝ) =
      -(Real.pi * Real.exp (349 / 400 : ℝ) - (699 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (75268753547292669 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (75268753547292669 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell698_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (349 / 800 : ℝ) (699 / 1600 : ℝ)) :
    (242340337 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2460421423 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell698_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell698_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell699_leftExp :
    (23958785731 / 10000000000 : ℝ) ≤ Real.exp (699 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (699 / 800 : ℝ) (1027680876583 / 1000000000000 : ℝ)
    (23958785731 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell699_rightExp :
    Real.exp (7 / 8 : ℝ) ≤ (1199437647 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 8 : ℝ) (32116281911 / 31250000000 : ℝ)
    (1199437647 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell699_denomUpper :
    Real.exp (3658926165751671 / 500000000000000 : ℝ) ≤ (7534820163437 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3658926165751671 / 500000000000000 : ℝ) (251388676131 /
    200000000000 : ℝ) (7534820163437 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell699_denomLower :
    (1492373311443 / 1000000000 : ℝ) ≤ Real.exp (9135153697777969 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9135153697777969 / 1250000000000000 : ℝ) (39267539813 /
    31250000000 : ℝ) (1492373311443 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell699_product_lower :
    (9408591197777969 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (699 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell699_leftExp
    (by norm_num : (0 : ℝ) ≤ (23958785731 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell699_product_upper :
    Real.pi * Real.exp (7 / 8 : ℝ) ≤ (3768144915751671 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell699_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell699_endpointLower :
    (602051623 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (699 / 1600 : ℝ) (7 / 16 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9408591197777969 / 1250000000000000 : ℝ) (Real.pi * Real.exp (699 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell699_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 8 : ℝ) - (699 / 3200 : ℝ)) ≤
      (7534820163437 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell699_denomUpper
    linarith [hpThetaJensenCell699_product_upper]
  have hi : (1 / (7534820163437 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 8 : ℝ) - (699 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7534820163437 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7534820163437 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((699 / 3200 : ℝ) - Real.pi * Real.exp (7 / 8 : ℝ)) := by
    rw [show (699 / 3200 : ℝ) - Real.pi * Real.exp (7 / 8 : ℝ) =
      -(Real.pi * Real.exp (7 / 8 : ℝ) - (699 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (699 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (699 / 800 : ℝ)) := by
    have h := hpThetaJensenCell699_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7534820163437 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell699_endpointUpper :
    hpThetaJensenKernelEndpointUpper (699 / 1600 : ℝ) (7 / 16 : ℝ) ≤ (152813749 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 8 : ℝ)) (3768144915751671 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 16 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell699_product_upper
  have hD : (1492373311443 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (699 / 800 : ℝ) - (7 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell699_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell699_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (699 / 800 : ℝ) - (7 / 32 : ℝ)) ≤
      (1 / (1492373311443 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1492373311443 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 32 : ℝ) - Real.pi * Real.exp (699 / 800 : ℝ)) ≤
      (2 / (1492373311443 / 1000000000 : ℝ) : ℝ) := by
    rw [show (7 / 32 : ℝ) - Real.pi * Real.exp (699 / 800 : ℝ) =
      -(Real.pi * Real.exp (699 / 800 : ℝ) - (7 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3768144915751671 / 500000000000000 : ℝ) ^ 2 - 6 *
      (3768144915751671 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell699_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (699 / 1600 : ℝ) (7 / 16 : ℝ)) :
    (602051623 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (152813749 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell699_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell699_endpointUpper

def hpThetaJensenCellsBatch034Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2708305539 / 10000000000 : ℝ)
  | 1 => (538381963 / 2000000000 : ℝ)
  | 2 => (1337790599 / 5000000000 : ℝ)
  | 3 => (1329659819 / 5000000000 : ℝ)
  | 4 => (2643125081 / 10000000000 : ℝ)
  | 5 => (82093671 / 312500000 : ℝ)
  | 6 => (652734189 / 2500000000 : ℝ)
  | 7 => (20759543 / 80000000 : ℝ)
  | 8 => (257901577 / 1000000000 : ℝ)
  | 9 => (128157769 / 500000000 : ℝ)
  | 10 => (636840411 / 2500000000 : ℝ)
  | 11 => (1265817249 / 5000000000 : ℝ)
  | 12 => (628993469 / 2500000000 : ℝ)
  | 13 => (1250189857 / 5000000000 : ℝ)
  | 14 => (310606493 / 1250000000 : ℝ)
  | 15 => (493878099 / 2000000000 : ℝ)
  | 16 => (1226997649 / 5000000000 : ℝ)
  | 17 => (60966657 / 250000000 : ℝ)
  | 18 => (242340337 / 1000000000 : ℝ)
  | 19 => (602051623 / 2500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch034Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1374562349 / 5000000000 : ℝ)
  | 1 => (546502383 / 2000000000 : ℝ)
  | 2 => (271596693 / 1000000000 : ℝ)
  | 3 => (269948969 / 1000000000 : ℝ)
  | 4 => (167692509 / 625000000 : ℝ)
  | 5 => (2666738237 / 10000000000 : ℝ)
  | 6 => (530092783 / 2000000000 : ℝ)
  | 7 => (16464107 / 62500000 : ℝ)
  | 8 => (2618117793 / 10000000000 : ℝ)
  | 9 => (20816367 / 80000000 : ℝ)
  | 10 => (1293020653 / 5000000000 : ℝ)
  | 11 => (2570104021 / 10000000000 : ℝ)
  | 12 => (638558489 / 2500000000 : ℝ)
  | 13 => (317303881 / 1250000000 : ℝ)
  | 14 => (100907809 / 400000000 : ℝ)
  | 15 => (2507026423 / 10000000000 : ℝ)
  | 16 => (249142457 / 1000000000 : ℝ)
  | 17 => (495177919 / 2000000000 : ℝ)
  | 18 => (2460421423 / 10000000000 : ℝ)
  | 19 => (152813749 / 625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch034_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch034Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch034Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell680_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell681_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell682_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell683_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell684_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell685_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell686_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell687_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell688_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell689_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell690_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell691_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell692_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell693_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell694_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell695_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell696_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell697_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell698_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell699_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper] at h ⊢
    exact h

end HodgeProofHP
