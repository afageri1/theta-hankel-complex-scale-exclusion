import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1500_leftExp :
    (32604095601 / 5000000000 : ℝ) ≤ Real.exp (15 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15 / 8 : ℝ) (1060344388321 / 1000000000000 : ℝ)
    (32604095601 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1500_rightExp :
    Real.exp (1501 / 800 : ℝ) ≤ (6528975241 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1501 / 800 : ℝ) (530192904417 / 500000000000 : ℝ)
    (6528975241 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1500_denomUpper :
    Real.exp (20042632914298913 / 1000000000000000 : ℝ) ≤ (1012592888906902897 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (20042632914298913 / 1000000000000000 : ℝ) (935368320131
    / 500000000000 : ℝ) (1012592888906902897 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1500_denomLower :
    (2466654445031324789 / 5000000000 : ℝ) ≤ Real.exp (12510431675917099 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12510431675917099 / 625000000000000 : ℝ) (934610329207 /
    500000000000 : ℝ) (2466654445031324789 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1500_product_lower :
    (12803595738417099 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (15 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1500_leftExp
    (by norm_num : (0 : ℝ) ≤ (32604095601 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1500_product_upper :
    Real.pi * Real.exp (1501 / 800 : ℝ) ≤ (20511382914298913 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1500_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1500_endpointLower :
    (3841 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (15 / 16 : ℝ) (1501 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12803595738417099 / 625000000000000 : ℝ) (Real.pi * Real.exp (15 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell1500_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1501 / 800 : ℝ) - (15 / 32 : ℝ)) ≤
      (1012592888906902897 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1500_denomUpper
    linarith [hpThetaJensenCell1500_product_upper]
  have hi : (1 / (1012592888906902897 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1501 / 800 : ℝ) - (15 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1012592888906902897 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1012592888906902897 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((15 / 32 : ℝ) - Real.pi * Real.exp (1501 / 800 : ℝ)) := by
    rw [show (15 / 32 : ℝ) - Real.pi * Real.exp (1501 / 800 : ℝ) =
      -(Real.pi * Real.exp (1501 / 800 : ℝ) - (15 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (15 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (15 / 8 : ℝ)) := by
    have h := hpThetaJensenCell1500_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1012592888906902897 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1500_endpointUpper :
    hpThetaJensenKernelEndpointUpper (15 / 16 : ℝ) (1501 / 1600 : ℝ) ≤ (31701 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1501 / 800 : ℝ)) (20511382914298913 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1501 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1500_product_upper
  have hD : (2466654445031324789 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (15 / 8 : ℝ) - (1501 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1500_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1500_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (15 / 8 : ℝ) - (1501 / 3200 : ℝ)) ≤
      (1 / (2466654445031324789 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2466654445031324789 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1501 / 3200 : ℝ) - Real.pi * Real.exp (15 / 8 : ℝ)) ≤
      (2 / (2466654445031324789 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1501 / 3200 : ℝ) - Real.pi * Real.exp (15 / 8 : ℝ) =
      -(Real.pi * Real.exp (15 / 8 : ℝ) - (1501 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20511382914298913 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (20511382914298913 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1500_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (15 / 16 : ℝ) (1501 / 1600 : ℝ)) :
    (3841 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (31701 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1500_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1500_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1501_leftExp :
    (65289752407 / 10000000000 : ℝ) ≤ Real.exp (1501 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1501 / 800 : ℝ) (1060385808833 / 1000000000000 : ℝ)
    (65289752407 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1501_rightExp :
    Real.exp (751 / 400 : ℝ) ≤ (16342853907 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (751 / 400 : ℝ) (1060427230963 / 1000000000000 : ℝ)
    (16342853907 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1501_denomUpper :
    Real.exp (50169939184253851 / 2500000000000000 : ℝ) ≤ (2596456807334045107 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (50169939184253851 / 2500000000000000 : ℝ) (234027347247
    / 125000000000 : ℝ) (2596456807334045107 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1501_denomLower :
    (2529884019831170731 / 5000000000 : ℝ) ≤ Real.exp (25052501730476493 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25052501730476493 / 1250000000000000 : ℝ) (37413994421 /
    20000000000 : ℝ) (2529884019831170731 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1501_product_lower :
    (25639220480476493 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1501 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1501_leftExp
    (by norm_num : (0 : ℝ) ≤ (65289752407 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1501_product_upper :
    Real.pi * Real.exp (751 / 400 : ℝ) ≤ (51342595434253851 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1501_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1501_endpointLower :
    (30037 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1501 / 1600 : ℝ) (751 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25639220480476493 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1501 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1501_product_lower
  have hD : Real.exp (Real.pi * Real.exp (751 / 400 : ℝ) - (1501 / 3200 : ℝ)) ≤
      (2596456807334045107 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1501_denomUpper
    linarith [hpThetaJensenCell1501_product_upper]
  have hi : (1 / (2596456807334045107 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (751 / 400 : ℝ) - (1501 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2596456807334045107 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2596456807334045107 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1501 / 3200 : ℝ) - Real.pi * Real.exp (751 / 400 : ℝ)) := by
    rw [show (1501 / 3200 : ℝ) - Real.pi * Real.exp (751 / 400 : ℝ) =
      -(Real.pi * Real.exp (751 / 400 : ℝ) - (1501 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1501 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1501 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1501_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2596456807334045107 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1501_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1501 / 1600 : ℝ) (751 / 800 : ℝ) ≤ (61979 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (751 / 400 : ℝ)) (51342595434253851 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (751 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1501_product_upper
  have hD : (2529884019831170731 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1501 / 800 : ℝ) - (751 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1501_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1501_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1501 / 800 : ℝ) - (751 / 1600 : ℝ)) ≤
      (1 / (2529884019831170731 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2529884019831170731 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((751 / 1600 : ℝ) - Real.pi * Real.exp (1501 / 800 : ℝ)) ≤
      (2 / (2529884019831170731 / 5000000000 : ℝ) : ℝ) := by
    rw [show (751 / 1600 : ℝ) - Real.pi * Real.exp (1501 / 800 : ℝ) =
      -(Real.pi * Real.exp (1501 / 800 : ℝ) - (751 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51342595434253851 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (51342595434253851 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1501_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1501 / 1600 : ℝ) (751 / 800 : ℝ)) :
    (30037 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (61979 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1501_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1501_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1502_leftExp :
    (20918853 / 3200000 : ℝ) ≤ Real.exp (751 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (751 / 400 : ℝ) (530213615481 / 500000000000 : ℝ)
    (20918853 / 3200000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1502_rightExp :
    Real.exp (1503 / 800 : ℝ) ≤ (6545318099 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1503 / 800 : ℝ) (1060468654711 / 1000000000000 : ℝ)
    (6545318099 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1502_denomUpper :
    Real.exp (20093350522591707 / 1000000000000000 : ℝ) ≤ (83224516532539849 / 156250000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (20093350522591707 / 1000000000000000 : ℝ) (1873703968893
    / 1000000000000 : ℝ) (83224516532539849 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1502_denomLower :
    (1297408781605413231 / 2500000000 : ℝ) ≤ Real.exp (8026937654247 / 400000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8026937654247 / 400000000000 : ℝ) (374436365807 /
    200000000000 : ℝ) (1297408781605413231 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1502_product_lower :
    (8214812654247 / 400000000000 : ℝ) ≤ Real.pi * Real.exp (751 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1502_leftExp
    (by norm_num : (0 : ℝ) ≤ (20918853 / 3200000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1502_product_upper :
    Real.pi * Real.exp (1503 / 800 : ℝ) ≤ (20562725522591707 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1502_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1502_endpointLower :
    (58721 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (751 / 800 : ℝ) (1503 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8214812654247 / 400000000000 : ℝ) (Real.pi * Real.exp (751 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1502_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1503 / 800 : ℝ) - (751 / 1600 : ℝ)) ≤
      (83224516532539849 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1502_denomUpper
    linarith [hpThetaJensenCell1502_product_upper]
  have hi : (1 / (83224516532539849 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1503 / 800 : ℝ) - (751 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (83224516532539849 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (83224516532539849 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((751 / 1600 : ℝ) - Real.pi * Real.exp (1503 / 800 : ℝ)) := by
    rw [show (751 / 1600 : ℝ) - Real.pi * Real.exp (1503 / 800 : ℝ) =
      -(Real.pi * Real.exp (1503 / 800 : ℝ) - (751 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (751 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (751 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1502_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (83224516532539849 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1502_endpointUpper :
    hpThetaJensenKernelEndpointUpper (751 / 800 : ℝ) (1503 / 1600 : ℝ) ≤ (12117 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1503 / 800 : ℝ)) (20562725522591707 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1503 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1502_product_upper
  have hD : (1297408781605413231 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (751 / 400 : ℝ) - (1503 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1502_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1502_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (751 / 400 : ℝ) - (1503 / 3200 : ℝ)) ≤
      (1 / (1297408781605413231 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1297408781605413231 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1503 / 3200 : ℝ) - Real.pi * Real.exp (751 / 400 : ℝ)) ≤
      (2 / (1297408781605413231 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1503 / 3200 : ℝ) - Real.pi * Real.exp (751 / 400 : ℝ) =
      -(Real.pi * Real.exp (751 / 400 : ℝ) - (1503 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20562725522591707 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (20562725522591707 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1502_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (751 / 800 : ℝ) (1503 / 1600 : ℝ)) :
    (58721 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12117 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1502_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1502_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1503_leftExp :
    (16363295247 / 2500000000 : ℝ) ≤ Real.exp (1503 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1503 / 800 : ℝ) (106046865471 / 100000000000 : ℝ)
    (16363295247 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1503_rightExp :
    Real.exp (47 / 25 : ℝ) ≤ (4095940539 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 25 : ℝ) (1060510080077 / 1000000000000 : ℝ)
    (4095940539 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1503_denomUpper :
    Real.exp (12574223438238627 / 625000000000000 : ℝ) ≤ (2731714889625553281 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (12574223438238627 / 625000000000000 : ℝ) (1875192220771
    / 1000000000000 : ℝ) (2731714889625553281 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1503_denomLower :
    (5323006272389433287 / 10000000000 : ℝ) ≤ Real.exp (6278974680201653 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6278974680201653 / 312500000000000 : ℝ) (1873666990181 /
    1000000000000 : ℝ) (5323006272389433287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1503_product_lower :
    (6425849680201653 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1503 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1503_leftExp
    (by norm_num : (0 : ℝ) ≤ (16363295247 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1503_product_upper :
    Real.pi * Real.exp (47 / 25 : ℝ) ≤ (12867778125738627 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1503_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1503_endpointLower :
    (57397 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1503 / 1600 : ℝ) (47 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6425849680201653 / 312500000000000 : ℝ) (Real.pi * Real.exp (1503 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1503_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 25 : ℝ) - (1503 / 3200 : ℝ)) ≤
      (2731714889625553281 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1503_denomUpper
    linarith [hpThetaJensenCell1503_product_upper]
  have hi : (1 / (2731714889625553281 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 25 : ℝ) - (1503 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2731714889625553281 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2731714889625553281 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1503 / 3200 : ℝ) - Real.pi * Real.exp (47 / 25 : ℝ)) := by
    rw [show (1503 / 3200 : ℝ) - Real.pi * Real.exp (47 / 25 : ℝ) =
      -(Real.pi * Real.exp (47 / 25 : ℝ) - (1503 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1503 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1503 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1503_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2731714889625553281 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1503_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1503 / 1600 : ℝ) (47 / 50 : ℝ) ≤ (59221 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 25 : ℝ)) (12867778125738627 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1503_product_upper
  have hD : (5323006272389433287 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1503 / 800 : ℝ) - (47 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell1503_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1503_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1503 / 800 : ℝ) - (47 / 100 : ℝ)) ≤
      (1 / (5323006272389433287 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5323006272389433287 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 100 : ℝ) - Real.pi * Real.exp (1503 / 800 : ℝ)) ≤
      (2 / (5323006272389433287 / 10000000000 : ℝ) : ℝ) := by
    rw [show (47 / 100 : ℝ) - Real.pi * Real.exp (1503 / 800 : ℝ) =
      -(Real.pi * Real.exp (1503 / 800 : ℝ) - (47 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12867778125738627 / 625000000000000 : ℝ) ^ 2 - 6 *
      (12867778125738627 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1503_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1503 / 1600 : ℝ) (47 / 50 : ℝ)) :
    (57397 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (59221 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1503_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1503_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1504_leftExp :
    (65535048621 / 10000000000 : ℝ) ≤ Real.exp (47 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 25 : ℝ) (265127520019 / 250000000000 : ℝ)
    (65535048621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1504_rightExp :
    Real.exp (301 / 160 : ℝ) ≤ (13123403731 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (301 / 160 : ℝ) (1060551507061 / 1000000000000 : ℝ)
    (13123403731 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1504_denomUpper :
    Real.exp (40288393297483483 / 2000000000000000 : ℝ) ≤ (5604197692000030327 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (40288393297483483 / 2000000000000000 : ℝ) (375336708267
    / 200000000000 : ℝ) (5604197692000030327 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1504_denomLower :
    (682497551796465497 / 1250000000 : ℝ) ≤ Real.exp (25147657433418079 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (25147657433418079 / 1250000000000000 : ℝ) (187515521219
    / 100000000000 : ℝ) (682497551796465497 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1504_product_lower :
    (25735548058418079 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1504_leftExp
    (by norm_num : (0 : ℝ) ≤ (65535048621 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1504_product_upper :
    Real.pi * Real.exp (301 / 160 : ℝ) ≤ (41228393297483483 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1504_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1504_endpointLower :
    (561 / 100000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 50 : ℝ) (301 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25735548058418079 / 1250000000000000 : ℝ) (Real.pi * Real.exp (47 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1504_product_lower
  have hD : Real.exp (Real.pi * Real.exp (301 / 160 : ℝ) - (47 / 100 : ℝ)) ≤
      (5604197692000030327 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1504_denomUpper
    linarith [hpThetaJensenCell1504_product_upper]
  have hi : (1 / (5604197692000030327 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (301 / 160 : ℝ) - (47 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5604197692000030327 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5604197692000030327 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 100 : ℝ) - Real.pi * Real.exp (301 / 160 : ℝ)) := by
    rw [show (47 / 100 : ℝ) - Real.pi * Real.exp (301 / 160 : ℝ) =
      -(Real.pi * Real.exp (301 / 160 : ℝ) - (47 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1504_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5604197692000030327 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1504_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 50 : ℝ) (301 / 320 : ℝ) ≤ (11577 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (301 / 160 : ℝ)) (41228393297483483 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (301 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1504_product_upper
  have hD : (682497551796465497 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 25 : ℝ) - (301 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1504_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1504_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 25 : ℝ) - (301 / 640 : ℝ)) ≤
      (1 / (682497551796465497 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (682497551796465497 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((301 / 640 : ℝ) - Real.pi * Real.exp (47 / 25 : ℝ)) ≤
      (2 / (682497551796465497 / 1250000000 : ℝ) : ℝ) := by
    rw [show (301 / 640 : ℝ) - Real.pi * Real.exp (47 / 25 : ℝ) =
      -(Real.pi * Real.exp (47 / 25 : ℝ) - (301 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41228393297483483 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (41228393297483483 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1504_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 50 : ℝ) (301 / 320 : ℝ)) :
    (561 / 100000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11577 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1504_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1504_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1505_leftExp :
    (16404254663 / 2500000000 : ℝ) ≤ Real.exp (301 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (301 / 160 : ℝ) (53027575353 / 50000000000 : ℝ)
    (16404254663 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1505_rightExp :
    Real.exp (753 / 400 : ℝ) ≤ (16424772803 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (753 / 400 : ℝ) (1060592935663 / 1000000000000 : ℝ)
    (16424772803 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1505_denomUpper :
    Real.exp (50424170014495179 / 2500000000000000 : ℝ) ≤ (1149755544092668913 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (50424170014495179 / 2500000000000000 : ℝ) (469544484601
    / 250000000000 : ℝ) (1149755544092668913 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1505_denomLower :
    (700082425823065241 / 1250000000 : ℝ) ≤ Real.exp (6294864089405437 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6294864089405437 / 312500000000000 : ℝ) (46916162571 /
    25000000000 : ℝ) (700082425823065241 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1505_product_lower :
    (6441934401905437 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (301 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1505_leftExp
    (by norm_num : (0 : ℝ) ≤ (16404254663 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1505_product_upper :
    Real.pi * Real.exp (753 / 400 : ℝ) ≤ (51599951264495179 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1505_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1505_endpointLower :
    (3427 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (301 / 320 : ℝ) (753 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6441934401905437 / 312500000000000 : ℝ) (Real.pi * Real.exp (301 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1505_product_lower
  have hD : Real.exp (Real.pi * Real.exp (753 / 400 : ℝ) - (301 / 640 : ℝ)) ≤
      (1149755544092668913 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1505_denomUpper
    linarith [hpThetaJensenCell1505_product_upper]
  have hi : (1 / (1149755544092668913 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (753 / 400 : ℝ) - (301 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1149755544092668913 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1149755544092668913 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((301 / 640 : ℝ) - Real.pi * Real.exp (753 / 400 : ℝ)) := by
    rw [show (301 / 640 : ℝ) - Real.pi * Real.exp (753 / 400 : ℝ) =
      -(Real.pi * Real.exp (753 / 400 : ℝ) - (301 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (301 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (301 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1505_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1149755544092668913 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1505_endpointUpper :
    hpThetaJensenKernelEndpointUpper (301 / 320 : ℝ) (753 / 800 : ℝ) ≤ (28289 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (753 / 400 : ℝ)) (51599951264495179 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (753 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1505_product_upper
  have hD : (700082425823065241 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (301 / 160 : ℝ) - (753 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1505_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1505_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (301 / 160 : ℝ) - (753 / 1600 : ℝ)) ≤
      (1 / (700082425823065241 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (700082425823065241 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((753 / 1600 : ℝ) - Real.pi * Real.exp (301 / 160 : ℝ)) ≤
      (2 / (700082425823065241 / 1250000000 : ℝ) : ℝ) := by
    rw [show (753 / 1600 : ℝ) - Real.pi * Real.exp (301 / 160 : ℝ) =
      -(Real.pi * Real.exp (301 / 160 : ℝ) - (753 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51599951264495179 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (51599951264495179 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1505_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (301 / 320 : ℝ) (753 / 800 : ℝ)) :
    (3427 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (28289 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1505_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1505_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1506_leftExp :
    (65699091209 / 10000000000 : ℝ) ≤ Real.exp (753 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (753 / 400 : ℝ) (530296467831 / 500000000000 : ℝ)
    (65699091209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1506_rightExp :
    Real.exp (1507 / 800 : ℝ) ≤ (2631250657 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1507 / 800 : ℝ) (265158591471 / 250000000000 : ℝ)
    (2631250657 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1506_denomUpper :
    Real.exp (8078068645276601 / 400000000000000 : ℝ) ≤ (5897277886407847977 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (8078068645276601 / 400000000000000 : ℝ) (469918854959 /
    250000000000 : ℝ) (5897277886407847977 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1506_denomLower :
    (2872574052693766863 / 5000000000 : ℝ) ≤ Real.exp (25211295543683091 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25211295543683091 / 1250000000000000 : ℝ) (939070434967
    / 500000000000 : ℝ) (2872574052693766863 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1506_product_lower :
    (25799967418683091 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (753 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1506_leftExp
    (by norm_num : (0 : ℝ) ≤ (65699091209 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1506_product_upper :
    Real.pi * Real.exp (1507 / 800 : ℝ) ≤ (8266318645276601 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1506_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1506_endpointLower :
    (5359 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (753 / 800 : ℝ) (1507 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25799967418683091 / 1250000000000000 : ℝ) (Real.pi * Real.exp (753 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1506_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1507 / 800 : ℝ) - (753 / 1600 : ℝ)) ≤
      (5897277886407847977 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1506_denomUpper
    linarith [hpThetaJensenCell1506_product_upper]
  have hi : (1 / (5897277886407847977 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1507 / 800 : ℝ) - (753 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5897277886407847977 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5897277886407847977 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((753 / 1600 : ℝ) - Real.pi * Real.exp (1507 / 800 : ℝ)) := by
    rw [show (753 / 1600 : ℝ) - Real.pi * Real.exp (1507 / 800 : ℝ) =
      -(Real.pi * Real.exp (1507 / 800 : ℝ) - (753 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (753 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (753 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1506_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5897277886407847977 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1506_endpointUpper :
    hpThetaJensenKernelEndpointUpper (753 / 800 : ℝ) (1507 / 1600 : ℝ) ≤ (55299 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1507 / 800 : ℝ)) (8266318645276601 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1507 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1506_product_upper
  have hD : (2872574052693766863 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (753 / 400 : ℝ) - (1507 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1506_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1506_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (753 / 400 : ℝ) - (1507 / 3200 : ℝ)) ≤
      (1 / (2872574052693766863 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2872574052693766863 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1507 / 3200 : ℝ) - Real.pi * Real.exp (753 / 400 : ℝ)) ≤
      (2 / (2872574052693766863 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1507 / 3200 : ℝ) - Real.pi * Real.exp (753 / 400 : ℝ) =
      -(Real.pi * Real.exp (753 / 400 : ℝ) - (1507 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8266318645276601 / 400000000000000 : ℝ) ^ 2 - 6 *
      (8266318645276601 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1506_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (753 / 800 : ℝ) (1507 / 1600 : ℝ)) :
    (5359 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (55299 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1506_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1506_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1507_leftExp :
    (32890633211 / 5000000000 : ℝ) ≤ Real.exp (1507 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1507 / 800 : ℝ) (1060634365883 / 1000000000000 : ℝ)
    (32890633211 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1507_rightExp :
    Real.exp (377 / 200 : ℝ) ≤ (65863544421 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (377 / 200 : ℝ) (1060675797723 / 1000000000000 : ℝ)
    (65863544421 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1507_denomUpper :
    Real.exp (202207075108202653 / 10000000000000000 : ℝ) ≤ (6049809396760795273 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (202207075108202653 / 10000000000000000 : ℝ)
    (940587996727 / 500000000000 : ℝ) (6049809396760795273 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1507_denomLower :
    (5893554463969313499 / 10000000000 : ℝ) ≤ Real.exp (12621587521326489 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (12621587521326489 / 625000000000000 : ℝ) (1879638321327
    / 1000000000000 : ℝ) (5893554463969313499 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1507_product_lower :
    (12916118771326489 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1507 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1507_leftExp
    (by norm_num : (0 : ℝ) ≤ (32890633211 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1507_product_upper :
    Real.pi * Real.exp (377 / 200 : ℝ) ≤ (206916450108202653 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1507_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1507_endpointLower :
    (419 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (1507 / 1600 : ℝ) (377 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12916118771326489 / 625000000000000 : ℝ) (Real.pi * Real.exp (1507 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1507_product_lower
  have hD : Real.exp (Real.pi * Real.exp (377 / 200 : ℝ) - (1507 / 3200 : ℝ)) ≤
      (6049809396760795273 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1507_denomUpper
    linarith [hpThetaJensenCell1507_product_upper]
  have hi : (1 / (6049809396760795273 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (377 / 200 : ℝ) - (1507 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6049809396760795273 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6049809396760795273 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1507 / 3200 : ℝ) - Real.pi * Real.exp (377 / 200 : ℝ)) := by
    rw [show (1507 / 3200 : ℝ) - Real.pi * Real.exp (377 / 200 : ℝ) =
      -(Real.pi * Real.exp (377 / 200 : ℝ) - (1507 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1507 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1507 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1507_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6049809396760795273 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1507_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1507 / 1600 : ℝ) (377 / 400 : ℝ) ≤ (27023 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (377 / 200 : ℝ)) (206916450108202653 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (377 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1507_product_upper
  have hD : (5893554463969313499 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1507 / 800 : ℝ) - (377 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1507_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1507_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1507 / 800 : ℝ) - (377 / 800 : ℝ)) ≤
      (1 / (5893554463969313499 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5893554463969313499 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((377 / 800 : ℝ) - Real.pi * Real.exp (1507 / 800 : ℝ)) ≤
      (2 / (5893554463969313499 / 10000000000 : ℝ) : ℝ) := by
    rw [show (377 / 800 : ℝ) - Real.pi * Real.exp (1507 / 800 : ℝ) =
      -(Real.pi * Real.exp (1507 / 800 : ℝ) - (377 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (206916450108202653 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (206916450108202653 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1507_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1507 / 1600 : ℝ) (377 / 400 : ℝ)) :
    (419 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (27023 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1507_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1507_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1508_leftExp :
    (32931772209 / 5000000000 : ℝ) ≤ Real.exp (377 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (377 / 200 : ℝ) (530337898861 / 500000000000 : ℝ)
    (32931772209 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1508_rightExp :
    Real.exp (1509 / 800 : ℝ) ≤ (6594592533 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1509 / 800 : ℝ) (1060717231181 / 1000000000000 : ℝ)
    (6594592533 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1508_denomUpper :
    Real.exp (20246275739525069 / 1000000000000000 : ℝ) ≤ (6206486752962940897 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (20246275739525069 / 1000000000000000 : ℝ) (1882679667161
    / 1000000000000 : ℝ) (6206486752962940897 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1508_denomLower :
    (3022994809677867339 / 5000000000 : ℝ) ≤ Real.exp (12637547452202091 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12637547452202091 / 625000000000000 : ℝ) (940569432423 /
    500000000000 : ℝ) (3022994809677867339 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1508_product_lower :
    (12932274014702091 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (377 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1508_leftExp
    (by norm_num : (0 : ℝ) ≤ (32931772209 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1508_product_upper :
    Real.pi * Real.exp (1509 / 800 : ℝ) ≤ (20717525739525069 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1508_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1508_endpointLower :
    (10237 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (377 / 400 : ℝ) (1509 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12932274014702091 / 625000000000000 : ℝ) (Real.pi * Real.exp (377 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1508_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1509 / 800 : ℝ) - (377 / 800 : ℝ)) ≤
      (6206486752962940897 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1508_denomUpper
    linarith [hpThetaJensenCell1508_product_upper]
  have hi : (1 / (6206486752962940897 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1509 / 800 : ℝ) - (377 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6206486752962940897 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6206486752962940897 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((377 / 800 : ℝ) - Real.pi * Real.exp (1509 / 800 : ℝ)) := by
    rw [show (377 / 800 : ℝ) - Real.pi * Real.exp (1509 / 800 : ℝ) =
      -(Real.pi * Real.exp (1509 / 800 : ℝ) - (377 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (377 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (377 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1508_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6206486752962940897 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1508_endpointUpper :
    hpThetaJensenKernelEndpointUpper (377 / 400 : ℝ) (1509 / 1600 : ℝ) ≤ (52821 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1509 / 800 : ℝ)) (20717525739525069 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1509 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1508_product_upper
  have hD : (3022994809677867339 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (377 / 200 : ℝ) - (1509 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1508_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1508_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (377 / 200 : ℝ) - (1509 / 3200 : ℝ)) ≤
      (1 / (3022994809677867339 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3022994809677867339 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1509 / 3200 : ℝ) - Real.pi * Real.exp (377 / 200 : ℝ)) ≤
      (2 / (3022994809677867339 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1509 / 3200 : ℝ) - Real.pi * Real.exp (377 / 200 : ℝ) =
      -(Real.pi * Real.exp (377 / 200 : ℝ) - (1509 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20717525739525069 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (20717525739525069 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1508_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (377 / 400 : ℝ) (1509 / 1600 : ℝ)) :
    (10237 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (52821 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1508_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1508_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1509_leftExp :
    (65945925327 / 10000000000 : ℝ) ≤ Real.exp (1509 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1509 / 800 : ℝ) (53035861559 / 50000000000 : ℝ)
    (65945925327 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1509_rightExp :
    Real.exp (151 / 80 : ℝ) ≤ (33014204639 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (151 / 80 : ℝ) (1060758666257 / 1000000000000 : ℝ)
    (33014204639 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1509_denomUpper :
    Real.exp (101359381694449927 / 5000000000000000 : ℝ) ≤ (6367427838063839873 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (101359381694449927 / 5000000000000000 : ℝ) (471046612201
    / 250000000000 : ℝ) (6367427838063839873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1509_denomLower :
    (1550642000050269311 / 2500000000 : ℝ) ≤ Real.exp (25307055179987573 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25307055179987573 / 1250000000000000 : ℝ) (188264250839
    / 100000000000 : ℝ) (1550642000050269311 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1509_product_lower :
    (25896898929987573 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1509 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1509_leftExp
    (by norm_num : (0 : ℝ) ≤ (65945925327 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1509_product_upper :
    Real.pi * Real.exp (151 / 80 : ℝ) ≤ (103717194194449927 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1509_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1509_endpointLower :
    (50021 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1509 / 1600 : ℝ) (151 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25896898929987573 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1509 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1509_product_lower
  have hD : Real.exp (Real.pi * Real.exp (151 / 80 : ℝ) - (1509 / 3200 : ℝ)) ≤
      (6367427838063839873 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1509_denomUpper
    linarith [hpThetaJensenCell1509_product_upper]
  have hi : (1 / (6367427838063839873 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (151 / 80 : ℝ) - (1509 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6367427838063839873 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6367427838063839873 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1509 / 3200 : ℝ) - Real.pi * Real.exp (151 / 80 : ℝ)) := by
    rw [show (1509 / 3200 : ℝ) - Real.pi * Real.exp (151 / 80 : ℝ) =
      -(Real.pi * Real.exp (151 / 80 : ℝ) - (1509 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1509 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1509 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1509_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6367427838063839873 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1509_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1509 / 1600 : ℝ) (151 / 160 : ℝ) ≤ (51621 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (151 / 80 : ℝ)) (103717194194449927 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (151 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1509_product_upper
  have hD : (1550642000050269311 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1509 / 800 : ℝ) - (151 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1509_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1509_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1509 / 800 : ℝ) - (151 / 320 : ℝ)) ≤
      (1 / (1550642000050269311 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1550642000050269311 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((151 / 320 : ℝ) - Real.pi * Real.exp (1509 / 800 : ℝ)) ≤
      (2 / (1550642000050269311 / 2500000000 : ℝ) : ℝ) := by
    rw [show (151 / 320 : ℝ) - Real.pi * Real.exp (1509 / 800 : ℝ) =
      -(Real.pi * Real.exp (1509 / 800 : ℝ) - (151 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (103717194194449927 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (103717194194449927 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1509_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1509 / 1600 : ℝ) (151 / 160 : ℝ)) :
    (50021 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (51621 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1509_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1509_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1510_leftExp :
    (2641136371 / 400000000 : ℝ) ≤ Real.exp (151 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (151 / 80 : ℝ) (66297416641 / 62500000000 : ℝ)
    (2641136371 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1510_rightExp :
    Real.exp (1511 / 800 : ℝ) ≤ (16527749099 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1511 / 800 : ℝ) (132600012869 / 125000000000 : ℝ)
    (16527749099 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1510_denomUpper :
    Real.exp (50743773375174707 / 2500000000000000 : ℝ) ≤ (1306550807781950873 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (50743773375174707 / 2500000000000000 : ℝ) (377139269269
    / 200000000000 : ℝ) (1306550807781950873 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1510_denomLower :
    (198856481726183487 / 312500000 : ℝ) ≤ Real.exp (1013562236755329 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1013562236755329 / 50000000000000 : ℝ) (58879664369 /
    31250000000 : ℝ) (198856481726183487 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1510_product_lower :
    (1037171611755329 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (151 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1510_leftExp
    (by norm_num : (0 : ℝ) ≤ (2641136371 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1510_product_upper :
    Real.pi * Real.exp (1511 / 800 : ℝ) ≤ (51923460875174707 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1510_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1510_endpointLower :
    (24441 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (151 / 160 : ℝ) (1511 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1037171611755329 / 50000000000000 : ℝ) (Real.pi * Real.exp (151 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1510_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1511 / 800 : ℝ) - (151 / 320 : ℝ)) ≤
      (1306550807781950873 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1510_denomUpper
    linarith [hpThetaJensenCell1510_product_upper]
  have hi : (1 / (1306550807781950873 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1511 / 800 : ℝ) - (151 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1306550807781950873 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1306550807781950873 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((151 / 320 : ℝ) - Real.pi * Real.exp (1511 / 800 : ℝ)) := by
    rw [show (151 / 320 : ℝ) - Real.pi * Real.exp (1511 / 800 : ℝ) =
      -(Real.pi * Real.exp (1511 / 800 : ℝ) - (151 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (151 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (151 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1510_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1306550807781950873 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1510_endpointUpper :
    hpThetaJensenKernelEndpointUpper (151 / 160 : ℝ) (1511 / 1600 : ℝ) ≤ (50447 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1511 / 800 : ℝ)) (51923460875174707 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1511 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1510_product_upper
  have hD : (198856481726183487 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (151 / 80 : ℝ) - (1511 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1510_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1510_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (151 / 80 : ℝ) - (1511 / 3200 : ℝ)) ≤
      (1 / (198856481726183487 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (198856481726183487 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1511 / 3200 : ℝ) - Real.pi * Real.exp (151 / 80 : ℝ)) ≤
      (2 / (198856481726183487 / 312500000 : ℝ) : ℝ) := by
    rw [show (1511 / 3200 : ℝ) - Real.pi * Real.exp (151 / 80 : ℝ) =
      -(Real.pi * Real.exp (151 / 80 : ℝ) - (1511 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51923460875174707 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (51923460875174707 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1510_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (151 / 160 : ℝ) (1511 / 1600 : ℝ)) :
    (24441 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (50447 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1510_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1510_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1511_leftExp :
    (66110996393 / 10000000000 : ℝ) ≤ Real.exp (1511 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1511 / 800 : ℝ) (1060800102951 / 1000000000000 : ℝ)
    (66110996393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1511_rightExp :
    Real.exp (189 / 100 : ℝ) ≤ (16548421703 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (189 / 100 : ℝ) (212168308253 / 200000000000 : ℝ)
    (16548421703 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1511_denomUpper :
    Real.exp (50807937033192879 / 2500000000000000 : ℝ) ≤ (1340518067658876111 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (50807937033192879 / 2500000000000000 : ℝ) (943604683857
    / 500000000000 : ℝ) (1340518067658876111 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1511_denomLower :
    (6528629174469610637 / 10000000000 : ℝ) ≤ Real.exp (25371097172534707 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25371097172534707 / 1250000000000000 : ℝ) (1885659127061
    / 1000000000000 : ℝ) (6528629174469610637 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1511_product_lower :
    (25961722172534707 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1511 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1511_leftExp
    (by norm_num : (0 : ℝ) ≤ (66110996393 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1511_product_upper :
    Real.pi * Real.exp (189 / 100 : ℝ) ≤ (51988405783192879 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1511_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1511_endpointLower :
    (5971 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1511 / 1600 : ℝ) (189 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25961722172534707 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1511 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1511_product_lower
  have hD : Real.exp (Real.pi * Real.exp (189 / 100 : ℝ) - (1511 / 3200 : ℝ)) ≤
      (1340518067658876111 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1511_denomUpper
    linarith [hpThetaJensenCell1511_product_upper]
  have hi : (1 / (1340518067658876111 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (189 / 100 : ℝ) - (1511 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1340518067658876111 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1340518067658876111 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1511 / 3200 : ℝ) - Real.pi * Real.exp (189 / 100 : ℝ)) := by
    rw [show (1511 / 3200 : ℝ) - Real.pi * Real.exp (189 / 100 : ℝ) =
      -(Real.pi * Real.exp (189 / 100 : ℝ) - (1511 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1511 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1511 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1511_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1340518067658876111 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1511_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1511 / 1600 : ℝ) (189 / 200 : ℝ) ≤ (49299 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (189 / 100 : ℝ)) (51988405783192879 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (189 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1511_product_upper
  have hD : (6528629174469610637 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1511 / 800 : ℝ) - (189 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1511_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1511_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1511 / 800 : ℝ) - (189 / 400 : ℝ)) ≤
      (1 / (6528629174469610637 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6528629174469610637 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((189 / 400 : ℝ) - Real.pi * Real.exp (1511 / 800 : ℝ)) ≤
      (2 / (6528629174469610637 / 10000000000 : ℝ) : ℝ) := by
    rw [show (189 / 400 : ℝ) - Real.pi * Real.exp (1511 / 800 : ℝ) =
      -(Real.pi * Real.exp (1511 / 800 : ℝ) - (189 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51988405783192879 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (51988405783192879 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1511_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1511 / 1600 : ℝ) (189 / 200 : ℝ)) :
    (5971 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (49299 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1511_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1511_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1512_leftExp :
    (66193686809 / 10000000000 : ℝ) ≤ Real.exp (189 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (189 / 100 : ℝ) (66302596329 / 62500000000 : ℝ)
    (66193686809 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1512_rightExp :
    Real.exp (1513 / 800 : ℝ) ≤ (4142280041 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1513 / 800 : ℝ) (1060882981197 / 1000000000000 : ℝ)
    (4142280041 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1512_denomUpper :
    Real.exp (12718045480845313 / 625000000000000 : ℝ) ≤ (6877065435497998533 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (12718045480845313 / 625000000000000 : ℝ) (1888725520897
    / 1000000000000 : ℝ) (6877065435497998533 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1512_denomLower :
    (6698358181563266593 / 10000000000 : ℝ) ≤ Real.exp (25403178991207491 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25403178991207491 / 1250000000000000 : ℝ) (943586059039
    / 500000000000 : ℝ) (6698358181563266593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1512_product_lower :
    (25994194616207491 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (189 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1512_leftExp
    (by norm_num : (0 : ℝ) ≤ (66193686809 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1512_product_upper :
    Real.pi * Real.exp (1513 / 800 : ℝ) ≤ (13013357980845313 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1512_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1512_endpointLower :
    (46677 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (189 / 200 : ℝ) (1513 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25994194616207491 / 1250000000000000 : ℝ) (Real.pi * Real.exp (189 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1512_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1513 / 800 : ℝ) - (189 / 400 : ℝ)) ≤
      (6877065435497998533 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1512_denomUpper
    linarith [hpThetaJensenCell1512_product_upper]
  have hi : (1 / (6877065435497998533 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1513 / 800 : ℝ) - (189 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6877065435497998533 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6877065435497998533 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((189 / 400 : ℝ) - Real.pi * Real.exp (1513 / 800 : ℝ)) := by
    rw [show (189 / 400 : ℝ) - Real.pi * Real.exp (1513 / 800 : ℝ) =
      -(Real.pi * Real.exp (1513 / 800 : ℝ) - (189 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (189 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (189 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1512_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6877065435497998533 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1512_endpointUpper :
    hpThetaJensenKernelEndpointUpper (189 / 200 : ℝ) (1513 / 1600 : ℝ) ≤ (24087 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1513 / 800 : ℝ)) (13013357980845313 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1513 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1512_product_upper
  have hD : (6698358181563266593 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (189 / 100 : ℝ) - (1513 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1512_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1512_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (189 / 100 : ℝ) - (1513 / 3200 : ℝ)) ≤
      (1 / (6698358181563266593 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6698358181563266593 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1513 / 3200 : ℝ) - Real.pi * Real.exp (189 / 100 : ℝ)) ≤
      (2 / (6698358181563266593 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1513 / 3200 : ℝ) - Real.pi * Real.exp (189 / 100 : ℝ) =
      -(Real.pi * Real.exp (189 / 100 : ℝ) - (1513 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13013357980845313 / 625000000000000 : ℝ) ^ 2 - 6 *
      (13013357980845313 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1512_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (189 / 200 : ℝ) (1513 / 1600 : ℝ)) :
    (46677 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (24087 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1512_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1512_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1513_leftExp :
    (66276480653 / 10000000000 : ℝ) ≤ Real.exp (1513 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1513 / 800 : ℝ) (265220745299 / 250000000000 : ℝ)
    (66276480653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1513_rightExp :
    Real.exp (757 / 400 : ℝ) ≤ (66359378057 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (757 / 400 : ℝ) (265231105687 / 250000000000 : ℝ)
    (66359378057 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1513_denomUpper :
    Real.exp (203746032588224801 / 10000000000000000 : ℝ) ≤ (1764077963785434317 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (203746032588224801 / 10000000000000000 : ℝ)
    (472561203471 / 250000000000 : ℝ) (1764077963785434317 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1513_denomLower :
    (6872723054544644151 / 10000000000 : ℝ) ≤ Real.exp (25435301425952447 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25435301425952447 / 1250000000000000 : ℝ) (944344120423
    / 500000000000 : ℝ) (6872723054544644151 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1513_product_lower :
    (26026707675952447 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1513 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1513_leftExp
    (by norm_num : (0 : ℝ) ≤ (66276480653 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1513_product_upper :
    Real.pi * Real.exp (757 / 400 : ℝ) ≤ (208474157588224801 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1513_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1513_endpointLower :
    (45609 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1513 / 1600 : ℝ) (757 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26026707675952447 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1513 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1513_product_lower
  have hD : Real.exp (Real.pi * Real.exp (757 / 400 : ℝ) - (1513 / 3200 : ℝ)) ≤
      (1764077963785434317 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1513_denomUpper
    linarith [hpThetaJensenCell1513_product_upper]
  have hi : (1 / (1764077963785434317 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (757 / 400 : ℝ) - (1513 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1764077963785434317 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1764077963785434317 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1513 / 3200 : ℝ) - Real.pi * Real.exp (757 / 400 : ℝ)) := by
    rw [show (1513 / 3200 : ℝ) - Real.pi * Real.exp (757 / 400 : ℝ) =
      -(Real.pi * Real.exp (757 / 400 : ℝ) - (1513 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1513 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1513 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1513_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1764077963785434317 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1513_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1513 / 1600 : ℝ) (757 / 800 : ℝ) ≤ (23537 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (757 / 400 : ℝ)) (208474157588224801 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (757 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1513_product_upper
  have hD : (6872723054544644151 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1513 / 800 : ℝ) - (757 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1513_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1513_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1513 / 800 : ℝ) - (757 / 1600 : ℝ)) ≤
      (1 / (6872723054544644151 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6872723054544644151 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((757 / 1600 : ℝ) - Real.pi * Real.exp (1513 / 800 : ℝ)) ≤
      (2 / (6872723054544644151 / 10000000000 : ℝ) : ℝ) := by
    rw [show (757 / 1600 : ℝ) - Real.pi * Real.exp (1513 / 800 : ℝ) =
      -(Real.pi * Real.exp (1513 / 800 : ℝ) - (757 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (208474157588224801 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (208474157588224801 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1513_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1513 / 1600 : ℝ) (757 / 800 : ℝ)) :
    (45609 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (23537 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1513_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1513_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1514_leftExp :
    (33179689027 / 5000000000 : ℝ) ≤ Real.exp (757 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (757 / 400 : ℝ) (1060924422747 / 1000000000000 : ℝ)
    (33179689027 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1514_rightExp :
    Real.exp (303 / 160 : ℝ) ≤ (13288475829 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (303 / 160 : ℝ) (530482932959 / 500000000000 : ℝ)
    (13288475829 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1514_denomUpper :
    Real.exp (40800732645055597 / 2000000000000000 : ℝ) ≤ (7240466069702747537 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (40800732645055597 / 2000000000000000 : ℝ) (945883627353
    / 500000000000 : ℝ) (7240466069702747537 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1514_denomLower :
    (1762964058593405369 / 2500000000 : ℝ) ≤ Real.exp (12733732263713873 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12733732263713873 / 625000000000000 : ℝ) (472551875839 /
    250000000000 : ℝ) (1762964058593405369 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1514_product_lower :
    (13029630701213873 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (757 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1514_leftExp
    (by norm_num : (0 : ℝ) ≤ (33179689027 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1514_product_upper :
    Real.pi * Real.exp (303 / 160 : ℝ) ≤ (41746982645055597 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1514_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1514_endpointLower :
    (8913 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (757 / 800 : ℝ) (303 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13029630701213873 / 625000000000000 : ℝ) (Real.pi * Real.exp (757 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1514_product_lower
  have hD : Real.exp (Real.pi * Real.exp (303 / 160 : ℝ) - (757 / 1600 : ℝ)) ≤
      (7240466069702747537 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1514_denomUpper
    linarith [hpThetaJensenCell1514_product_upper]
  have hi : (1 / (7240466069702747537 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (303 / 160 : ℝ) - (757 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7240466069702747537 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7240466069702747537 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((757 / 1600 : ℝ) - Real.pi * Real.exp (303 / 160 : ℝ)) := by
    rw [show (757 / 1600 : ℝ) - Real.pi * Real.exp (303 / 160 : ℝ) =
      -(Real.pi * Real.exp (303 / 160 : ℝ) - (757 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (757 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (757 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1514_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7240466069702747537 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1514_endpointUpper :
    hpThetaJensenKernelEndpointUpper (757 / 800 : ℝ) (303 / 320 : ℝ) ≤ (22999 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (303 / 160 : ℝ)) (41746982645055597 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (303 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1514_product_upper
  have hD : (1762964058593405369 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (757 / 400 : ℝ) - (303 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1514_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1514_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (757 / 400 : ℝ) - (303 / 640 : ℝ)) ≤
      (1 / (1762964058593405369 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1762964058593405369 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((303 / 640 : ℝ) - Real.pi * Real.exp (757 / 400 : ℝ)) ≤
      (2 / (1762964058593405369 / 2500000000 : ℝ) : ℝ) := by
    rw [show (303 / 640 : ℝ) - Real.pi * Real.exp (757 / 400 : ℝ) =
      -(Real.pi * Real.exp (757 / 400 : ℝ) - (303 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41746982645055597 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (41746982645055597 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1514_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (757 / 800 : ℝ) (303 / 320 : ℝ)) :
    (8913 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22999 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1514_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1514_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1515_leftExp :
    (33221189571 / 5000000000 : ℝ) ≤ Real.exp (303 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (303 / 160 : ℝ) (1060965865917 / 1000000000000 : ℝ)
    (33221189571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1515_rightExp :
    Real.exp (379 / 200 : ℝ) ≤ (66525484047 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (379 / 200 : ℝ) (530503655353 / 500000000000 : ℝ)
    (66525484047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1515_denomUpper :
    Real.exp (204261620003666871 / 10000000000000000 : ℝ) ≤ (742966861229095477 / 1000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (204261620003666871 / 10000000000000000 : ℝ)
    (1893292851359 / 1000000000000 : ℝ) (742966861229095477 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1515_denomLower :
    (7235894106893164853 / 10000000000 : ℝ) ≤ Real.exp (12749834173342129 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (12749834173342129 / 625000000000000 : ℝ) (472932478409 /
    250000000000 : ℝ) (7235894106893164853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1515_product_lower :
    (13045927923342129 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (303 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1515_leftExp
    (by norm_num : (0 : ℝ) ≤ (33221189571 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1515_product_upper :
    Real.pi * Real.exp (379 / 200 : ℝ) ≤ (208995995003666871 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1515_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1515_endpointLower :
    (43543 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (303 / 320 : ℝ) (379 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13045927923342129 / 625000000000000 : ℝ) (Real.pi * Real.exp (303 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1515_product_lower
  have hD : Real.exp (Real.pi * Real.exp (379 / 200 : ℝ) - (303 / 640 : ℝ)) ≤
      (742966861229095477 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1515_denomUpper
    linarith [hpThetaJensenCell1515_product_upper]
  have hi : (1 / (742966861229095477 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (379 / 200 : ℝ) - (303 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (742966861229095477 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (742966861229095477 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((303 / 640 : ℝ) - Real.pi * Real.exp (379 / 200 : ℝ)) := by
    rw [show (303 / 640 : ℝ) - Real.pi * Real.exp (379 / 200 : ℝ) =
      -(Real.pi * Real.exp (379 / 200 : ℝ) - (303 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (303 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (303 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1515_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (742966861229095477 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1515_endpointUpper :
    hpThetaJensenKernelEndpointUpper (303 / 320 : ℝ) (379 / 400 : ℝ) ≤ (2809 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (379 / 200 : ℝ)) (208995995003666871 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (379 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1515_product_upper
  have hD : (7235894106893164853 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (303 / 160 : ℝ) - (379 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1515_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1515_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (303 / 160 : ℝ) - (379 / 800 : ℝ)) ≤
      (1 / (7235894106893164853 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7235894106893164853 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((379 / 800 : ℝ) - Real.pi * Real.exp (303 / 160 : ℝ)) ≤
      (2 / (7235894106893164853 / 10000000000 : ℝ) : ℝ) := by
    rw [show (379 / 800 : ℝ) - Real.pi * Real.exp (303 / 160 : ℝ) =
      -(Real.pi * Real.exp (303 / 160 : ℝ) - (379 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (208995995003666871 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (208995995003666871 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1515_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (303 / 320 : ℝ) (379 / 400 : ℝ)) :
    (43543 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2809 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1515_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1515_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1516_leftExp :
    (16631371011 / 2500000000 : ℝ) ≤ Real.exp (379 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (379 / 200 : ℝ) (212201462141 / 200000000000 : ℝ)
    (16631371011 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1516_rightExp :
    Real.exp (1517 / 800 : ℝ) ≤ (33304346449 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1517 / 800 : ℝ) (530524378557 / 500000000000 : ℝ)
    (33304346449 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1516_denomUpper :
    Real.exp (102259951673753257 / 5000000000000000 : ℝ) ≤ (7624064228346055391 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (102259951673753257 / 5000000000000000 : ℝ)
    (1894821612011 / 1000000000000 : ℝ) (7624064228346055391 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1516_denomLower :
    (7424977116602985239 / 10000000000 : ℝ) ≤ Real.exp (6382978233398689 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6382978233398689 / 312500000000000 : ℝ) (473313869921 /
    250000000000 : ℝ) (7424977116602985239 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1516_product_lower :
    (6531122764648689 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (379 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1516_leftExp
    (by norm_num : (0 : ℝ) ≤ (16631371011 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1516_product_upper :
    Real.pi * Real.exp (1517 / 800 : ℝ) ≤ (104628701673753257 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1516_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1516_endpointLower :
    (42543 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (379 / 400 : ℝ) (1517 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6531122764648689 / 312500000000000 : ℝ) (Real.pi * Real.exp (379 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1516_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1517 / 800 : ℝ) - (379 / 800 : ℝ)) ≤
      (7624064228346055391 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1516_denomUpper
    linarith [hpThetaJensenCell1516_product_upper]
  have hi : (1 / (7624064228346055391 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1517 / 800 : ℝ) - (379 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7624064228346055391 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7624064228346055391 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((379 / 800 : ℝ) - Real.pi * Real.exp (1517 / 800 : ℝ)) := by
    rw [show (379 / 800 : ℝ) - Real.pi * Real.exp (1517 / 800 : ℝ) =
      -(Real.pi * Real.exp (1517 / 800 : ℝ) - (379 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (379 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (379 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1516_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7624064228346055391 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1516_endpointUpper :
    hpThetaJensenKernelEndpointUpper (379 / 400 : ℝ) (1517 / 1600 : ℝ) ≤ (21957 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1517 / 800 : ℝ)) (104628701673753257 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1517 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1516_product_upper
  have hD : (7424977116602985239 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (379 / 200 : ℝ) - (1517 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1516_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1516_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (379 / 200 : ℝ) - (1517 / 3200 : ℝ)) ≤
      (1 / (7424977116602985239 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7424977116602985239 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1517 / 3200 : ℝ) - Real.pi * Real.exp (379 / 200 : ℝ)) ≤
      (2 / (7424977116602985239 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1517 / 3200 : ℝ) - Real.pi * Real.exp (379 / 200 : ℝ) =
      -(Real.pi * Real.exp (379 / 200 : ℝ) - (1517 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (104628701673753257 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (104628701673753257 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1516_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (379 / 400 : ℝ) (1517 / 1600 : ℝ)) :
    (42543 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (21957 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1516_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1516_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1517_leftExp :
    (13321738579 / 2000000000 : ℝ) ≤ Real.exp (1517 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1517 / 800 : ℝ) (1061048757113 / 1000000000000 : ℝ)
    (13321738579 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1517_rightExp :
    Real.exp (759 / 400 : ℝ) ≤ (33346002911 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (759 / 400 : ℝ) (53054510257 / 50000000000 : ℝ)
    (33346002911 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1517_denomUpper :
    Real.exp (102389256823177223 / 5000000000000000 : ℝ) ≤ (7823801961162088361 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (102389256823177223 / 5000000000000000 : ℝ)
    (1896353544647 / 1000000000000 : ℝ) (7823801961162088361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1517_denomLower :
    (3809624958654420011 / 5000000000 : ℝ) ≤ Real.exp (5112839668234721 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5112839668234721 / 250000000000000 : ℝ) (1894784209667 /
    1000000000000 : ℝ) (3809624958654420011 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1517_product_lower :
    (5231433418234721 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1517 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1517_leftExp
    (by norm_num : (0 : ℝ) ≤ (13321738579 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1517_product_upper :
    Real.pi * Real.exp (759 / 400 : ℝ) ≤ (104759569323177223 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1517_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1517_endpointLower :
    (8313 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1517 / 1600 : ℝ) (759 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5231433418234721 / 250000000000000 : ℝ) (Real.pi * Real.exp (1517 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1517_product_lower
  have hD : Real.exp (Real.pi * Real.exp (759 / 400 : ℝ) - (1517 / 3200 : ℝ)) ≤
      (7823801961162088361 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1517_denomUpper
    linarith [hpThetaJensenCell1517_product_upper]
  have hi : (1 / (7823801961162088361 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (759 / 400 : ℝ) - (1517 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7823801961162088361 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7823801961162088361 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1517 / 3200 : ℝ) - Real.pi * Real.exp (759 / 400 : ℝ)) := by
    rw [show (1517 / 3200 : ℝ) - Real.pi * Real.exp (759 / 400 : ℝ) =
      -(Real.pi * Real.exp (759 / 400 : ℝ) - (1517 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1517 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1517 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1517_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7823801961162088361 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1517_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1517 / 1600 : ℝ) (759 / 800 : ℝ) ≤ (8581 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (759 / 400 : ℝ)) (104759569323177223 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (759 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1517_product_upper
  have hD : (3809624958654420011 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1517 / 800 : ℝ) - (759 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1517_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1517_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1517 / 800 : ℝ) - (759 / 1600 : ℝ)) ≤
      (1 / (3809624958654420011 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3809624958654420011 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((759 / 1600 : ℝ) - Real.pi * Real.exp (1517 / 800 : ℝ)) ≤
      (2 / (3809624958654420011 / 5000000000 : ℝ) : ℝ) := by
    rw [show (759 / 1600 : ℝ) - Real.pi * Real.exp (1517 / 800 : ℝ) =
      -(Real.pi * Real.exp (1517 / 800 : ℝ) - (759 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (104759569323177223 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (104759569323177223 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1517_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1517 / 1600 : ℝ) (759 / 800 : ℝ)) :
    (8313 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8581 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1517_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1517_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1518_leftExp :
    (66692005819 / 10000000000 : ℝ) ≤ Real.exp (759 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (759 / 400 : ℝ) (1061090205139 / 1000000000000 : ℝ)
    (66692005819 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1518_rightExp :
    Real.exp (1519 / 800 : ℝ) ≤ (13355084591 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1519 / 800 : ℝ) (530565827393 / 500000000000 : ℝ)
    (13355084591 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1518_denomUpper :
    Real.exp (41007490265493463 / 2000000000000000 : ℝ) ≤ (8029035340635623249 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (41007490265493463 / 2000000000000000 : ℝ) (1897888657497
    / 1000000000000 : ℝ) (8029035340635623249 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1518_denomLower :
    (7818861458072638729 / 10000000000 : ℝ) ≤ Real.exp (25596524618115481 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25596524618115481 / 1250000000000000 : ℝ) (189631611157
    / 100000000000 : ℝ) (7818861458072638729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1518_product_lower :
    (26189883993115481 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (759 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1518_leftExp
    (by norm_num : (0 : ℝ) ≤ (66692005819 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1518_product_upper :
    Real.pi * Real.exp (1519 / 800 : ℝ) ≤ (41956240265493463 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1518_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1518_endpointLower :
    (1269 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (759 / 800 : ℝ) (1519 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26189883993115481 / 1250000000000000 : ℝ) (Real.pi * Real.exp (759 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1518_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1519 / 800 : ℝ) - (759 / 1600 : ℝ)) ≤
      (8029035340635623249 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1518_denomUpper
    linarith [hpThetaJensenCell1518_product_upper]
  have hi : (1 / (8029035340635623249 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1519 / 800 : ℝ) - (759 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8029035340635623249 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8029035340635623249 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((759 / 1600 : ℝ) - Real.pi * Real.exp (1519 / 800 : ℝ)) := by
    rw [show (759 / 1600 : ℝ) - Real.pi * Real.exp (1519 / 800 : ℝ) =
      -(Real.pi * Real.exp (1519 / 800 : ℝ) - (759 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (759 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (759 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1518_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8029035340635623249 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1518_endpointUpper :
    hpThetaJensenKernelEndpointUpper (759 / 800 : ℝ) (1519 / 1600 : ℝ) ≤ (41919 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1519 / 800 : ℝ)) (41956240265493463 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1519 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1518_product_upper
  have hD : (7818861458072638729 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (759 / 400 : ℝ) - (1519 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1518_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1518_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (759 / 400 : ℝ) - (1519 / 3200 : ℝ)) ≤
      (1 / (7818861458072638729 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7818861458072638729 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1519 / 3200 : ℝ) - Real.pi * Real.exp (759 / 400 : ℝ)) ≤
      (2 / (7818861458072638729 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1519 / 3200 : ℝ) - Real.pi * Real.exp (759 / 400 : ℝ) =
      -(Real.pi * Real.exp (759 / 400 : ℝ) - (1519 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41956240265493463 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (41956240265493463 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1518_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (759 / 800 : ℝ) (1519 / 1600 : ℝ)) :
    (1269 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (41919 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1518_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1518_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1519_leftExp :
    (8346927869 / 1250000000 : ℝ) ≤ Real.exp (1519 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1519 / 800 : ℝ) (212226330957 / 200000000000 : ℝ)
    (8346927869 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1519_rightExp :
    Real.exp (19 / 10 : ℝ) ≤ (8357368053 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 10 : ℝ) (1061173106051 / 1000000000000 : ℝ)
    (8357368053 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1519_denomUpper :
    Real.exp (25662089598728429 / 1250000000000000 : ℝ) ≤ (8239922471204165077 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (25662089598728429 / 1250000000000000 : ℝ) (379885391729
    / 200000000000 : ℝ) (8239922471204165077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1519_denomLower :
    (1604793034317557807 / 2000000000 : ℝ) ≤ Real.exp (3203611477228431 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3203611477228431 / 156250000000000 : ℝ) (948925596811 /
    500000000000 : ℝ) (1604793034317557807 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1519_product_lower :
    (3277830227228431 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1519 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1519_leftExp
    (by norm_num : (0 : ℝ) ≤ (8346927869 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1519_product_upper :
    Real.pi * Real.exp (19 / 10 : ℝ) ≤ (26255448973728429 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1519_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1519_endpointLower :
    (39671 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1519 / 1600 : ℝ) (19 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3277830227228431 / 156250000000000 : ℝ) (Real.pi * Real.exp (1519 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1519_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 10 : ℝ) - (1519 / 3200 : ℝ)) ≤
      (8239922471204165077 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1519_denomUpper
    linarith [hpThetaJensenCell1519_product_upper]
  have hi : (1 / (8239922471204165077 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 10 : ℝ) - (1519 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8239922471204165077 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8239922471204165077 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1519 / 3200 : ℝ) - Real.pi * Real.exp (19 / 10 : ℝ)) := by
    rw [show (1519 / 3200 : ℝ) - Real.pi * Real.exp (19 / 10 : ℝ) =
      -(Real.pi * Real.exp (19 / 10 : ℝ) - (1519 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1519 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1519 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1519_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8239922471204165077 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1519_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1519 / 1600 : ℝ) (19 / 20 : ℝ) ≤ (40953 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 10 : ℝ)) (26255448973728429 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 20 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1519_product_upper
  have hD : (1604793034317557807 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1519 / 800 : ℝ) - (19 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell1519_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1519_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1519 / 800 : ℝ) - (19 / 40 : ℝ)) ≤
      (1 / (1604793034317557807 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1604793034317557807 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 40 : ℝ) - Real.pi * Real.exp (1519 / 800 : ℝ)) ≤
      (2 / (1604793034317557807 / 2000000000 : ℝ) : ℝ) := by
    rw [show (19 / 40 : ℝ) - Real.pi * Real.exp (1519 / 800 : ℝ) =
      -(Real.pi * Real.exp (1519 / 800 : ℝ) - (19 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26255448973728429 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (26255448973728429 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1519_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1519 / 1600 : ℝ) (19 / 20 : ℝ)) :
    (39671 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40953 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1519_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1519_endpointUpper

def hpThetaJensenCellsBatch075Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3841 / 625000000 : ℝ)
  | 1 => (30037 / 5000000000 : ℝ)
  | 2 => (58721 / 10000000000 : ℝ)
  | 3 => (57397 / 10000000000 : ℝ)
  | 4 => (561 / 100000000 : ℝ)
  | 5 => (3427 / 625000000 : ℝ)
  | 6 => (5359 / 1000000000 : ℝ)
  | 7 => (419 / 80000000 : ℝ)
  | 8 => (10237 / 2000000000 : ℝ)
  | 9 => (50021 / 10000000000 : ℝ)
  | 10 => (24441 / 5000000000 : ℝ)
  | 11 => (5971 / 1250000000 : ℝ)
  | 12 => (46677 / 10000000000 : ℝ)
  | 13 => (45609 / 10000000000 : ℝ)
  | 14 => (8913 / 2000000000 : ℝ)
  | 15 => (43543 / 10000000000 : ℝ)
  | 16 => (42543 / 10000000000 : ℝ)
  | 17 => (8313 / 2000000000 : ℝ)
  | 18 => (1269 / 312500000 : ℝ)
  | 19 => (39671 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch075Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (31701 / 5000000000 : ℝ)
  | 1 => (61979 / 10000000000 : ℝ)
  | 2 => (12117 / 2000000000 : ℝ)
  | 3 => (59221 / 10000000000 : ℝ)
  | 4 => (11577 / 2000000000 : ℝ)
  | 5 => (28289 / 5000000000 : ℝ)
  | 6 => (55299 / 10000000000 : ℝ)
  | 7 => (27023 / 5000000000 : ℝ)
  | 8 => (52821 / 10000000000 : ℝ)
  | 9 => (51621 / 10000000000 : ℝ)
  | 10 => (50447 / 10000000000 : ℝ)
  | 11 => (49299 / 10000000000 : ℝ)
  | 12 => (24087 / 5000000000 : ℝ)
  | 13 => (23537 / 5000000000 : ℝ)
  | 14 => (22999 / 5000000000 : ℝ)
  | 15 => (2809 / 625000000 : ℝ)
  | 16 => (21957 / 5000000000 : ℝ)
  | 17 => (8581 / 2000000000 : ℝ)
  | 18 => (41919 / 10000000000 : ℝ)
  | 19 => (40953 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch075_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch075Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch075Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1500_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1501_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1502_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1503_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1504_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1505_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1506_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1507_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1508_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1509_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1510_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1511_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1512_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1513_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1514_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1515_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1516_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1517_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1518_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1519_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper] at h ⊢
    exact h

end HodgeProofHP
