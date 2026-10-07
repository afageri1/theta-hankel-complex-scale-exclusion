import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1000_leftExp :
    (17451714787 / 5000000000 : ℝ) ≤ Real.exp (5 / 4 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5 / 4 : ℝ) (129979433917 / 125000000000 : ℝ)
    (17451714787 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1000_rightExp :
    Real.exp (1001 / 800 : ℝ) ≤ (17473543071 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1001 / 800 : ℝ) (1039876090703 / 1000000000000 : ℝ)
    (17473543071 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1000_denomUpper :
    Real.exp (53332260597052103 / 5000000000000000 : ℝ) ≤ (214462468893127 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53332260597052103 / 5000000000000000 : ℝ) (348900767023
    / 250000000000 : ℝ) (214462468893127 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1000_denomLower :
    (211474335434633 / 5000000000 : ℝ) ≤ Real.exp (6657763132640113 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6657763132640113 / 625000000000000 : ℝ) (697495634611 /
    500000000000 : ℝ) (211474335434633 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1000_product_lower :
    (6853270945140113 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (5 / 4 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1000_leftExp
    (by norm_num : (0 : ℝ) ≤ (17451714787 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1000_product_upper :
    Real.pi * Real.exp (1001 / 800 : ℝ) ≤ (54894760597052103 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1000_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1000_endpointLower :
    (3871577 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (5 / 8 : ℝ) (1001 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6853270945140113 / 625000000000000 : ℝ) (Real.pi * Real.exp (5 / 4 : ℝ))
    (by norm_num) hpThetaJensenCell1000_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1001 / 800 : ℝ) - (5 / 16 : ℝ)) ≤
      (214462468893127 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1000_denomUpper
    linarith [hpThetaJensenCell1000_product_upper]
  have hi : (1 / (214462468893127 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1001 / 800 : ℝ) - (5 / 16 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (214462468893127 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (214462468893127 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((5 / 16 : ℝ) - Real.pi * Real.exp (1001 / 800 : ℝ)) := by
    rw [show (5 / 16 : ℝ) - Real.pi * Real.exp (1001 / 800 : ℝ) =
      -(Real.pi * Real.exp (1001 / 800 : ℝ) - (5 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (5 / 4 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (5 / 4 : ℝ)) := by
    have h := hpThetaJensenCell1000_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (214462468893127 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1000_endpointUpper :
    hpThetaJensenKernelEndpointUpper (5 / 8 : ℝ) (1001 / 1600 : ℝ) ≤ (197363013 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1001 / 800 : ℝ)) (54894760597052103 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1001 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1000_product_upper
  have hD : (211474335434633 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (5 / 4 : ℝ) - (1001 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1000_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1000_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (5 / 4 : ℝ) - (1001 / 3200 : ℝ)) ≤
      (1 / (211474335434633 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (211474335434633 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1001 / 3200 : ℝ) - Real.pi * Real.exp (5 / 4 : ℝ)) ≤
      (2 / (211474335434633 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1001 / 3200 : ℝ) - Real.pi * Real.exp (5 / 4 : ℝ) =
      -(Real.pi * Real.exp (5 / 4 : ℝ) - (1001 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54894760597052103 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (54894760597052103 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1000_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (5 / 8 : ℝ) (1001 / 1600 : ℝ)) :
    (3871577 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (197363013 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1000_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1000_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1001_leftExp :
    (1747354307 / 500000000 : ℝ) ≤ Real.exp (1001 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1001 / 800 : ℝ) (519938045351 / 500000000000 : ℝ)
    (1747354307 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1001_rightExp :
    Real.exp (501 / 400 : ℝ) ≤ (34990797313 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (501 / 400 : ℝ) (129989588957 / 125000000000 : ℝ)
    (34990797313 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1001_denomUpper :
    Real.exp (106798718902939609 / 10000000000000000 : ℝ) ≤ (434719808133309 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (106798718902939609 / 10000000000000000 : ℝ)
    (349047115469 / 250000000000 : ℝ) (434719808133309 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1001_denomLower :
    (85731089029821 / 2000000000 : ℝ) ≤ Real.exp (666613976504593 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (666613976504593 / 62500000000000 : ℝ) (1395575658047 /
    1000000000000 : ℝ) (85731089029821 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1001_product_lower :
    (686184289004593 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (1001 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1001_leftExp
    (by norm_num : (0 : ℝ) ≤ (1747354307 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1001_product_upper :
    Real.pi * Real.exp (501 / 400 : ℝ) ≤ (109926843902939609 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1001_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1001_endpointLower :
    (9575721 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1001 / 1600 : ℝ) (501 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (686184289004593 / 62500000000000 : ℝ) (Real.pi * Real.exp (1001 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1001_product_lower
  have hD : Real.exp (Real.pi * Real.exp (501 / 400 : ℝ) - (1001 / 3200 : ℝ)) ≤
      (434719808133309 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1001_denomUpper
    linarith [hpThetaJensenCell1001_product_upper]
  have hi : (1 / (434719808133309 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (501 / 400 : ℝ) - (1001 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (434719808133309 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (434719808133309 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1001 / 3200 : ℝ) - Real.pi * Real.exp (501 / 400 : ℝ)) := by
    rw [show (1001 / 3200 : ℝ) - Real.pi * Real.exp (501 / 400 : ℝ) =
      -(Real.pi * Real.exp (501 / 400 : ℝ) - (1001 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1001 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1001 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1001_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (434719808133309 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1001_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1001 / 1600 : ℝ) (501 / 800 : ℝ) ≤ (195261521 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (501 / 400 : ℝ)) (109926843902939609 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (501 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1001_product_upper
  have hD : (85731089029821 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1001 / 800 : ℝ) - (501 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1001_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1001_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1001 / 800 : ℝ) - (501 / 1600 : ℝ)) ≤
      (1 / (85731089029821 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (85731089029821 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((501 / 1600 : ℝ) - Real.pi * Real.exp (1001 / 800 : ℝ)) ≤
      (2 / (85731089029821 / 2000000000 : ℝ) : ℝ) := by
    rw [show (501 / 1600 : ℝ) - Real.pi * Real.exp (1001 / 800 : ℝ) =
      -(Real.pi * Real.exp (1001 / 800 : ℝ) - (501 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (109926843902939609 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (109926843902939609 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1001_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1001 / 1600 : ℝ) (501 / 800 : ℝ)) :
    (9575721 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (195261521 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1001_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1001_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1002_leftExp :
    (34990797311 / 10000000000 : ℝ) ≤ Real.exp (501 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (501 / 400 : ℝ) (207983342331 / 200000000000 : ℝ)
    (34990797311 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1002_rightExp :
    Real.exp (1003 / 800 : ℝ) ≤ (17517281579 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1003 / 800 : ℝ) (259989333549 / 250000000000 : ℝ)
    (17517281579 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1002_denomUpper :
    Real.exp (53466544187615347 / 5000000000000000 : ℝ) ≤ (220300268145349 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53466544187615347 / 5000000000000000 : ℝ) (69838742547 /
    50000000000 : ℝ) (220300268145349 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1002_denomLower :
    (434446672692419 / 10000000000 : ℝ) ≤ Real.exp (13349054238232389 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13349054238232389 / 1250000000000000 : ℝ) (1396161040143
    / 1000000000000 : ℝ) (434446672692419 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1002_product_lower :
    (13740851113232389 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (501 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1002_leftExp
    (by norm_num : (0 : ℝ) ≤ (34990797311 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1002_product_upper :
    Real.pi * Real.exp (1003 / 800 : ℝ) ≤ (55032169187615347 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1002_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1002_endpointLower :
    (23683587 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (501 / 800 : ℝ) (1003 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13740851113232389 / 1250000000000000 : ℝ) (Real.pi * Real.exp (501 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1002_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1003 / 800 : ℝ) - (501 / 1600 : ℝ)) ≤
      (220300268145349 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1002_denomUpper
    linarith [hpThetaJensenCell1002_product_upper]
  have hi : (1 / (220300268145349 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1003 / 800 : ℝ) - (501 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (220300268145349 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (220300268145349 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((501 / 1600 : ℝ) - Real.pi * Real.exp (1003 / 800 : ℝ)) := by
    rw [show (501 / 1600 : ℝ) - Real.pi * Real.exp (1003 / 800 : ℝ) =
      -(Real.pi * Real.exp (1003 / 800 : ℝ) - (501 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (501 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (501 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1002_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (220300268145349 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1002_endpointUpper :
    hpThetaJensenKernelEndpointUpper (501 / 800 : ℝ) (1003 / 1600 : ℝ) ≤ (38635807 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1003 / 800 : ℝ)) (55032169187615347 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1003 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1002_product_upper
  have hD : (434446672692419 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (501 / 400 : ℝ) - (1003 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1002_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1002_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (501 / 400 : ℝ) - (1003 / 3200 : ℝ)) ≤
      (1 / (434446672692419 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (434446672692419 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1003 / 3200 : ℝ) - Real.pi * Real.exp (501 / 400 : ℝ)) ≤
      (2 / (434446672692419 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1003 / 3200 : ℝ) - Real.pi * Real.exp (501 / 400 : ℝ) =
      -(Real.pi * Real.exp (501 / 400 : ℝ) - (1003 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55032169187615347 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (55032169187615347 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1002_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (501 / 800 : ℝ) (1003 / 1600 : ℝ)) :
    (23683587 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (38635807 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1002_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1002_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1003_leftExp :
    (8758640789 / 2500000000 : ℝ) ≤ Real.exp (1003 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1003 / 800 : ℝ) (207991466839 / 200000000000 : ℝ)
    (8758640789 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1003_rightExp :
    Real.exp (251 / 200 : ℝ) ≤ (274049873 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (251 / 200 : ℝ) (1039997958323 / 1000000000000 : ℝ)
    (274049873 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1003_denomUpper :
    Real.exp (836465857980189 / 78125000000000 : ℝ) ≤ (446568496499687 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (836465857980189 / 78125000000000 : ℝ) (1397362237251 /
    1000000000000 : ℝ) (446568496499687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1003_denomLower :
    (440323704047463 / 10000000000 : ℝ) ≤ Real.exp (3341462604199511 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3341462604199511 / 312500000000000 : ℝ) (1396747417499 /
    1000000000000 : ℝ) (440323704047463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1003_product_lower :
    (3439509479199511 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1003 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1003_leftExp
    (by norm_num : (0 : ℝ) ≤ (8758640789 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1003_product_upper :
    Real.pi * Real.exp (251 / 200 : ℝ) ≤ (860953162667689 / 78125000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1003_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1003_endpointLower :
    (46860387 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1003 / 1600 : ℝ) (251 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3439509479199511 / 312500000000000 : ℝ) (Real.pi * Real.exp (1003 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1003_product_lower
  have hD : Real.exp (Real.pi * Real.exp (251 / 200 : ℝ) - (1003 / 3200 : ℝ)) ≤
      (446568496499687 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1003_denomUpper
    linarith [hpThetaJensenCell1003_product_upper]
  have hi : (1 / (446568496499687 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (251 / 200 : ℝ) - (1003 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (446568496499687 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (446568496499687 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1003 / 3200 : ℝ) - Real.pi * Real.exp (251 / 200 : ℝ)) := by
    rw [show (1003 / 3200 : ℝ) - Real.pi * Real.exp (251 / 200 : ℝ) =
      -(Real.pi * Real.exp (251 / 200 : ℝ) - (1003 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1003 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1003 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1003_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (446568496499687 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1003_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1003 / 1600 : ℝ) (251 / 400 : ℝ) ≤ (191115423 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (251 / 200 : ℝ)) (860953162667689 / 78125000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (251 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1003_product_upper
  have hD : (440323704047463 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1003 / 800 : ℝ) - (251 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1003_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1003_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1003 / 800 : ℝ) - (251 / 800 : ℝ)) ≤
      (1 / (440323704047463 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (440323704047463 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((251 / 800 : ℝ) - Real.pi * Real.exp (1003 / 800 : ℝ)) ≤
      (2 / (440323704047463 / 10000000000 : ℝ) : ℝ) := by
    rw [show (251 / 800 : ℝ) - Real.pi * Real.exp (1003 / 800 : ℝ) =
      -(Real.pi * Real.exp (1003 / 800 : ℝ) - (251 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (860953162667689 / 78125000000000 : ℝ) ^ 2 - 6 *
      (860953162667689 / 78125000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1003_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1003 / 1600 : ℝ) (251 / 400 : ℝ)) :
    (46860387 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (191115423 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1003_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1003_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1004_leftExp :
    (17539191871 / 5000000000 : ℝ) ≤ Real.exp (251 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (251 / 200 : ℝ) (519998979161 / 500000000000 : ℝ)
    (17539191871 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1004_rightExp :
    Real.exp (201 / 160 : ℝ) ≤ (35122259141 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (201 / 160 : ℝ) (1040038584037 / 1000000000000 : ℝ)
    (35122259141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1004_denomUpper :
    Real.exp (107202343461551613 / 10000000000000000 : ℝ) ≤ (452625086950849 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (107202343461551613 / 10000000000000000 : ℝ)
    (698975311411 / 500000000000 : ℝ) (452625086950849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1004_denomLower :
    (446287912591209 / 10000000000 : ℝ) ≤ Real.exp (6691334046049829 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6691334046049829 / 625000000000000 : ℝ) (698667396041 /
    500000000000 : ℝ) (446287912591209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1004_product_lower :
    (6887623108549829 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (251 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1004_leftExp
    (by norm_num : (0 : ℝ) ≤ (17539191871 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1004_product_upper :
    Real.pi * Real.exp (201 / 160 : ℝ) ≤ (110339843461551613 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1004_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1004_endpointLower :
    (185432843 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (251 / 400 : ℝ) (201 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6887623108549829 / 625000000000000 : ℝ) (Real.pi * Real.exp (251 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1004_product_lower
  have hD : Real.exp (Real.pi * Real.exp (201 / 160 : ℝ) - (251 / 800 : ℝ)) ≤
      (452625086950849 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1004_denomUpper
    linarith [hpThetaJensenCell1004_product_upper]
  have hi : (1 / (452625086950849 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (201 / 160 : ℝ) - (251 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (452625086950849 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (452625086950849 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((251 / 800 : ℝ) - Real.pi * Real.exp (201 / 160 : ℝ)) := by
    rw [show (251 / 800 : ℝ) - Real.pi * Real.exp (201 / 160 : ℝ) =
      -(Real.pi * Real.exp (201 / 160 : ℝ) - (251 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (251 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (251 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1004_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (452625086950849 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1004_endpointUpper :
    hpThetaJensenKernelEndpointUpper (251 / 400 : ℝ) (201 / 320 : ℝ) ≤ (189070549 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (201 / 160 : ℝ)) (110339843461551613 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (201 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1004_product_upper
  have hD : (446287912591209 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (251 / 200 : ℝ) - (201 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1004_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1004_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (251 / 200 : ℝ) - (201 / 640 : ℝ)) ≤
      (1 / (446287912591209 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (446287912591209 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((201 / 640 : ℝ) - Real.pi * Real.exp (251 / 200 : ℝ)) ≤
      (2 / (446287912591209 / 10000000000 : ℝ) : ℝ) := by
    rw [show (201 / 640 : ℝ) - Real.pi * Real.exp (251 / 200 : ℝ) =
      -(Real.pi * Real.exp (251 / 200 : ℝ) - (201 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (110339843461551613 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (110339843461551613 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1004_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (251 / 400 : ℝ) (201 / 320 : ℝ)) :
    (185432843 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (189070549 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1004_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1004_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1005_leftExp :
    (35122259139 / 10000000000 : ℝ) ≤ Real.exp (201 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (201 / 160 : ℝ) (260009646009 / 250000000000 : ℝ)
    (35122259139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1005_rightExp :
    Real.exp (503 / 400 : ℝ) ≤ (7033237883 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (503 / 400 : ℝ) (1040079211337 / 1000000000000 : ℝ)
    (7033237883 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1005_denomUpper :
    Real.exp (21467445900567619 / 2000000000000000 : ℝ) ≤ (458771729179143 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (21467445900567619 / 2000000000000000 : ℝ) (1398540009611
    / 1000000000000 : ℝ) (458771729179143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1005_denomLower :
    (452340695634893 / 10000000000 : ℝ) ≤ Real.exp (13399507291626161 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13399507291626161 / 1250000000000000 : ℝ) (279584633181
    / 200000000000 : ℝ) (452340695634893 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1005_product_lower :
    (13792476041626161 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (201 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1005_leftExp
    (by norm_num : (0 : ℝ) ≤ (35122259139 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1005_product_upper :
    Real.pi * Real.exp (503 / 400 : ℝ) ≤ (22095570900567619 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1005_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1005_endpointLower :
    (11465153 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (201 / 320 : ℝ) (503 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13792476041626161 / 1250000000000000 : ℝ) (Real.pi * Real.exp (201 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1005_product_lower
  have hD : Real.exp (Real.pi * Real.exp (503 / 400 : ℝ) - (201 / 640 : ℝ)) ≤
      (458771729179143 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1005_denomUpper
    linarith [hpThetaJensenCell1005_product_upper]
  have hi : (1 / (458771729179143 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (503 / 400 : ℝ) - (201 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (458771729179143 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (458771729179143 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((201 / 640 : ℝ) - Real.pi * Real.exp (503 / 400 : ℝ)) := by
    rw [show (201 / 640 : ℝ) - Real.pi * Real.exp (503 / 400 : ℝ) =
      -(Real.pi * Real.exp (503 / 400 : ℝ) - (201 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (201 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (201 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1005_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (458771729179143 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1005_endpointUpper :
    hpThetaJensenKernelEndpointUpper (201 / 320 : ℝ) (503 / 800 : ℝ) ≤ (187044281 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (503 / 400 : ℝ)) (22095570900567619 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (503 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1005_product_upper
  have hD : (452340695634893 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (201 / 160 : ℝ) - (503 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1005_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1005_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (201 / 160 : ℝ) - (503 / 1600 : ℝ)) ≤
      (1 / (452340695634893 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (452340695634893 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((503 / 1600 : ℝ) - Real.pi * Real.exp (201 / 160 : ℝ)) ≤
      (2 / (452340695634893 / 10000000000 : ℝ) : ℝ) := by
    rw [show (503 / 1600 : ℝ) - Real.pi * Real.exp (201 / 160 : ℝ) =
      -(Real.pi * Real.exp (201 / 160 : ℝ) - (503 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22095570900567619 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (22095570900567619 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1005_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (201 / 320 : ℝ) (503 / 800 : ℝ)) :
    (11465153 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (187044281 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1005_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1005_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1006_leftExp :
    (35166189413 / 10000000000 : ℝ) ≤ Real.exp (503 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (503 / 400 : ℝ) (130009901417 / 125000000000 : ℝ)
    (35166189413 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1006_rightExp :
    Real.exp (1007 / 800 : ℝ) ≤ (35210174637 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1007 / 800 : ℝ) (41604793609 / 40000000000 : ℝ)
    (35210174637 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1006_denomUpper :
    Real.exp (107472288168376741 / 10000000000000000 : ℝ) ≤ (465009869852013 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (107472288168376741 / 10000000000000000 : ℝ)
    (349782599913 / 250000000000 : ℝ) (465009869852013 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1006_denomLower :
    (458483473819451 / 10000000000 : ℝ) ≤ Real.exp (13416368041295687 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13416368041295687 / 1250000000000000 : ℝ) (699256270463
    / 500000000000 : ℝ) (458483473819451 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1006_product_lower :
    (13809727416295687 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (503 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1006_leftExp
    (by norm_num : (0 : ℝ) ≤ (35166189413 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1006_product_upper :
    Real.pi * Real.exp (1007 / 800 : ℝ) ≤ (110616038168376741 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1006_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1006_endpointLower :
    (90735117 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (503 / 800 : ℝ) (1007 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13809727416295687 / 1250000000000000 : ℝ) (Real.pi * Real.exp (503 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1006_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1007 / 800 : ℝ) - (503 / 1600 : ℝ)) ≤
      (465009869852013 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1006_denomUpper
    linarith [hpThetaJensenCell1006_product_upper]
  have hi : (1 / (465009869852013 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1007 / 800 : ℝ) - (503 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (465009869852013 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (465009869852013 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((503 / 1600 : ℝ) - Real.pi * Real.exp (1007 / 800 : ℝ)) := by
    rw [show (503 / 1600 : ℝ) - Real.pi * Real.exp (1007 / 800 : ℝ) =
      -(Real.pi * Real.exp (1007 / 800 : ℝ) - (503 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (503 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (503 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1006_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (465009869852013 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1006_endpointUpper :
    hpThetaJensenKernelEndpointUpper (503 / 800 : ℝ) (1007 / 1600 : ℝ) ≤ (37007297 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1007 / 800 : ℝ)) (110616038168376741 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1007 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1006_product_upper
  have hD : (458483473819451 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (503 / 400 : ℝ) - (1007 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1006_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1006_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (503 / 400 : ℝ) - (1007 / 3200 : ℝ)) ≤
      (1 / (458483473819451 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (458483473819451 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1007 / 3200 : ℝ) - Real.pi * Real.exp (503 / 400 : ℝ)) ≤
      (2 / (458483473819451 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1007 / 3200 : ℝ) - Real.pi * Real.exp (503 / 400 : ℝ) =
      -(Real.pi * Real.exp (503 / 400 : ℝ) - (1007 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (110616038168376741 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (110616038168376741 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1006_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (503 / 800 : ℝ) (1007 / 1600 : ℝ)) :
    (90735117 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (37007297 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1006_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1006_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1007_leftExp :
    (7042034927 / 2000000000 : ℝ) ≤ Real.exp (1007 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1007 / 800 : ℝ) (32503745007 / 31250000000 : ℝ)
    (7042034927 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1007_rightExp :
    Real.exp (63 / 50 : ℝ) ≤ (282033719 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 50 : ℝ) (10401604707 / 10000000000 : ℝ)
    (282033719 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1007_denomUpper :
    Real.exp (860860157374367 / 80000000000000 : ℝ) ≤ (471340980034271 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (860860157374367 / 80000000000000 : ℝ) (1399721794941 /
    1000000000000 : ℝ) (471340980034271 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1007_denomLower :
    (116179423225631 / 2500000000 : ℝ) ≤ Real.exp (2686650073797973 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2686650073797973 / 250000000000000 : ℝ) (1399102919179 /
    1000000000000 : ℝ) (116179423225631 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1007_product_lower :
    (2765400073797973 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1007 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1007_leftExp
    (by norm_num : (0 : ℝ) ≤ (7042034927 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1007_product_upper :
    Real.pi * Real.exp (63 / 50 : ℝ) ≤ (886035157374367 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1007_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1007_endpointLower :
    (17951607 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1007 / 1600 : ℝ) (63 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2765400073797973 / 250000000000000 : ℝ) (Real.pi * Real.exp (1007 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1007_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 50 : ℝ) - (1007 / 3200 : ℝ)) ≤
      (471340980034271 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1007_denomUpper
    linarith [hpThetaJensenCell1007_product_upper]
  have hi : (1 / (471340980034271 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 50 : ℝ) - (1007 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (471340980034271 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (471340980034271 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1007 / 3200 : ℝ) - Real.pi * Real.exp (63 / 50 : ℝ)) := by
    rw [show (1007 / 3200 : ℝ) - Real.pi * Real.exp (63 / 50 : ℝ) =
      -(Real.pi * Real.exp (63 / 50 : ℝ) - (1007 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1007 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1007 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1007_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (471340980034271 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1007_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1007 / 1600 : ℝ) (63 / 100 : ℝ) ≤ (18304703 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 50 : ℝ)) (886035157374367 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1007_product_upper
  have hD : (116179423225631 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1007 / 800 : ℝ) - (63 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1007_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1007_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1007 / 800 : ℝ) - (63 / 200 : ℝ)) ≤
      (1 / (116179423225631 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (116179423225631 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 200 : ℝ) - Real.pi * Real.exp (1007 / 800 : ℝ)) ≤
      (2 / (116179423225631 / 2500000000 : ℝ) : ℝ) := by
    rw [show (63 / 200 : ℝ) - Real.pi * Real.exp (1007 / 800 : ℝ) =
      -(Real.pi * Real.exp (1007 / 800 : ℝ) - (63 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (886035157374367 / 80000000000000 : ℝ) ^ 2 - 6 *
      (886035157374367 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1007_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1007 / 1600 : ℝ) (63 / 100 : ℝ)) :
    (17951607 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (18304703 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1007_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1007_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1008_leftExp :
    (35254214873 / 10000000000 : ℝ) ≤ Real.exp (63 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 50 : ℝ) (1040160470699 / 1000000000000 : ℝ)
    (35254214873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1008_rightExp :
    Real.exp (1009 / 800 : ℝ) ≤ (35298310197 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1009 / 800 : ℝ) (520100551381 / 500000000000 : ℝ)
    (35298310197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1008_denomUpper :
    Real.exp (107742924226723821 / 10000000000000000 : ℝ) ≤ (238883278018389 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (107742924226723821 / 10000000000000000 : ℝ) (56012567899
    / 40000000000 : ℝ) (238883278018389 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1008_denomLower :
    (29440301438313 / 625000000 : ℝ) ≤ Real.exp (13450154301412227 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13450154301412227 / 1250000000000000 : ℝ) (1399694302659
    / 1000000000000 : ℝ) (29440301438313 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1008_product_lower :
    (13844294926412227 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (63 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1008_leftExp
    (by norm_num : (0 : ℝ) ≤ (35254214873 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1008_product_upper :
    Real.pi * Real.exp (1009 / 800 : ℝ) ≤ (110892924226723821 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1008_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1008_endpointLower :
    (88789913 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 100 : ℝ) (1009 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13844294926412227 / 1250000000000000 : ℝ) (Real.pi * Real.exp (63 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1008_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1009 / 800 : ℝ) - (63 / 200 : ℝ)) ≤
      (238883278018389 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1008_denomUpper
    linarith [hpThetaJensenCell1008_product_upper]
  have hi : (1 / (238883278018389 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1009 / 800 : ℝ) - (63 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (238883278018389 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (238883278018389 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 200 : ℝ) - Real.pi * Real.exp (1009 / 800 : ℝ)) := by
    rw [show (63 / 200 : ℝ) - Real.pi * Real.exp (1009 / 800 : ℝ) =
      -(Real.pi * Real.exp (1009 / 800 : ℝ) - (63 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1008_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (238883278018389 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1008_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 100 : ℝ) (1009 / 1600 : ℝ) ≤ (22634473 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1009 / 800 : ℝ)) (110892924226723821 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1009 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1008_product_upper
  have hD : (29440301438313 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 50 : ℝ) - (1009 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1008_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1008_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 50 : ℝ) - (1009 / 3200 : ℝ)) ≤
      (1 / (29440301438313 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29440301438313 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1009 / 3200 : ℝ) - Real.pi * Real.exp (63 / 50 : ℝ)) ≤
      (2 / (29440301438313 / 625000000 : ℝ) : ℝ) := by
    rw [show (1009 / 3200 : ℝ) - Real.pi * Real.exp (63 / 50 : ℝ) =
      -(Real.pi * Real.exp (63 / 50 : ℝ) - (1009 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (110892924226723821 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (110892924226723821 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1008_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 100 : ℝ) (1009 / 1600 : ℝ)) :
    (88789913 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22634473 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1008_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1008_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1009_leftExp :
    (7059662039 / 2000000000 : ℝ) ≤ Real.exp (1009 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1009 / 800 : ℝ) (1040201102761 / 1000000000000 : ℝ)
    (7059662039 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1009_rightExp :
    Real.exp (101 / 80 : ℝ) ≤ (35342460673 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (101 / 80 : ℝ) (1040241736411 / 1000000000000 : ℝ)
    (35342460673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1009_denomUpper :
    Real.exp (107878502053072089 / 10000000000000000 : ℝ) ≤ (96857624045771 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (107878502053072089 / 10000000000000000 : ℝ)
    (350226902321 / 250000000000 : ℝ) (96857624045771 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1009_denomLower :
    (238733179771073 / 5000000000 : ℝ) ≤ Real.exp (2693415973053261 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2693415973053261 / 250000000000000 : ℝ) (280057338673 /
    200000000000 : ℝ) (238733179771073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1009_product_lower :
    (2772322223053261 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1009 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1009_leftExp
    (by norm_num : (0 : ℝ) ≤ (7059662039 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1009_product_upper :
    Real.pi * Real.exp (101 / 80 : ℝ) ≤ (111031627053072089 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1009_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1009_endpointLower :
    (43915343 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1009 / 1600 : ℝ) (101 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2772322223053261 / 250000000000000 : ℝ) (Real.pi * Real.exp (1009 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1009_product_lower
  have hD : Real.exp (Real.pi * Real.exp (101 / 80 : ℝ) - (1009 / 3200 : ℝ)) ≤
      (96857624045771 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1009_denomUpper
    linarith [hpThetaJensenCell1009_product_upper]
  have hi : (1 / (96857624045771 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (101 / 80 : ℝ) - (1009 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (96857624045771 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (96857624045771 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1009 / 3200 : ℝ) - Real.pi * Real.exp (101 / 80 : ℝ)) := by
    rw [show (1009 / 3200 : ℝ) - Real.pi * Real.exp (101 / 80 : ℝ) =
      -(Real.pi * Real.exp (101 / 80 : ℝ) - (1009 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1009 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1009 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1009_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (96857624045771 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1009_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1009 / 1600 : ℝ) (101 / 160 : ℝ) ≤ (22390327 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (101 / 80 : ℝ)) (111031627053072089 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (101 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1009_product_upper
  have hD : (238733179771073 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1009 / 800 : ℝ) - (101 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1009_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1009_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1009 / 800 : ℝ) - (101 / 320 : ℝ)) ≤
      (1 / (238733179771073 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (238733179771073 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((101 / 320 : ℝ) - Real.pi * Real.exp (1009 / 800 : ℝ)) ≤
      (2 / (238733179771073 / 5000000000 : ℝ) : ℝ) := by
    rw [show (101 / 320 : ℝ) - Real.pi * Real.exp (1009 / 800 : ℝ) =
      -(Real.pi * Real.exp (1009 / 800 : ℝ) - (101 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (111031627053072089 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (111031627053072089 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1009_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1009 / 1600 : ℝ) (101 / 160 : ℝ)) :
    (43915343 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22390327 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1009_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1009_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1010_leftExp :
    (35342460671 / 10000000000 : ℝ) ≤ Real.exp (101 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (101 / 80 : ℝ) (104024173641 / 100000000000 : ℝ)
    (35342460671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1010_rightExp :
    Real.exp (1011 / 800 : ℝ) ≤ (8846666593 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1011 / 800 : ℝ) (16254412057 / 15625000000 : ℝ)
    (8846666593 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1010_denomUpper :
    Real.exp (27003563341902649 / 2500000000000000 : ℝ) ≤ (490907221058113 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (27003563341902649 / 2500000000000000 : ℝ) (1401502032389
    / 1000000000000 : ℝ) (490907221058113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1010_denomLower :
    (483983823880189 / 10000000000 : ℝ) ≤ Real.exp (13484027088041029 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13484027088041029 / 1250000000000000 : ℝ) (56035203733 /
    40000000000 : ℝ) (483983823880189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1010_product_lower :
    (13878948963041029 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (101 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1010_leftExp
    (by norm_num : (0 : ℝ) ≤ (35342460671 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1010_product_upper :
    Real.pi * Real.exp (1011 / 800 : ℝ) ≤ (27792625841902649 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1010_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1010_endpointLower :
    (8688029 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (101 / 160 : ℝ) (1011 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13878948963041029 / 1250000000000000 : ℝ) (Real.pi * Real.exp (101 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1010_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1011 / 800 : ℝ) - (101 / 320 : ℝ)) ≤
      (490907221058113 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1010_denomUpper
    linarith [hpThetaJensenCell1010_product_upper]
  have hi : (1 / (490907221058113 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1011 / 800 : ℝ) - (101 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (490907221058113 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (490907221058113 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((101 / 320 : ℝ) - Real.pi * Real.exp (1011 / 800 : ℝ)) := by
    rw [show (101 / 320 : ℝ) - Real.pi * Real.exp (1011 / 800 : ℝ) =
      -(Real.pi * Real.exp (1011 / 800 : ℝ) - (101 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (101 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (101 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1010_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (490907221058113 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1010_endpointUpper :
    hpThetaJensenKernelEndpointUpper (101 / 160 : ℝ) (1011 / 1600 : ℝ) ≤ (44296849 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1011 / 800 : ℝ)) (27792625841902649 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1011 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1010_product_upper
  have hD : (483983823880189 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (101 / 80 : ℝ) - (1011 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1010_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1010_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (101 / 80 : ℝ) - (1011 / 3200 : ℝ)) ≤
      (1 / (483983823880189 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (483983823880189 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1011 / 3200 : ℝ) - Real.pi * Real.exp (101 / 80 : ℝ)) ≤
      (2 / (483983823880189 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1011 / 3200 : ℝ) - Real.pi * Real.exp (101 / 80 : ℝ) =
      -(Real.pi * Real.exp (101 / 80 : ℝ) - (1011 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27792625841902649 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (27792625841902649 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1010_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (101 / 160 : ℝ) (1011 / 1600 : ℝ)) :
    (8688029 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (44296849 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1010_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1010_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1011_leftExp :
    (3538666637 / 1000000000 : ℝ) ≤ Real.exp (1011 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1011 / 800 : ℝ) (1040282371647 / 1000000000000 : ℝ)
    (3538666637 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1011_rightExp :
    Real.exp (253 / 200 : ℝ) ≤ (35430927363 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (253 / 200 : ℝ) (130040376059 / 125000000000 : ℝ)
    (35430927363 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1011_denomUpper :
    Real.exp (108150178387109259 / 10000000000000000 : ℝ) ≤ (497625433633371 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (108150178387109259 / 10000000000000000 : ℝ)
    (350524367203 / 250000000000 : ℝ) (497625433633371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1011_denomLower :
    (61324845438967 / 1250000000 : ℝ) ≤ Real.exp (1350099599683263 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1350099599683263 / 125000000000000 : ℝ) (1401474504561 /
    1000000000000 : ℝ) (61324845438967 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1011_product_lower :
    (1389630849683263 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1011 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1011_leftExp
    (by norm_num : (0 : ℝ) ≤ (3538666637 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1011_product_upper :
    Real.pi * Real.exp (253 / 200 : ℝ) ≤ (111309553387109259 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1011_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1011_endpointLower :
    (171877323 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1011 / 1600 : ℝ) (253 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1389630849683263 / 125000000000000 : ℝ) (Real.pi * Real.exp (1011 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1011_product_lower
  have hD : Real.exp (Real.pi * Real.exp (253 / 200 : ℝ) - (1011 / 3200 : ℝ)) ≤
      (497625433633371 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1011_denomUpper
    linarith [hpThetaJensenCell1011_product_upper]
  have hi : (1 / (497625433633371 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (253 / 200 : ℝ) - (1011 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (497625433633371 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (497625433633371 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1011 / 3200 : ℝ) - Real.pi * Real.exp (253 / 200 : ℝ)) := by
    rw [show (1011 / 3200 : ℝ) - Real.pi * Real.exp (253 / 200 : ℝ) =
      -(Real.pi * Real.exp (253 / 200 : ℝ) - (1011 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1011 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1011 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1011_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (497625433633371 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1011_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1011 / 1600 : ℝ) (253 / 400 : ℝ) ≤ (87634997 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (253 / 200 : ℝ)) (111309553387109259 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (253 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1011_product_upper
  have hD : (61324845438967 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1011 / 800 : ℝ) - (253 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1011_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1011_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1011 / 800 : ℝ) - (253 / 800 : ℝ)) ≤
      (1 / (61324845438967 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (61324845438967 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((253 / 800 : ℝ) - Real.pi * Real.exp (1011 / 800 : ℝ)) ≤
      (2 / (61324845438967 / 1250000000 : ℝ) : ℝ) := by
    rw [show (253 / 800 : ℝ) - Real.pi * Real.exp (1011 / 800 : ℝ) =
      -(Real.pi * Real.exp (1011 / 800 : ℝ) - (253 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (111309553387109259 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (111309553387109259 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1011_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1011 / 1600 : ℝ) (253 / 400 : ℝ)) :
    (171877323 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (87634997 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1011_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1011_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1012_leftExp :
    (35430927361 / 10000000000 : ℝ) ≤ Real.exp (253 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (253 / 200 : ℝ) (1040323008471 / 1000000000000 : ℝ)
    (35430927361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1012_rightExp :
    Real.exp (1013 / 800 : ℝ) ≤ (17737621857 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1013 / 800 : ℝ) (1040363646883 / 1000000000000 : ℝ)
    (17737621857 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1012_denomUpper :
    Real.exp (54143138662598201 / 5000000000000000 : ℝ) ≤ (100888872023653 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (54143138662598201 / 5000000000000000 : ℝ) (175336740071
    / 125000000000 : ℝ) (100888872023653 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1012_denomLower :
    (99462550513283 / 2000000000 : ℝ) ≤ Real.exp (13517986618737339 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13517986618737339 / 1250000000000000 : ℝ) (175258741137
    / 125000000000 : ℝ) (99462550513283 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1012_product_lower :
    (13913689743737339 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (253 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1012_leftExp
    (by norm_num : (0 : ℝ) ≤ (35430927361 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1012_product_upper :
    Real.pi * Real.exp (1013 / 800 : ℝ) ≤ (55724388662598201 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1012_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1012_endpointLower :
    (170011471 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (253 / 400 : ℝ) (1013 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13913689743737339 / 1250000000000000 : ℝ) (Real.pi * Real.exp (253 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1012_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1013 / 800 : ℝ) - (253 / 800 : ℝ)) ≤
      (100888872023653 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1012_denomUpper
    linarith [hpThetaJensenCell1012_product_upper]
  have hi : (1 / (100888872023653 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1013 / 800 : ℝ) - (253 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (100888872023653 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (100888872023653 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((253 / 800 : ℝ) - Real.pi * Real.exp (1013 / 800 : ℝ)) := by
    rw [show (253 / 800 : ℝ) - Real.pi * Real.exp (1013 / 800 : ℝ) =
      -(Real.pi * Real.exp (1013 / 800 : ℝ) - (253 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (253 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (253 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1012_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (100888872023653 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1012_endpointUpper :
    hpThetaJensenKernelEndpointUpper (253 / 400 : ℝ) (1013 / 1600 : ℝ) ≤ (4334257 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1013 / 800 : ℝ)) (55724388662598201 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1013 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1012_product_upper
  have hD : (99462550513283 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (253 / 200 : ℝ) - (1013 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1012_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1012_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (253 / 200 : ℝ) - (1013 / 3200 : ℝ)) ≤
      (1 / (99462550513283 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (99462550513283 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1013 / 3200 : ℝ) - Real.pi * Real.exp (253 / 200 : ℝ)) ≤
      (2 / (99462550513283 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1013 / 3200 : ℝ) - Real.pi * Real.exp (253 / 200 : ℝ) =
      -(Real.pi * Real.exp (253 / 200 : ℝ) - (1013 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55724388662598201 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (55724388662598201 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1012_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (253 / 400 : ℝ) (1013 / 1600 : ℝ)) :
    (170011471 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4334257 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1012_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1012_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1013_leftExp :
    (35475243711 / 10000000000 : ℝ) ≤ Real.exp (1013 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1013 / 800 : ℝ) (520181823441 / 500000000000 : ℝ)
    (35475243711 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1013_rightExp :
    Real.exp (507 / 400 : ℝ) ≤ (17759807747 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (507 / 400 : ℝ) (1040404286881 / 1000000000000 : ℝ)
    (17759807747 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1013_denomUpper :
    Real.exp (54211275199320971 / 5000000000000000 : ℝ) ≤ (511365630488307 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (54211275199320971 / 5000000000000000 : ℝ) (175411423711
    / 125000000000 : ℝ) (511365630488307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1013_denomLower :
    (100825478401051 / 2000000000 : ℝ) ≤ Real.exp (13534998980065989 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13534998980065989 / 1250000000000000 : ℝ) (43833324029 /
    31250000000 : ℝ) (100825478401051 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1013_product_lower :
    (13931092730065989 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1013 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1013_leftExp
    (by norm_num : (0 : ℝ) ≤ (35475243711 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1013_product_upper :
    Real.pi * Real.exp (507 / 400 : ℝ) ≤ (55794087699320971 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1013_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1013_endpointLower :
    (1681629 / 100000000 : ℝ) ≤ hpThetaTraceEndpointLower (1013 / 1600 : ℝ) (507 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13931092730065989 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1013 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1013_product_lower
  have hD : Real.exp (Real.pi * Real.exp (507 / 400 : ℝ) - (1013 / 3200 : ℝ)) ≤
      (511365630488307 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1013_denomUpper
    linarith [hpThetaJensenCell1013_product_upper]
  have hi : (1 / (511365630488307 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (507 / 400 : ℝ) - (1013 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (511365630488307 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (511365630488307 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1013 / 3200 : ℝ) - Real.pi * Real.exp (507 / 400 : ℝ)) := by
    rw [show (1013 / 3200 : ℝ) - Real.pi * Real.exp (507 / 400 : ℝ) =
      -(Real.pi * Real.exp (507 / 400 : ℝ) - (1013 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1013 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1013 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1013_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (511365630488307 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1013_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1013 / 1600 : ℝ) (507 / 800 : ℝ) ≤ (85744063 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (507 / 400 : ℝ)) (55794087699320971 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (507 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1013_product_upper
  have hD : (100825478401051 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1013 / 800 : ℝ) - (507 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1013_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1013_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1013 / 800 : ℝ) - (507 / 1600 : ℝ)) ≤
      (1 / (100825478401051 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (100825478401051 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((507 / 1600 : ℝ) - Real.pi * Real.exp (1013 / 800 : ℝ)) ≤
      (2 / (100825478401051 / 2000000000 : ℝ) : ℝ) := by
    rw [show (507 / 1600 : ℝ) - Real.pi * Real.exp (1013 / 800 : ℝ) =
      -(Real.pi * Real.exp (1013 / 800 : ℝ) - (507 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55794087699320971 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (55794087699320971 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1013_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1013 / 1600 : ℝ) (507 / 800 : ℝ)) :
    (1681629 / 100000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (85744063 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1013_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1013_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1014_leftExp :
    (8879903873 / 2500000000 : ℝ) ≤ Real.exp (507 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (507 / 400 : ℝ) (6502526793 / 6250000000 : ℝ) (8879903873
    / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1014_rightExp :
    Real.exp (203 / 160 : ℝ) ≤ (4445505347 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (203 / 160 : ℝ) (260111232117 / 250000000000 : ℝ)
    (4445505347 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1014_denomUpper :
    Real.exp (13569874729597771 / 1250000000000000 : ℝ) ≤ (259195451771537 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13569874729597771 / 1250000000000000 : ℝ) (1403889878261
    / 1000000000000 : ℝ) (259195451771537 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1014_denomLower :
    (127761077821047 / 2500000000 : ℝ) ≤ Real.exp (3388008277273227 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3388008277273227 / 312500000000000 : ℝ) (350815956533 /
    250000000000 : ℝ) (127761077821047 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1014_product_lower :
    (3487129371023227 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (507 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1014_leftExp
    (by norm_num : (0 : ℝ) ≤ (8879903873 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1014_product_upper :
    Real.pi * Real.exp (203 / 160 : ℝ) ≤ (13965968479597771 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1014_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1014_endpointLower :
    (166331481 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (507 / 800 : ℝ) (203 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3487129371023227 / 312500000000000 : ℝ) (Real.pi * Real.exp (507 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1014_product_lower
  have hD : Real.exp (Real.pi * Real.exp (203 / 160 : ℝ) - (507 / 1600 : ℝ)) ≤
      (259195451771537 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1014_denomUpper
    linarith [hpThetaJensenCell1014_product_upper]
  have hi : (1 / (259195451771537 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (203 / 160 : ℝ) - (507 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (259195451771537 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (259195451771537 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((507 / 1600 : ℝ) - Real.pi * Real.exp (203 / 160 : ℝ)) := by
    rw [show (507 / 1600 : ℝ) - Real.pi * Real.exp (203 / 160 : ℝ) =
      -(Real.pi * Real.exp (203 / 160 : ℝ) - (507 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (507 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (507 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1014_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (259195451771537 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1014_endpointUpper :
    hpThetaJensenKernelEndpointUpper (507 / 800 : ℝ) (203 / 320 : ℝ) ≤ (42405851 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (203 / 160 : ℝ)) (13965968479597771 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (203 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1014_product_upper
  have hD : (127761077821047 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (507 / 400 : ℝ) - (203 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1014_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1014_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (507 / 400 : ℝ) - (203 / 640 : ℝ)) ≤
      (1 / (127761077821047 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (127761077821047 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((203 / 640 : ℝ) - Real.pi * Real.exp (507 / 400 : ℝ)) ≤
      (2 / (127761077821047 / 2500000000 : ℝ) : ℝ) := by
    rw [show (203 / 640 : ℝ) - Real.pi * Real.exp (507 / 400 : ℝ) =
      -(Real.pi * Real.exp (507 / 400 : ℝ) - (203 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13965968479597771 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13965968479597771 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1014_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (507 / 800 : ℝ) (203 / 320 : ℝ)) :
    (166331481 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (42405851 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1014_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1014_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1015_leftExp :
    (35564042773 / 10000000000 : ℝ) ≤ Real.exp (203 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (203 / 160 : ℝ) (1040444928467 / 1000000000000 : ℝ)
    (35564042773 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1015_rightExp :
    Real.exp (127 / 100 : ℝ) ≤ (4451065703 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (127 / 100 : ℝ) (1040485571641 / 1000000000000 : ℝ)
    (4451065703 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1015_denomUpper :
    Real.exp (13586952480084879 / 1250000000000000 : ℝ) ≤ (262760932673023 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13586952480084879 / 1250000000000000 : ℝ) (1404489388257
    / 1000000000000 : ℝ) (262760932673023 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1015_denomLower :
    (51806516749949 / 1000000000 : ℝ) ≤ Real.exp (13569089032914327 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13569089032914327 / 1250000000000000 : ℝ) (70193115137 /
    50000000000 : ℝ) (51806516749949 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1015_product_lower :
    (13965964032914327 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (203 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1015_leftExp
    (by norm_num : (0 : ℝ) ≤ (35564042773 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1015_product_upper :
    Real.pi * Real.exp (127 / 100 : ℝ) ≤ (13983436855084879 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1015_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1015_endpointLower :
    (16451709 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (203 / 320 : ℝ) (127 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13965964032914327 / 1250000000000000 : ℝ) (Real.pi * Real.exp (203 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1015_product_lower
  have hD : Real.exp (Real.pi * Real.exp (127 / 100 : ℝ) - (203 / 640 : ℝ)) ≤
      (262760932673023 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1015_denomUpper
    linarith [hpThetaJensenCell1015_product_upper]
  have hi : (1 / (262760932673023 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (127 / 100 : ℝ) - (203 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (262760932673023 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (262760932673023 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((203 / 640 : ℝ) - Real.pi * Real.exp (127 / 100 : ℝ)) := by
    rw [show (203 / 640 : ℝ) - Real.pi * Real.exp (127 / 100 : ℝ) =
      -(Real.pi * Real.exp (127 / 100 : ℝ) - (203 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (203 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (203 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1015_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (262760932673023 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1015_endpointUpper :
    hpThetaJensenKernelEndpointUpper (203 / 320 : ℝ) (127 / 200 : ℝ) ≤ (83887993 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (127 / 100 : ℝ)) (13983436855084879 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (127 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1015_product_upper
  have hD : (51806516749949 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (203 / 160 : ℝ) - (127 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1015_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1015_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (203 / 160 : ℝ) - (127 / 400 : ℝ)) ≤
      (1 / (51806516749949 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (51806516749949 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((127 / 400 : ℝ) - Real.pi * Real.exp (203 / 160 : ℝ)) ≤
      (2 / (51806516749949 / 1000000000 : ℝ) : ℝ) := by
    rw [show (127 / 400 : ℝ) - Real.pi * Real.exp (203 / 160 : ℝ) =
      -(Real.pi * Real.exp (203 / 160 : ℝ) - (127 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13983436855084879 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13983436855084879 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1015_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (203 / 320 : ℝ) (127 / 200 : ℝ)) :
    (16451709 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (83887993 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1015_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1015_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1016_leftExp :
    (17804262811 / 5000000000 : ℝ) ≤ Real.exp (127 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (127 / 100 : ℝ) (26012139291 / 25000000000 : ℝ)
    (17804262811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1016_rightExp :
    Real.exp (1017 / 800 : ℝ) ≤ (2228316507 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1017 / 800 : ℝ) (1040526216403 / 1000000000000 : ℝ)
    (2228316507 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1016_denomUpper :
    Real.exp (6802026040175651 / 625000000000000 : ℝ) ≤ (133190058199187 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6802026040175651 / 625000000000000 : ℝ) (702544960893 /
    500000000000 : ℝ) (133190058199187 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1016_denomLower :
    (262595823161417 / 5000000000 : ℝ) ≤ Real.exp (6793083389116889 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6793083389116889 / 625000000000000 : ℝ) (1404461800779 /
    1000000000000 : ℝ) (262595823161417 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1016_product_lower :
    (6991716201616889 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (127 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1016_leftExp
    (by norm_num : (0 : ℝ) ≤ (17804262811 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1016_product_upper :
    Real.pi * Real.exp (1017 / 800 : ℝ) ≤ (7000463540175651 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1016_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1016_endpointLower :
    (406799 / 25000000 : ℝ) ≤ hpThetaTraceEndpointLower (127 / 200 : ℝ) (1017 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6991716201616889 / 625000000000000 : ℝ) (Real.pi * Real.exp (127 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1016_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1017 / 800 : ℝ) - (127 / 400 : ℝ)) ≤
      (133190058199187 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1016_denomUpper
    linarith [hpThetaJensenCell1016_product_upper]
  have hi : (1 / (133190058199187 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1017 / 800 : ℝ) - (127 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (133190058199187 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (133190058199187 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((127 / 400 : ℝ) - Real.pi * Real.exp (1017 / 800 : ℝ)) := by
    rw [show (127 / 400 : ℝ) - Real.pi * Real.exp (1017 / 800 : ℝ) =
      -(Real.pi * Real.exp (1017 / 800 : ℝ) - (127 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (127 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (127 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1016_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (133190058199187 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1016_endpointUpper :
    hpThetaJensenKernelEndpointUpper (127 / 200 : ℝ) (1017 / 1600 : ℝ) ≤ (33189149 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1017 / 800 : ℝ)) (7000463540175651 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1017 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1016_product_upper
  have hD : (262595823161417 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (127 / 100 : ℝ) - (1017 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1016_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1016_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (127 / 100 : ℝ) - (1017 / 3200 : ℝ)) ≤
      (1 / (262595823161417 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (262595823161417 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1017 / 3200 : ℝ) - Real.pi * Real.exp (127 / 100 : ℝ)) ≤
      (2 / (262595823161417 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1017 / 3200 : ℝ) - Real.pi * Real.exp (127 / 100 : ℝ) =
      -(Real.pi * Real.exp (127 / 100 : ℝ) - (1017 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7000463540175651 / 625000000000000 : ℝ) ^ 2 - 6 *
      (7000463540175651 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1016_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (127 / 200 : ℝ) (1017 / 1600 : ℝ)) :
    (406799 / 25000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (33189149 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1016_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1016_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1017_leftExp :
    (3565306411 / 1000000000 : ℝ) ≤ Real.exp (1017 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1017 / 800 : ℝ) (520263108201 / 500000000000 : ℝ)
    (3565306411 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1017_rightExp :
    Real.exp (509 / 400 : ℝ) ≤ (8924414577 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (509 / 400 : ℝ) (32517714461 / 31250000000 : ℝ)
    (8924414577 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1017_denomUpper :
    Real.exp (27242347114201161 / 2500000000000000 : ℝ) ≤ (135026937908167 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27242347114201161 / 2500000000000000 : ℝ) (1405691480883
    / 1000000000000 : ℝ) (135026937908167 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1017_denomLower :
    (266212731539067 / 5000000000 : ℝ) ≤ Real.exp (1360326637293289 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1360326637293289 / 125000000000000 : ℝ) (1405062322317 /
    1000000000000 : ℝ) (266212731539067 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1017_product_lower :
    (1400092262293289 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1017 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1017_leftExp
    (by norm_num : (0 : ℝ) ≤ (3565306411 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1017_product_upper :
    Real.pi * Real.exp (509 / 400 : ℝ) ≤ (28036878364201161 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1017_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1017_endpointLower :
    (20117361 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1017 / 1600 : ℝ) (509 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1400092262293289 / 125000000000000 : ℝ) (Real.pi * Real.exp (1017 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1017_product_lower
  have hD : Real.exp (Real.pi * Real.exp (509 / 400 : ℝ) - (1017 / 3200 : ℝ)) ≤
      (135026937908167 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1017_denomUpper
    linarith [hpThetaJensenCell1017_product_upper]
  have hi : (1 / (135026937908167 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (509 / 400 : ℝ) - (1017 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (135026937908167 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (135026937908167 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1017 / 3200 : ℝ) - Real.pi * Real.exp (509 / 400 : ℝ)) := by
    rw [show (1017 / 3200 : ℝ) - Real.pi * Real.exp (509 / 400 : ℝ) =
      -(Real.pi * Real.exp (509 / 400 : ℝ) - (1017 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1017 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1017 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1017_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (135026937908167 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1017_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1017 / 1600 : ℝ) (509 / 800 : ℝ) ≤ (41033139 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (509 / 400 : ℝ)) (28036878364201161 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (509 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1017_product_upper
  have hD : (266212731539067 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1017 / 800 : ℝ) - (509 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1017_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1017_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1017 / 800 : ℝ) - (509 / 1600 : ℝ)) ≤
      (1 / (266212731539067 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (266212731539067 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((509 / 1600 : ℝ) - Real.pi * Real.exp (1017 / 800 : ℝ)) ≤
      (2 / (266212731539067 / 5000000000 : ℝ) : ℝ) := by
    rw [show (509 / 1600 : ℝ) - Real.pi * Real.exp (1017 / 800 : ℝ) =
      -(Real.pi * Real.exp (1017 / 800 : ℝ) - (509 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28036878364201161 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (28036878364201161 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1017_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1017 / 1600 : ℝ) (509 / 800 : ℝ)) :
    (20117361 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (41033139 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1017_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1017_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1018_leftExp :
    (17848829153 / 5000000000 : ℝ) ≤ Real.exp (509 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (509 / 400 : ℝ) (1040566862751 / 1000000000000 : ℝ)
    (17848829153 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1018_rightExp :
    Real.exp (1019 / 800 : ℝ) ≤ (35742308281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1019 / 800 : ℝ) (1040607510689 / 1000000000000 : ℝ)
    (35742308281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1018_denomUpper :
    Real.exp (109106535499431633 / 10000000000000000 : ℝ) ≤ (547566197997067 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (109106535499431633 / 10000000000000000 : ℝ)
    (281258813519 / 200000000000 : ℝ) (547566197997067 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1018_denomLower :
    (539768362545847 / 10000000000 : ℝ) ≤ Real.exp (6810193922053947 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6810193922053947 / 625000000000000 : ℝ) (1405663869401 /
    1000000000000 : ℝ) (539768362545847 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1018_product_lower :
    (7009217359553947 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (509 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1018_leftExp
    (by norm_num : (0 : ℝ) ≤ (17848829153 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1018_product_upper :
    Real.pi * Real.exp (1019 / 800 : ℝ) ≤ (112287785499431633 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1018_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1018_endpointLower :
    (15917483 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (509 / 800 : ℝ) (1019 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7009217359553947 / 625000000000000 : ℝ) (Real.pi * Real.exp (509 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1018_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1019 / 800 : ℝ) - (509 / 1600 : ℝ)) ≤
      (547566197997067 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1018_denomUpper
    linarith [hpThetaJensenCell1018_product_upper]
  have hi : (1 / (547566197997067 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1019 / 800 : ℝ) - (509 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (547566197997067 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (547566197997067 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((509 / 1600 : ℝ) - Real.pi * Real.exp (1019 / 800 : ℝ)) := by
    rw [show (509 / 1600 : ℝ) - Real.pi * Real.exp (1019 / 800 : ℝ) =
      -(Real.pi * Real.exp (1019 / 800 : ℝ) - (509 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (509 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (509 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1018_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (547566197997067 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1018_endpointUpper :
    hpThetaJensenKernelEndpointUpper (509 / 800 : ℝ) (1019 / 1600 : ℝ) ≤ (40584073 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1019 / 800 : ℝ)) (112287785499431633 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1019 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1018_product_upper
  have hD : (539768362545847 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (509 / 400 : ℝ) - (1019 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1018_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1018_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (509 / 400 : ℝ) - (1019 / 3200 : ℝ)) ≤
      (1 / (539768362545847 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (539768362545847 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1019 / 3200 : ℝ) - Real.pi * Real.exp (509 / 400 : ℝ)) ≤
      (2 / (539768362545847 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1019 / 3200 : ℝ) - Real.pi * Real.exp (509 / 400 : ℝ) =
      -(Real.pi * Real.exp (509 / 400 : ℝ) - (1019 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (112287785499431633 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (112287785499431633 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1018_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (509 / 800 : ℝ) (1019 / 1600 : ℝ)) :
    (15917483 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40584073 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1018_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1018_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1019_leftExp :
    (35742308279 / 10000000000 : ℝ) ≤ Real.exp (1019 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1019 / 800 : ℝ) (32518984709 / 31250000000 : ℝ)
    (35742308279 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1019_rightExp :
    Real.exp (51 / 40 : ℝ) ≤ (17893507051 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 40 : ℝ) (520324080107 / 500000000000 : ℝ)
    (17893507051 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1019_denomUpper :
    Real.exp (54621928996872243 / 5000000000000000 : ℝ) ≤ (555137379306197 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (54621928996872243 / 5000000000000000 : ℝ) (281379536801
    / 200000000000 : ℝ) (555137379306197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1019_denomLower :
    (273611059894361 / 5000000000 : ℝ) ≤ Real.exp (13637531218855021 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13637531218855021 / 1250000000000000 : ℝ) (1406266444081
    / 1000000000000 : ℝ) (273611059894361 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1019_product_lower :
    (14035968718855021 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1019 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1019_leftExp
    (by norm_num : (0 : ℝ) ≤ (35742308279 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1019_product_upper :
    Real.pi * Real.exp (51 / 40 : ℝ) ≤ (56214116496872243 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1019_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1019_endpointLower :
    (78713651 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1019 / 1600 : ℝ) (51 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14035968718855021 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1019 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1019_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 40 : ℝ) - (1019 / 3200 : ℝ)) ≤
      (555137379306197 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1019_denomUpper
    linarith [hpThetaJensenCell1019_product_upper]
  have hi : (1 / (555137379306197 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 40 : ℝ) - (1019 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (555137379306197 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (555137379306197 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1019 / 3200 : ℝ) - Real.pi * Real.exp (51 / 40 : ℝ)) := by
    rw [show (1019 / 3200 : ℝ) - Real.pi * Real.exp (51 / 40 : ℝ) =
      -(Real.pi * Real.exp (51 / 40 : ℝ) - (1019 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1019 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1019 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1019_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (555137379306197 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1019_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1019 / 1600 : ℝ) (51 / 80 : ℝ) ≤ (40139207 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 40 : ℝ)) (56214116496872243 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1019_product_upper
  have hD : (273611059894361 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1019 / 800 : ℝ) - (51 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1019_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1019_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1019 / 800 : ℝ) - (51 / 160 : ℝ)) ≤
      (1 / (273611059894361 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (273611059894361 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 160 : ℝ) - Real.pi * Real.exp (1019 / 800 : ℝ)) ≤
      (2 / (273611059894361 / 5000000000 : ℝ) : ℝ) := by
    rw [show (51 / 160 : ℝ) - Real.pi * Real.exp (1019 / 800 : ℝ) =
      -(Real.pi * Real.exp (1019 / 800 : ℝ) - (51 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56214116496872243 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (56214116496872243 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1019_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1019 / 1600 : ℝ) (51 / 80 : ℝ)) :
    (78713651 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40139207 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1019_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1019_endpointUpper

def hpThetaJensenCellsBatch050Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3871577 / 200000000 : ℝ)
  | 1 => (9575721 / 500000000 : ℝ)
  | 2 => (23683587 / 1250000000 : ℝ)
  | 3 => (46860387 / 2500000000 : ℝ)
  | 4 => (185432843 / 10000000000 : ℝ)
  | 5 => (11465153 / 625000000 : ℝ)
  | 6 => (90735117 / 5000000000 : ℝ)
  | 7 => (17951607 / 1000000000 : ℝ)
  | 8 => (88789913 / 5000000000 : ℝ)
  | 9 => (43915343 / 2500000000 : ℝ)
  | 10 => (8688029 / 500000000 : ℝ)
  | 11 => (171877323 / 10000000000 : ℝ)
  | 12 => (170011471 / 10000000000 : ℝ)
  | 13 => (1681629 / 100000000 : ℝ)
  | 14 => (166331481 / 10000000000 : ℝ)
  | 15 => (16451709 / 1000000000 : ℝ)
  | 16 => (406799 / 25000000 : ℝ)
  | 17 => (20117361 / 1250000000 : ℝ)
  | 18 => (15917483 / 1000000000 : ℝ)
  | 19 => (78713651 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch050Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (197363013 / 10000000000 : ℝ)
  | 1 => (195261521 / 10000000000 : ℝ)
  | 2 => (38635807 / 2000000000 : ℝ)
  | 3 => (191115423 / 10000000000 : ℝ)
  | 4 => (189070549 / 10000000000 : ℝ)
  | 5 => (187044281 / 10000000000 : ℝ)
  | 6 => (37007297 / 2000000000 : ℝ)
  | 7 => (18304703 / 1000000000 : ℝ)
  | 8 => (22634473 / 1250000000 : ℝ)
  | 9 => (22390327 / 1250000000 : ℝ)
  | 10 => (44296849 / 2500000000 : ℝ)
  | 11 => (87634997 / 5000000000 : ℝ)
  | 12 => (4334257 / 250000000 : ℝ)
  | 13 => (85744063 / 5000000000 : ℝ)
  | 14 => (42405851 / 2500000000 : ℝ)
  | 15 => (83887993 / 5000000000 : ℝ)
  | 16 => (33189149 / 2000000000 : ℝ)
  | 17 => (41033139 / 2500000000 : ℝ)
  | 18 => (40584073 / 2500000000 : ℝ)
  | 19 => (40139207 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch050_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch050Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch050Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1000_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1001_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1002_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1003_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1004_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1005_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1006_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1007_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1008_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1009_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1010_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1011_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1012_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1013_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1014_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1015_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1016_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1017_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1018_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1019_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper] at h ⊢
    exact h

end HodgeProofHP
