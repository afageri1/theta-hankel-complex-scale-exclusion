import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell0_leftExp :
    (1 / 1 : ℝ) ≤ Real.exp (0 / 1 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (0 / 1 : ℝ) (1 / 1 : ℝ) (1 / 1 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell0_rightExp :
    Real.exp (1 / 800 : ℝ) ≤ (1251563477 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 800 : ℝ) (1000039063263 / 1000000000000 : ℝ)
    (1251563477 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell0_denomUpper :
    Real.exp (3931903058398861 / 1250000000000000 : ℝ) ≤ (232318096867 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3931903058398861 / 1250000000000000 : ℝ) (110329104971 /
    100000000000 : ℝ) (232318096867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell0_denomLower :
    (231334471761 / 10000000000 : ℝ) ≤ Real.exp (6282559 / 2000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6282559 / 2000000 : ℝ) (551572385873 / 500000000000 : ℝ)
    (231334471761 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell0_product_lower :
    (392699 / 125000 : ℝ) ≤ Real.pi * Real.exp (0 / 1 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell0_leftExp
    (by norm_num : (0 : ℝ) ≤ (1 / 1 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell0_product_upper :
    Real.pi * Real.exp (1 / 800 : ℝ) ≤ (3931903058398861 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell0_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell0_endpointLower :
    (2219892623 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (0 / 1 : ℝ) (1 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (392699 / 125000 : ℝ) (Real.pi * Real.exp (0 / 1 : ℝ))
    (by norm_num) hpThetaJensenCell0_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 800 : ℝ) - (0 / 1 : ℝ)) ≤
      (232318096867 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell0_denomUpper
    linarith [hpThetaJensenCell0_product_upper]
  have hi : (1 / (232318096867 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 800 : ℝ) - (0 / 1 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (232318096867 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (232318096867 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((0 / 1 : ℝ) - Real.pi * Real.exp (1 / 800 : ℝ)) := by
    rw [show (0 / 1 : ℝ) - Real.pi * Real.exp (1 / 800 : ℝ) =
      -(Real.pi * Real.exp (1 / 800 : ℝ) - (0 / 1 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (0 / 1 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (0 / 1 : ℝ)) := by
    have h := hpThetaJensenCell0_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (232318096867 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell0_endpointUpper :
    hpThetaJensenKernelEndpointUpper (0 / 1 : ℝ) (1 / 1600 : ℝ) ≤ (17946859257 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 800 : ℝ)) (3931903058398861 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell0_product_upper
  have hD : (231334471761 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (0 / 1 : ℝ) - (1 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell0_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell0_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (0 / 1 : ℝ) - (1 / 3200 : ℝ)) ≤
      (1 / (231334471761 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (231334471761 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 3200 : ℝ) - Real.pi * Real.exp (0 / 1 : ℝ)) ≤
      (2 / (231334471761 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 3200 : ℝ) - Real.pi * Real.exp (0 / 1 : ℝ) =
      -(Real.pi * Real.exp (0 / 1 : ℝ) - (1 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3931903058398861 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (3931903058398861 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell0_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (0 / 1 : ℝ) (1 / 1600 : ℝ)) :
    (2219892623 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17946859257 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell0_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell0_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1_leftExp :
    (2002501563 / 2000000000 : ℝ) ≤ Real.exp (1 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 800 : ℝ) (500019531631 / 500000000000 : ℝ)
    (2002501563 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1_rightExp :
    Real.exp (1 / 400 : ℝ) ≤ (10025031277 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 400 : ℝ) (250019532013 / 250000000000 : ℝ)
    (10025031277 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1_denomUpper :
    Real.exp (31491443084604261 / 10000000000000000 : ℝ) ≤ (23316104649 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31491443084604261 / 10000000000000000 : ℝ) (220683186153
    / 200000000000 : ℝ) (23316104649 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1_denomLower :
    (116086355439 / 5000000000 : ℝ) ≤ Real.exp (786224111288537 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (786224111288537 / 250000000000000 : ℝ) (220653893347 /
    200000000000 : ℝ) (116086355439 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1_product_lower :
    (786380361288537 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1_leftExp
    (by norm_num : (0 : ℝ) ≤ (2002501563 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1_product_upper :
    Real.pi * Real.exp (1 / 400 : ℝ) ≤ (31494568084604261 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1_endpointLower :
    (3551895531 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 1600 : ℝ) (1 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (786380361288537 / 250000000000000 : ℝ) (Real.pi * Real.exp (1 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 400 : ℝ) - (1 / 3200 : ℝ)) ≤
      (23316104649 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1_denomUpper
    linarith [hpThetaJensenCell1_product_upper]
  have hi : (1 / (23316104649 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 400 : ℝ) - (1 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23316104649 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23316104649 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 3200 : ℝ) - Real.pi * Real.exp (1 / 400 : ℝ)) := by
    rw [show (1 / 3200 : ℝ) - Real.pi * Real.exp (1 / 400 : ℝ) =
      -(Real.pi * Real.exp (1 / 400 : ℝ) - (1 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23316104649 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 1600 : ℝ) (1 / 800 : ℝ) ≤ (2243404857 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 400 : ℝ)) (31494568084604261 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell1_product_upper
  have hD : (116086355439 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 800 : ℝ) - (1 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 800 : ℝ) - (1 / 1600 : ℝ)) ≤
      (1 / (116086355439 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (116086355439 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 1600 : ℝ) - Real.pi * Real.exp (1 / 800 : ℝ)) ≤
      (2 / (116086355439 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 1600 : ℝ) - Real.pi * Real.exp (1 / 800 : ℝ) =
      -(Real.pi * Real.exp (1 / 800 : ℝ) - (1 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31494568084604261 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (31494568084604261 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 1600 : ℝ) (1 / 800 : ℝ)) :
    (3551895531 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2243404857 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell2_leftExp :
    (401001251 / 400000000 : ℝ) ≤ Real.exp (1 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 400 : ℝ) (1000078128051 / 1000000000000 : ℝ)
    (401001251 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell2_rightExp :
    Real.exp (3 / 800 : ℝ) ≤ (10037570401 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 800 : ℝ) (1000117194367 / 1000000000000 : ℝ)
    (10037570401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell2_denomUpper :
    Real.exp (31527710908788793 / 10000000000000000 : ℝ) ≤ (117004103089 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31527710908788793 / 10000000000000000 : ℝ)
    (1103540995649 / 1000000000000 : ℝ) (117004103089 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell2_denomLower :
    (233015132613 / 10000000000 : ℝ) ≤ Real.exp (157425915266449 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157425915266449 / 50000000000000 : ℝ) (1103394345293 /
    1000000000000 : ℝ) (233015132613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell2_product_lower :
    (157472790266449 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell2_leftExp
    (by norm_num : (0 : ℝ) ≤ (401001251 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell2_product_upper :
    Real.pi * Real.exp (3 / 800 : ℝ) ≤ (31533960908788793 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell2_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell2_endpointLower :
    (17759678591 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 800 : ℝ) (3 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (157472790266449 / 50000000000000 : ℝ) (Real.pi * Real.exp (1 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell2_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 800 : ℝ) - (1 / 1600 : ℝ)) ≤
      (117004103089 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell2_denomUpper
    linarith [hpThetaJensenCell2_product_upper]
  have hi : (1 / (117004103089 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 800 : ℝ) - (1 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (117004103089 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (117004103089 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 1600 : ℝ) - Real.pi * Real.exp (3 / 800 : ℝ)) := by
    rw [show (1 / 1600 : ℝ) - Real.pi * Real.exp (3 / 800 : ℝ) =
      -(Real.pi * Real.exp (3 / 800 : ℝ) - (1 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 400 : ℝ)) := by
    have h := hpThetaJensenCell2_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (117004103089 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell2_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 800 : ℝ) (3 / 1600 : ℝ) ≤ (1121717597 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 800 : ℝ)) (31533960908788793 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell2_product_upper
  have hD : (233015132613 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 400 : ℝ) - (3 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell2_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell2_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 400 : ℝ) - (3 / 3200 : ℝ)) ≤
      (1 / (233015132613 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (233015132613 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 3200 : ℝ) - Real.pi * Real.exp (1 / 400 : ℝ)) ≤
      (2 / (233015132613 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 3200 : ℝ) - Real.pi * Real.exp (1 / 400 : ℝ) =
      -(Real.pi * Real.exp (1 / 400 : ℝ) - (3 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31533960908788793 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (31533960908788793 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell2_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 800 : ℝ) (3 / 1600 : ℝ)) :
    (17759678591 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1121717597 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell2_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell2_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell3_leftExp :
    (12546963 / 12500000 : ℝ) ≤ Real.exp (3 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 800 : ℝ) (500058597183 / 500000000000 : ℝ) (12546963
    / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell3_rightExp :
    Real.exp (1 / 200 : ℝ) ≤ (10050125209 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 200 : ℝ) (15627441597 / 15625000000 : ℝ)
    (10050125209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell3_denomUpper :
    Real.exp (31564028005717937 / 10000000000000000 : ℝ) ≤ (58714900281 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31564028005717937 / 10000000000000000 : ℝ) (137958280581
    / 125000000000 : ℝ) (58714900281 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell3_denomLower :
    (116930880961 / 5000000000 : ℝ) ≤ Real.exp (4925226698137 / 1562500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4925226698137 / 1562500000000 : ℝ) (551759703849 /
    500000000000 : ℝ) (116930880961 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell3_product_lower :
    (4927179823137 / 1562500000000 : ℝ) ≤ Real.pi * Real.exp (3 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell3_leftExp
    (by norm_num : (0 : ℝ) ≤ (12546963 / 12500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell3_product_upper :
    Real.pi * Real.exp (1 / 200 : ℝ) ≤ (31573403005717937 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell3_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell3_endpointLower :
    (17759743841 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 1600 : ℝ) (1 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4927179823137 / 1562500000000 : ℝ) (Real.pi * Real.exp (3 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell3_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 200 : ℝ) - (3 / 3200 : ℝ)) ≤
      (58714900281 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell3_denomUpper
    linarith [hpThetaJensenCell3_product_upper]
  have hi : (1 / (58714900281 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 200 : ℝ) - (3 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (58714900281 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (58714900281 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 3200 : ℝ) - Real.pi * Real.exp (1 / 200 : ℝ)) := by
    rw [show (3 / 3200 : ℝ) - Real.pi * Real.exp (1 / 200 : ℝ) =
      -(Real.pi * Real.exp (1 / 200 : ℝ) - (3 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 800 : ℝ)) := by
    have h := hpThetaJensenCell3_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (58714900281 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell3_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 1600 : ℝ) (1 / 400 : ℝ) ≤ (17947587403 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 200 : ℝ)) (31573403005717937 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell3_product_upper
  have hD : (116930880961 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 800 : ℝ) - (1 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell3_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell3_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 800 : ℝ) - (1 / 800 : ℝ)) ≤
      (1 / (116930880961 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (116930880961 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 800 : ℝ) - Real.pi * Real.exp (3 / 800 : ℝ)) ≤
      (2 / (116930880961 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 800 : ℝ) - Real.pi * Real.exp (3 / 800 : ℝ) =
      -(Real.pi * Real.exp (3 / 800 : ℝ) - (1 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31573403005717937 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (31573403005717937 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell3_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 1600 : ℝ) (1 / 400 : ℝ)) :
    (17759743841 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17947587403 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell3_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell3_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell4_leftExp :
    (1256265651 / 1250000000 : ℝ) ≤ Real.exp (1 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 200 : ℝ) (1000156262207 / 1000000000000 : ℝ)
    (1256265651 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell4_rightExp :
    Real.exp (1 / 160 : ℝ) ≤ (10062695721 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 160 : ℝ) (40007813263 / 40000000000 : ℝ)
    (10062695721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell4_denomUpper :
    Real.exp (31600394438223553 / 10000000000000000 : ℝ) ≤ (117857628311 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31600394438223553 / 10000000000000000 : ℝ) (551895839019
    / 500000000000 : ℝ) (117857628311 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell4_denomLower :
    (234712623767 / 10000000000 : ℝ) ≤ Real.exp (493090124257049 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (493090124257049 / 156250000000000 : ℝ) (275911163551 /
    250000000000 : ℝ) (234712623767 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell4_product_lower :
    (493334264882049 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell4_leftExp
    (by norm_num : (0 : ℝ) ≤ (1256265651 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell4_product_upper :
    Real.pi * Real.exp (1 / 160 : ℝ) ≤ (31612894438223553 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell4_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell4_endpointLower :
    (8879836727 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 400 : ℝ) (1 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (493334264882049 / 156250000000000 : ℝ) (Real.pi * Real.exp (1 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell4_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 160 : ℝ) - (1 / 800 : ℝ)) ≤
      (117857628311 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell4_denomUpper
    linarith [hpThetaJensenCell4_product_upper]
  have hi : (1 / (117857628311 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 160 : ℝ) - (1 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (117857628311 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (117857628311 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 800 : ℝ) - Real.pi * Real.exp (1 / 160 : ℝ)) := by
    rw [show (1 / 800 : ℝ) - Real.pi * Real.exp (1 / 160 : ℝ) =
      -(Real.pi * Real.exp (1 / 160 : ℝ) - (1 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 200 : ℝ)) := by
    have h := hpThetaJensenCell4_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (117857628311 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell4_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 400 : ℝ) (1 / 320 : ℝ) ≤ (17947556479 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 160 : ℝ)) (31612894438223553 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell4_product_upper
  have hD : (234712623767 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 200 : ℝ) - (1 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell4_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell4_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 200 : ℝ) - (1 / 640 : ℝ)) ≤
      (1 / (234712623767 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (234712623767 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 640 : ℝ) - Real.pi * Real.exp (1 / 200 : ℝ)) ≤
      (2 / (234712623767 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 640 : ℝ) - Real.pi * Real.exp (1 / 200 : ℝ) =
      -(Real.pi * Real.exp (1 / 200 : ℝ) - (1 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31612894438223553 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (31612894438223553 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell4_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 400 : ℝ) (1 / 320 : ℝ)) :
    (8879836727 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17947556479 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell4_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell4_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell5_leftExp :
    (10062695719 / 10000000000 : ℝ) ≤ Real.exp (1 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 160 : ℝ) (500097665787 / 500000000000 : ℝ)
    (10062695719 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell5_rightExp :
    Real.exp (3 / 400 : ℝ) ≤ (2015056391 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 400 : ℝ) (250058600617 / 250000000000 : ℝ)
    (2015056391 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell5_denomUpper :
    Real.exp (6327362052570863 / 2000000000000000 : ℝ) ≤ (236575197987 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6327362052570863 / 2000000000000000 : ℝ) (1103917296073
    / 1000000000000 : ℝ) (236575197987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell5_denomLower :
    (117783871709 / 5000000000 : ℝ) ≤ Real.exp (3949266796155581 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3949266796155581 / 1250000000000000 : ℝ) (551885042543 /
    500000000000 : ℝ) (117783871709 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell5_product_lower :
    (3951610546155581 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell5_leftExp
    (by norm_num : (0 : ℝ) ≤ (10062695719 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell5_product_upper :
    Real.pi * Real.exp (3 / 400 : ℝ) ≤ (6330487052570863 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell5_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell5_endpointLower :
    (17759467503 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 320 : ℝ) (3 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3951610546155581 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell5_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 400 : ℝ) - (1 / 640 : ℝ)) ≤
      (236575197987 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell5_denomUpper
    linarith [hpThetaJensenCell5_product_upper]
  have hi : (1 / (236575197987 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 400 : ℝ) - (1 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (236575197987 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (236575197987 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 640 : ℝ) - Real.pi * Real.exp (3 / 400 : ℝ)) := by
    rw [show (1 / 640 : ℝ) - Real.pi * Real.exp (3 / 400 : ℝ) =
      -(Real.pi * Real.exp (3 / 400 : ℝ) - (1 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 160 : ℝ)) := by
    have h := hpThetaJensenCell5_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (236575197987 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell5_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 320 : ℝ) (3 / 800 : ℝ) ≤ (4486847207 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 400 : ℝ)) (6330487052570863 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell5_product_upper
  have hD : (117783871709 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 160 : ℝ) - (3 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell5_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell5_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 160 : ℝ) - (3 / 1600 : ℝ)) ≤
      (1 / (117783871709 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (117783871709 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 1600 : ℝ) - Real.pi * Real.exp (1 / 160 : ℝ)) ≤
      (2 / (117783871709 / 5000000000 : ℝ) : ℝ) := by
    rw [show (3 / 1600 : ℝ) - Real.pi * Real.exp (1 / 160 : ℝ) =
      -(Real.pi * Real.exp (1 / 160 : ℝ) - (3 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6330487052570863 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (6330487052570863 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell5_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 320 : ℝ) (3 / 800 : ℝ)) :
    (17759467503 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4486847207 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell5_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell5_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell6_leftExp :
    (5037640977 / 5000000000 : ℝ) ≤ Real.exp (3 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 400 : ℝ) (1000234402467 / 1000000000000 : ℝ)
    (5037640977 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell6_rightExp :
    Real.exp (7 / 800 : ℝ) ≤ (2521970983 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 800 : ℝ) (125034184361 / 125000000000 : ℝ)
    (2521970983 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell6_denomUpper :
    Real.exp (7918318886395919 / 2500000000000000 : ℝ) ≤ (237439450941 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7918318886395919 / 2500000000000000 : ℝ) (552021549521 /
    500000000000 : ℝ) (237439450941 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell6_denomLower :
    (118213573199 / 5000000000 : ℝ) ≤ Real.exp (1976909386526923 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1976909386526923 / 625000000000000 : ℝ) (1103895700631 /
    1000000000000 : ℝ) (118213573199 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell6_product_lower :
    (1978276574026923 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell6_leftExp
    (by norm_num : (0 : ℝ) ≤ (5037640977 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell6_product_upper :
    Real.pi * Real.exp (7 / 800 : ℝ) ≤ (7923006386395919 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell6_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell6_endpointLower :
    (17759126049 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 800 : ℝ) (7 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1978276574026923 / 625000000000000 : ℝ) (Real.pi * Real.exp (3 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell6_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 800 : ℝ) - (3 / 1600 : ℝ)) ≤
      (237439450941 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell6_denomUpper
    linarith [hpThetaJensenCell6_product_upper]
  have hi : (1 / (237439450941 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 800 : ℝ) - (3 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (237439450941 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (237439450941 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 1600 : ℝ) - Real.pi * Real.exp (7 / 800 : ℝ)) := by
    rw [show (3 / 1600 : ℝ) - Real.pi * Real.exp (7 / 800 : ℝ) =
      -(Real.pi * Real.exp (7 / 800 : ℝ) - (3 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 400 : ℝ)) := by
    have h := hpThetaJensenCell6_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (237439450941 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell6_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 800 : ℝ) (7 / 1600 : ℝ) ≤ (560846391 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 800 : ℝ)) (7923006386395919 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell6_product_upper
  have hD : (118213573199 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 400 : ℝ) - (7 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell6_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell6_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 400 : ℝ) - (7 / 3200 : ℝ)) ≤
      (1 / (118213573199 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (118213573199 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 3200 : ℝ) - Real.pi * Real.exp (3 / 400 : ℝ)) ≤
      (2 / (118213573199 / 5000000000 : ℝ) : ℝ) := by
    rw [show (7 / 3200 : ℝ) - Real.pi * Real.exp (3 / 400 : ℝ) =
      -(Real.pi * Real.exp (3 / 400 : ℝ) - (7 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7923006386395919 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (7923006386395919 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell6_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 800 : ℝ) (7 / 1600 : ℝ)) :
    (17759126049 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (560846391 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell6_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell6_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell7_leftExp :
    (10087883931 / 10000000000 : ℝ) ≤ Real.exp (7 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 800 : ℝ) (1000273474887 / 1000000000000 : ℝ)
    (10087883931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell7_rightExp :
    Real.exp (1 / 100 : ℝ) ≤ (1262562709 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 100 : ℝ) (500156274417 / 500000000000 : ℝ)
    (1262562709 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell7_denomUpper :
    Real.exp (3963723793655437 / 1250000000000000 : ℝ) ≤ (238308041291 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3963723793655437 / 1250000000000000 : ℝ) (1104169087221
    / 1000000000000 : ℝ) (238308041291 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell7_denomLower :
    (23729085819 / 1000000000 : ℝ) ≤ Real.exp (3958376931819769 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3958376931819769 / 1250000000000000 : ℝ) (220804300219 /
    200000000000 : ℝ) (23729085819 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell7_product_lower :
    (3961501931819769 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell7_leftExp
    (by norm_num : (0 : ℝ) ≤ (10087883931 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell7_product_upper :
    Real.pi * Real.exp (1 / 100 : ℝ) ≤ (3966458168655437 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell7_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell7_endpointLower :
    (8879324573 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 1600 : ℝ) (1 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3961501931819769 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell7_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 100 : ℝ) - (7 / 3200 : ℝ)) ≤
      (238308041291 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell7_denomUpper
    linarith [hpThetaJensenCell7_product_upper]
  have hi : (1 / (238308041291 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 100 : ℝ) - (7 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (238308041291 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (238308041291 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 3200 : ℝ) - Real.pi * Real.exp (1 / 100 : ℝ)) := by
    rw [show (7 / 3200 : ℝ) - Real.pi * Real.exp (1 / 100 : ℝ) =
      -(Real.pi * Real.exp (1 / 100 : ℝ) - (7 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 800 : ℝ)) := by
    have h := hpThetaJensenCell7_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (238308041291 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell7_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 1600 : ℝ) (1 / 200 : ℝ) ≤ (8973321803 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 100 : ℝ)) (3966458168655437 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell7_product_upper
  have hD : (23729085819 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 800 : ℝ) - (1 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell7_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell7_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 800 : ℝ) - (1 / 400 : ℝ)) ≤
      (1 / (23729085819 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23729085819 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 400 : ℝ) - Real.pi * Real.exp (7 / 800 : ℝ)) ≤
      (2 / (23729085819 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1 / 400 : ℝ) - Real.pi * Real.exp (7 / 800 : ℝ) =
      -(Real.pi * Real.exp (7 / 800 : ℝ) - (1 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3966458168655437 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (3966458168655437 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell7_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 1600 : ℝ) (1 / 200 : ℝ)) :
    (8879324573 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8973321803 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell7_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell7_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell8_leftExp :
    (1010050167 / 1000000000 : ℝ) ≤ Real.exp (1 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 100 : ℝ) (1000312548833 / 1000000000000 : ℝ)
    (1010050167 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell8_rightExp :
    Real.exp (9 / 800 : ℝ) ≤ (10113135193 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 800 : ℝ) (500175812153 / 500000000000 : ℝ)
    (10113135193 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell8_denomUpper :
    Real.exp (31746354730382449 / 10000000000000000 : ℝ) ≤ (1913447959 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31746354730382449 / 10000000000000000 : ℝ) (220859052173
    / 200000000000 : ℝ) (1913447959 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell8_denomLower :
    (23815890459 / 1000000000 : ℝ) ≤ Real.exp (396294128030733 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (396294128030733 / 125000000000000 : ℝ) (220829497351 /
    200000000000 : ℝ) (23815890459 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell8_product_lower :
    (396645690530733 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell8_leftExp
    (by norm_num : (0 : ℝ) ≤ (1010050167 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell8_product_upper :
    Real.pi * Real.exp (9 / 800 : ℝ) ≤ (31771354730382449 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell8_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell8_endpointLower :
    (17758036873 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 200 : ℝ) (9 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (396645690530733 / 125000000000000 : ℝ) (Real.pi * Real.exp (1 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell8_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 800 : ℝ) - (1 / 400 : ℝ)) ≤
      (1913447959 / 80000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell8_denomUpper
    linarith [hpThetaJensenCell8_product_upper]
  have hi : (1 / (1913447959 / 80000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 800 : ℝ) - (1 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1913447959 / 80000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1913447959 / 80000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 400 : ℝ) - Real.pi * Real.exp (9 / 800 : ℝ)) := by
    rw [show (1 / 400 : ℝ) - Real.pi * Real.exp (9 / 800 : ℝ) =
      -(Real.pi * Real.exp (9 / 800 : ℝ) - (1 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 100 : ℝ)) := by
    have h := hpThetaJensenCell8_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1913447959 / 80000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell8_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 200 : ℝ) (9 / 1600 : ℝ) ≤ (17946066163 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 800 : ℝ)) (31771354730382449 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell8_product_upper
  have hD : (23815890459 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 100 : ℝ) - (9 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell8_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell8_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 100 : ℝ) - (9 / 3200 : ℝ)) ≤
      (1 / (23815890459 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23815890459 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 3200 : ℝ) - Real.pi * Real.exp (1 / 100 : ℝ)) ≤
      (2 / (23815890459 / 1000000000 : ℝ) : ℝ) := by
    rw [show (9 / 3200 : ℝ) - Real.pi * Real.exp (1 / 100 : ℝ) =
      -(Real.pi * Real.exp (1 / 100 : ℝ) - (9 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31771354730382449 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (31771354730382449 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell8_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 200 : ℝ) (9 / 1600 : ℝ)) :
    (17758036873 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17946066163 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell8_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell8_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell9_leftExp :
    (1264141899 / 1250000000 : ℝ) ≤ Real.exp (9 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 800 : ℝ) (200070324861 / 200000000000 : ℝ)
    (1264141899 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell9_rightExp :
    Real.exp (1 / 80 : ℝ) ≤ (2531446129 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 80 : ℝ) (125048837663 / 125000000000 : ℝ)
    (2531446129 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell9_denomUpper :
    Real.exp (7945742188743497 / 2500000000000000 : ℝ) ≤ (240058337931 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7945742188743497 / 2500000000000000 : ℝ) (552210810131 /
    500000000000 : ℝ) (240058337931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell9_denomLower :
    (5975782791 / 250000000 : ℝ) ≤ Real.exp (495938978345401 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (495938978345401 / 156250000000000 : ℝ) (552136828949 /
    500000000000 : ℝ) (5975782791 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell9_product_lower :
    (496427259595401 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell9_leftExp
    (by norm_num : (0 : ℝ) ≤ (1264141899 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell9_product_upper :
    Real.pi * Real.exp (1 / 80 : ℝ) ≤ (7952773438743497 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell9_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell9_endpointLower :
    (17757289297 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 1600 : ℝ) (1 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (496427259595401 / 156250000000000 : ℝ) (Real.pi * Real.exp (9 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell9_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 80 : ℝ) - (9 / 3200 : ℝ)) ≤
      (240058337931 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell9_denomUpper
    linarith [hpThetaJensenCell9_product_upper]
  have hi : (1 / (240058337931 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 80 : ℝ) - (9 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (240058337931 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (240058337931 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 3200 : ℝ) - Real.pi * Real.exp (1 / 80 : ℝ)) := by
    rw [show (9 / 3200 : ℝ) - Real.pi * Real.exp (1 / 80 : ℝ) =
      -(Real.pi * Real.exp (1 / 80 : ℝ) - (9 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 800 : ℝ)) := by
    have h := hpThetaJensenCell9_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (240058337931 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell9_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 1600 : ℝ) (1 / 160 : ℝ) ≤ (4486338063 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 80 : ℝ)) (7952773438743497 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell9_product_upper
  have hD : (5975782791 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 800 : ℝ) - (1 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell9_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell9_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 800 : ℝ) - (1 / 320 : ℝ)) ≤
      (1 / (5975782791 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5975782791 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 320 : ℝ) - Real.pi * Real.exp (9 / 800 : ℝ)) ≤
      (2 / (5975782791 / 250000000 : ℝ) : ℝ) := by
    rw [show (1 / 320 : ℝ) - Real.pi * Real.exp (9 / 800 : ℝ) =
      -(Real.pi * Real.exp (9 / 800 : ℝ) - (1 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7952773438743497 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (7952773438743497 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell9_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 1600 : ℝ) (1 / 160 : ℝ)) :
    (17757289297 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4486338063 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell9_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell9_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell10_leftExp :
    (2025156903 / 2000000000 : ℝ) ≤ Real.exp (1 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 80 : ℝ) (1000390701303 / 1000000000000 : ℝ)
    (2025156903 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell10_rightExp :
    Real.exp (11 / 800 : ℝ) ≤ (10138449661 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 800 : ℝ) (1000429779829 / 1000000000000 : ℝ)
    (10138449661 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell10_denomUpper :
    Real.exp (31819632485849973 / 10000000000000000 : ℝ) ≤ (240940096797 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31819632485849973 / 10000000000000000 : ℝ)
    (1104548165689 / 1000000000000 : ℝ) (240940096797 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell10_denomLower :
    (119954052667 / 5000000000 : ℝ) ≤ Real.exp (794417715651197 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (794417715651197 / 250000000000000 : ℝ) (1104400014779 /
    1000000000000 : ℝ) (119954052667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell10_product_lower :
    (795277090651197 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell10_leftExp
    (by norm_num : (0 : ℝ) ≤ (2025156903 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell10_product_upper :
    Real.pi * Real.exp (11 / 800 : ℝ) ≤ (31850882485849973 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell10_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell10_endpointLower :
    (8878203241 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 160 : ℝ) (11 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (795277090651197 / 250000000000000 : ℝ) (Real.pi * Real.exp (1 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell10_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 800 : ℝ) - (1 / 320 : ℝ)) ≤
      (240940096797 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell10_denomUpper
    linarith [hpThetaJensenCell10_product_upper]
  have hi : (1 / (240940096797 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 800 : ℝ) - (1 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (240940096797 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (240940096797 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 320 : ℝ) - Real.pi * Real.exp (11 / 800 : ℝ)) := by
    rw [show (1 / 320 : ℝ) - Real.pi * Real.exp (11 / 800 : ℝ) =
      -(Real.pi * Real.exp (11 / 800 : ℝ) - (1 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 80 : ℝ)) := by
    have h := hpThetaJensenCell10_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (240940096797 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell10_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 160 : ℝ) (11 / 1600 : ℝ) ≤ (3588900391 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 800 : ℝ)) (31850882485849973 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell10_product_upper
  have hD : (119954052667 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 80 : ℝ) - (11 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell10_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell10_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 80 : ℝ) - (11 / 3200 : ℝ)) ≤
      (1 / (119954052667 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (119954052667 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 3200 : ℝ) - Real.pi * Real.exp (1 / 80 : ℝ)) ≤
      (2 / (119954052667 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 3200 : ℝ) - Real.pi * Real.exp (1 / 80 : ℝ) =
      -(Real.pi * Real.exp (1 / 80 : ℝ) - (11 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31850882485849973 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (31850882485849973 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell10_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 160 : ℝ) (11 / 1600 : ℝ)) :
    (8878203241 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3588900391 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell10_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell10_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell11_leftExp :
    (10138449659 / 10000000000 : ℝ) ≤ Real.exp (11 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 800 : ℝ) (250107444957 / 250000000000 : ℝ)
    (10138449659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell11_rightExp :
    Real.exp (3 / 200 : ℝ) ≤ (10151130647 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 200 : ℝ) (1000468859881 / 1000000000000 : ℝ)
    (10151130647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell11_denomUpper :
    Real.exp (31856345982700671 / 10000000000000000 : ℝ) ≤ (30228287241 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31856345982700671 / 10000000000000000 : ℝ) (552337448707
    / 500000000000 : ℝ) (30228287241 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell11_denomLower :
    (30098664001 / 1250000000 : ℝ) ≤ Real.exp (3976671542639641 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3976671542639641 / 1250000000000000 : ℝ) (1104526557677
    / 1000000000000 : ℝ) (30098664001 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell11_product_lower :
    (3981359042639641 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell11_leftExp
    (by norm_num : (0 : ℝ) ≤ (10138449659 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell11_product_upper :
    Real.pi * Real.exp (3 / 200 : ℝ) ≤ (31890720982700671 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell11_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell11_endpointLower :
    (17755388503 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 1600 : ℝ) (3 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3981359042639641 / 1250000000000000 : ℝ) (Real.pi * Real.exp (11 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell11_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 200 : ℝ) - (11 / 3200 : ℝ)) ≤
      (30228287241 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell11_denomUpper
    linarith [hpThetaJensenCell11_product_upper]
  have hi : (1 / (30228287241 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 200 : ℝ) - (11 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (30228287241 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (30228287241 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 3200 : ℝ) - Real.pi * Real.exp (3 / 200 : ℝ)) := by
    rw [show (11 / 3200 : ℝ) - Real.pi * Real.exp (3 / 200 : ℝ) =
      -(Real.pi * Real.exp (3 / 200 : ℝ) - (11 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 800 : ℝ)) := by
    have h := hpThetaJensenCell11_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (30228287241 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell11_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 1600 : ℝ) (3 / 400 : ℝ) ≤ (17943515337 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 200 : ℝ)) (31890720982700671 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell11_product_upper
  have hD : (30098664001 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 800 : ℝ) - (3 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell11_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell11_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 800 : ℝ) - (3 / 800 : ℝ)) ≤
      (1 / (30098664001 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (30098664001 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 800 : ℝ) - Real.pi * Real.exp (11 / 800 : ℝ)) ≤
      (2 / (30098664001 / 1250000000 : ℝ) : ℝ) := by
    rw [show (3 / 800 : ℝ) - Real.pi * Real.exp (11 / 800 : ℝ) =
      -(Real.pi * Real.exp (11 / 800 : ℝ) - (3 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31890720982700671 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (31890720982700671 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell11_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 1600 : ℝ) (3 / 400 : ℝ)) :
    (17755388503 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17943515337 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell11_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell11_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell12_leftExp :
    (5075565323 / 5000000000 : ℝ) ≤ Real.exp (3 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 200 : ℝ) (25011721497 / 25000000000 : ℝ) (5075565323
    / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell12_rightExp :
    Real.exp (13 / 800 : ℝ) ≤ (5081913747 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 800 : ℝ) (1000507941459 / 1000000000000 : ℝ)
    (5081913747 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell12_denomUpper :
    Real.exp (15946554654178971 / 5000000000000000 : ℝ) ≤ (242716968021 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15946554654178971 / 5000000000000000 : ℝ) (552400907857
    / 500000000000 : ℝ) (242716968021 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell12_denomLower :
    (120837479151 / 5000000000 : ℝ) ≤ Real.exp (1990630364276777 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1990630364276777 / 625000000000000 : ℝ) (1104653286889 /
    1000000000000 : ℝ) (120837479151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell12_product_lower :
    (1993169426776777 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell12_leftExp
    (by norm_num : (0 : ℝ) ≤ (5075565323 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell12_product_upper :
    Real.pi * Real.exp (13 / 800 : ℝ) ≤ (15965304654178971 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell12_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell12_endpointLower :
    (17754235449 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 400 : ℝ) (13 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1993169426776777 / 625000000000000 : ℝ) (Real.pi * Real.exp (3 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell12_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 800 : ℝ) - (3 / 800 : ℝ)) ≤
      (242716968021 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell12_denomUpper
    linarith [hpThetaJensenCell12_product_upper]
  have hi : (1 / (242716968021 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 800 : ℝ) - (3 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (242716968021 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (242716968021 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 800 : ℝ) - Real.pi * Real.exp (13 / 800 : ℝ)) := by
    rw [show (3 / 800 : ℝ) - Real.pi * Real.exp (13 / 800 : ℝ) =
      -(Real.pi * Real.exp (13 / 800 : ℝ) - (3 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 200 : ℝ)) := by
    have h := hpThetaJensenCell12_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (242716968021 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell12_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 400 : ℝ) (13 / 1600 : ℝ) ≤ (17942392463 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 800 : ℝ)) (15965304654178971 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell12_product_upper
  have hD : (120837479151 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 200 : ℝ) - (13 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell12_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell12_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 200 : ℝ) - (13 / 3200 : ℝ)) ≤
      (1 / (120837479151 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (120837479151 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 3200 : ℝ) - Real.pi * Real.exp (3 / 200 : ℝ)) ≤
      (2 / (120837479151 / 5000000000 : ℝ) : ℝ) := by
    rw [show (13 / 3200 : ℝ) - Real.pi * Real.exp (3 / 200 : ℝ) =
      -(Real.pi * Real.exp (3 / 200 : ℝ) - (13 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15965304654178971 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (15965304654178971 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell12_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 400 : ℝ) (13 / 1600 : ℝ)) :
    (17754235449 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17942392463 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell12_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell12_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell13_leftExp :
    (10163827493 / 10000000000 : ℝ) ≤ Real.exp (13 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 800 : ℝ) (500253970729 / 500000000000 : ℝ)
    (10163827493 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell13_rightExp :
    Real.exp (7 / 400 : ℝ) ≤ (5088270111 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 400 : ℝ) (250136756141 / 250000000000 : ℝ)
    (5088270111 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell13_denomUpper :
    Real.exp (15964961262826823 / 5000000000000000 : ℝ) ≤ (121806066979 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15964961262826823 / 5000000000000000 : ℝ) (1104928920867
    / 1000000000000 : ℝ) (121806066979 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell13_denomLower :
    (48513014137 / 2000000000 : ℝ) ≤ Real.exp (3985856142673607 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3985856142673607 / 1250000000000000 : ℝ) (552390101331 /
    500000000000 : ℝ) (48513014137 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell13_product_lower :
    (3991324892673607 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell13_leftExp
    (by norm_num : (0 : ℝ) ≤ (10163827493 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell13_product_upper :
    Real.pi * Real.exp (7 / 400 : ℝ) ≤ (15985273762826823 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell13_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell13_endpointLower :
    (17752947379 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 1600 : ℝ) (7 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3991324892673607 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell13_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 400 : ℝ) - (13 / 3200 : ℝ)) ≤
      (121806066979 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell13_denomUpper
    linarith [hpThetaJensenCell13_product_upper]
  have hi : (1 / (121806066979 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 400 : ℝ) - (13 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (121806066979 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (121806066979 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 3200 : ℝ) - Real.pi * Real.exp (7 / 400 : ℝ)) := by
    rw [show (13 / 3200 : ℝ) - Real.pi * Real.exp (7 / 400 : ℝ) =
      -(Real.pi * Real.exp (7 / 400 : ℝ) - (13 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 800 : ℝ)) := by
    have h := hpThetaJensenCell13_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (121806066979 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell13_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 1600 : ℝ) (7 / 800 : ℝ) ≤ (717645337 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 400 : ℝ)) (15985273762826823 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell13_product_upper
  have hD : (48513014137 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 800 : ℝ) - (7 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell13_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell13_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 800 : ℝ) - (7 / 1600 : ℝ)) ≤
      (1 / (48513014137 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (48513014137 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 1600 : ℝ) - Real.pi * Real.exp (13 / 800 : ℝ)) ≤
      (2 / (48513014137 / 2000000000 : ℝ) : ℝ) := by
    rw [show (7 / 1600 : ℝ) - Real.pi * Real.exp (13 / 800 : ℝ) =
      -(Real.pi * Real.exp (13 / 800 : ℝ) - (7 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15985273762826823 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (15985273762826823 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell13_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 1600 : ℝ) (7 / 800 : ℝ)) :
    (17752947379 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (717645337 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell13_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell13_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell14_leftExp :
    (10176540221 / 10000000000 : ℝ) ≤ Real.exp (7 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 400 : ℝ) (1000547024563 / 1000000000000 : ℝ)
    (10176540221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell14_rightExp :
    Real.exp (3 / 160 : ℝ) ≤ (10189268851 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 160 : ℝ) (200117221839 / 200000000000 : ℝ)
    (10189268851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell14_denomUpper :
    Real.exp (31966785697419643 / 10000000000000000 : ℝ) ≤ (122255911399 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31966785697419643 / 10000000000000000 : ℝ) (22101124263
    / 20000000000 : ℝ) (122255911399 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell14_denomLower :
    (243459676103 / 10000000000 : ℝ) ≤ Real.exp (3990457793246479 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3990457793246479 / 1250000000000000 : ℝ) (220981461057 /
    200000000000 : ℝ) (243459676103 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell14_product_lower :
    (3996317168246479 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell14_leftExp
    (by norm_num : (0 : ℝ) ≤ (10176540221 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell14_product_upper :
    Real.pi * Real.exp (3 / 160 : ℝ) ≤ (32010535697419643 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell14_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell14_endpointLower :
    (17751524381 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 800 : ℝ) (3 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3996317168246479 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell14_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 160 : ℝ) - (7 / 1600 : ℝ)) ≤
      (122255911399 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell14_denomUpper
    linarith [hpThetaJensenCell14_product_upper]
  have hi : (1 / (122255911399 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 160 : ℝ) - (7 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (122255911399 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (122255911399 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 1600 : ℝ) - Real.pi * Real.exp (3 / 160 : ℝ)) := by
    rw [show (7 / 1600 : ℝ) - Real.pi * Real.exp (3 / 160 : ℝ) =
      -(Real.pi * Real.exp (3 / 160 : ℝ) - (7 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 400 : ℝ)) := by
    have h := hpThetaJensenCell14_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (122255911399 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell14_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 800 : ℝ) (3 / 320 : ℝ) ≤ (3587947659 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 160 : ℝ)) (32010535697419643 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell14_product_upper
  have hD : (243459676103 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 400 : ℝ) - (3 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell14_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell14_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 400 : ℝ) - (3 / 640 : ℝ)) ≤
      (1 / (243459676103 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (243459676103 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 640 : ℝ) - Real.pi * Real.exp (7 / 400 : ℝ)) ≤
      (2 / (243459676103 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 640 : ℝ) - Real.pi * Real.exp (7 / 400 : ℝ) =
      -(Real.pi * Real.exp (7 / 400 : ℝ) - (3 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32010535697419643 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32010535697419643 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell14_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 800 : ℝ) (3 / 320 : ℝ)) :
    (17751524381 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3587947659 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell14_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell14_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell15_leftExp :
    (203785377 / 200000000 : ℝ) ≤ Real.exp (3 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 160 : ℝ) (500293054597 / 500000000000 : ℝ)
    (203785377 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell15_rightExp :
    Real.exp (1 / 50 : ℝ) ≤ (10202013401 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 50 : ℝ) (500312597677 / 500000000000 : ℝ)
    (10202013401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell15_denomUpper :
    Real.exp (32003698886487793 / 10000000000000000 : ℝ) ≤ (61354015451 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32003698886487793 / 10000000000000000 : ℝ)
    (1105183692843 / 1000000000000 : ℝ) (61354015451 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell15_denomLower :
    (61089700397 / 2500000000 : ℝ) ≤ Real.exp (79901313762523 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79901313762523 / 25000000000000 : ℝ) (552517297517 /
    500000000000 : ℝ) (61089700397 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell15_product_lower :
    (80026313762523 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell15_leftExp
    (by norm_num : (0 : ℝ) ≤ (203785377 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell15_product_upper :
    Real.pi * Real.exp (1 / 50 : ℝ) ≤ (32050573886487793 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell15_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell15_endpointLower :
    (3549993307 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 320 : ℝ) (1 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (80026313762523 / 25000000000000 : ℝ) (Real.pi * Real.exp (3 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell15_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 50 : ℝ) - (3 / 640 : ℝ)) ≤
      (61354015451 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell15_denomUpper
    linarith [hpThetaJensenCell15_product_upper]
  have hi : (1 / (61354015451 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 50 : ℝ) - (3 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (61354015451 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (61354015451 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 640 : ℝ) - Real.pi * Real.exp (1 / 50 : ℝ)) := by
    rw [show (3 / 640 : ℝ) - Real.pi * Real.exp (1 / 50 : ℝ) =
      -(Real.pi * Real.exp (1 / 50 : ℝ) - (3 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 160 : ℝ)) := by
    have h := hpThetaJensenCell15_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (61354015451 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell15_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 320 : ℝ) (1 / 100 : ℝ) ≤ (4484551789 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 50 : ℝ)) (32050573886487793 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell15_product_upper
  have hD : (61089700397 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 160 : ℝ) - (1 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell15_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell15_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 160 : ℝ) - (1 / 200 : ℝ)) ≤
      (1 / (61089700397 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (61089700397 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 200 : ℝ) - Real.pi * Real.exp (3 / 160 : ℝ)) ≤
      (2 / (61089700397 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1 / 200 : ℝ) - Real.pi * Real.exp (3 / 160 : ℝ) =
      -(Real.pi * Real.exp (3 / 160 : ℝ) - (1 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32050573886487793 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32050573886487793 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell15_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 320 : ℝ) (1 / 100 : ℝ)) :
    (3549993307 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4484551789 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell15_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell15_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell16_leftExp :
    (51010067 / 50000000 : ℝ) ≤ Real.exp (1 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 50 : ℝ) (1000625195353 / 1000000000000 : ℝ)
    (51010067 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell16_rightExp :
    Real.exp (17 / 800 : ℝ) ≤ (10214773891 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 800 : ℝ) (1000664283039 / 1000000000000 : ℝ)
    (10214773891 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell16_denomUpper :
    Real.exp (32040662152548363 / 10000000000000000 : ℝ) ≤ (246324878331 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32040662152548363 / 10000000000000000 : ℝ)
    (1105311360213 / 1000000000000 : ℝ) (246324878331 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell16_denomLower :
    (122631237193 / 5000000000 : ℝ) ≤ Real.exp (19998399175833 / 6250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19998399175833 / 6250000000000 : ℝ) (1105162072189 /
    1000000000000 : ℝ) (122631237193 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell16_product_lower :
    (20031602300833 / 6250000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell16_leftExp
    (by norm_num : (0 : ℝ) ≤ (51010067 / 50000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell16_product_upper :
    Real.pi * Real.exp (17 / 800 : ℝ) ≤ (32090662152548363 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell16_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell16_endpointLower :
    (1774827393 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 100 : ℝ) (17 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20031602300833 / 6250000000000 : ℝ) (Real.pi * Real.exp (1 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell16_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 800 : ℝ) - (1 / 200 : ℝ)) ≤
      (246324878331 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell16_denomUpper
    linarith [hpThetaJensenCell16_product_upper]
  have hi : (1 / (246324878331 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 800 : ℝ) - (1 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (246324878331 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (246324878331 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 200 : ℝ) - Real.pi * Real.exp (17 / 800 : ℝ)) := by
    rw [show (1 / 200 : ℝ) - Real.pi * Real.exp (17 / 800 : ℝ) =
      -(Real.pi * Real.exp (17 / 800 : ℝ) - (1 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 50 : ℝ)) := by
    have h := hpThetaJensenCell16_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (246324878331 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell16_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 100 : ℝ) (17 / 1600 : ℝ) ≤ (4484135021 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 800 : ℝ)) (32090662152548363 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell16_product_upper
  have hD : (122631237193 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 50 : ℝ) - (17 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell16_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell16_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 50 : ℝ) - (17 / 3200 : ℝ)) ≤
      (1 / (122631237193 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (122631237193 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 3200 : ℝ) - Real.pi * Real.exp (1 / 50 : ℝ)) ≤
      (2 / (122631237193 / 5000000000 : ℝ) : ℝ) := by
    rw [show (17 / 3200 : ℝ) - Real.pi * Real.exp (1 / 50 : ℝ) =
      -(Real.pi * Real.exp (1 / 50 : ℝ) - (17 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32090662152548363 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32090662152548363 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell16_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 100 : ℝ) (17 / 1600 : ℝ)) :
    (1774827393 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4484135021 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell16_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell16_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell17_leftExp :
    (1021477389 / 1000000000 : ℝ) ≤ Real.exp (17 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 800 : ℝ) (500332141519 / 500000000000 : ℝ)
    (1021477389 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell17_rightExp :
    Real.exp (9 / 400 : ℝ) ≤ (5113775171 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 400 : ℝ) (1000703372251 / 1000000000000 : ℝ)
    (5113775171 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell17_denomUpper :
    Real.exp (16038837780787403 / 5000000000000000 : ℝ) ≤ (61809575019 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16038837780787403 / 5000000000000000 : ℝ) (1105439215549
    / 1000000000000 : ℝ) (61809575019 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell17_denomLower :
    (61542680459 / 2500000000 : ℝ) ≤ Real.exp (400430024182911 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (400430024182911 / 125000000000000 : ℝ) (1105289737017 /
    1000000000000 : ℝ) (61542680459 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell17_product_lower :
    (401133149182911 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell17_leftExp
    (by norm_num : (0 : ℝ) ≤ (1021477389 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell17_product_upper :
    Real.pi * Real.exp (9 / 400 : ℝ) ≤ (16065400280787403 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell17_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell17_endpointLower :
    (17746446643 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 1600 : ℝ) (9 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (401133149182911 / 125000000000000 : ℝ) (Real.pi * Real.exp (17 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell17_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 400 : ℝ) - (17 / 3200 : ℝ)) ≤
      (61809575019 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell17_denomUpper
    linarith [hpThetaJensenCell17_product_upper]
  have hi : (1 / (61809575019 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 400 : ℝ) - (17 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (61809575019 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (61809575019 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 3200 : ℝ) - Real.pi * Real.exp (9 / 400 : ℝ)) := by
    rw [show (17 / 3200 : ℝ) - Real.pi * Real.exp (9 / 400 : ℝ) =
      -(Real.pi * Real.exp (9 / 400 : ℝ) - (17 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 800 : ℝ)) := by
    have h := hpThetaJensenCell17_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (61809575019 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell17_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 1600 : ℝ) (9 / 800 : ℝ) ≤ (717389487 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 400 : ℝ)) (16065400280787403 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell17_product_upper
  have hD : (61542680459 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 800 : ℝ) - (9 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell17_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell17_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 800 : ℝ) - (9 / 1600 : ℝ)) ≤
      (1 / (61542680459 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (61542680459 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 1600 : ℝ) - Real.pi * Real.exp (17 / 800 : ℝ)) ≤
      (2 / (61542680459 / 2500000000 : ℝ) : ℝ) := by
    rw [show (9 / 1600 : ℝ) - Real.pi * Real.exp (17 / 800 : ℝ) =
      -(Real.pi * Real.exp (17 / 800 : ℝ) - (9 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16065400280787403 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16065400280787403 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell17_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 1600 : ℝ) (9 / 800 : ℝ)) :
    (17746446643 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (717389487 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell17_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell17_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell18_leftExp :
    (10227550341 / 10000000000 : ℝ) ≤ Real.exp (9 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 400 : ℝ) (4002813489 / 4000000000 : ℝ) (10227550341
    / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell18_rightExp :
    Real.exp (19 / 800 : ℝ) ≤ (5120171387 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 800 : ℝ) (100074246299 / 100000000000 : ℝ)
    (5120171387 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell18_denomUpper :
    Real.exp (16057369588199491 / 5000000000000000 : ℝ) ≤ (248156354861 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16057369588199491 / 5000000000000000 : ℝ) (1105567259131
    / 1000000000000 : ℝ) (248156354861 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell18_denomLower :
    (1976668573 / 80000000 : ℝ) ≤ Real.exp (4008926916360359 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4008926916360359 / 1250000000000000 : ℝ) (69088599363 /
    62500000000 : ℝ) (1976668573 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell18_product_lower :
    (4016348791360359 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell18_leftExp
    (by norm_num : (0 : ℝ) ≤ (10227550341 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell18_product_upper :
    Real.pi * Real.exp (19 / 800 : ℝ) ≤ (16085494588199491 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell18_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell18_endpointLower :
    (8872242383 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 800 : ℝ) (19 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4016348791360359 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell18_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 800 : ℝ) - (9 / 1600 : ℝ)) ≤
      (248156354861 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell18_denomUpper
    linarith [hpThetaJensenCell18_product_upper]
  have hi : (1 / (248156354861 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 800 : ℝ) - (9 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (248156354861 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (248156354861 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 1600 : ℝ) - Real.pi * Real.exp (19 / 800 : ℝ)) := by
    rw [show (9 / 1600 : ℝ) - Real.pi * Real.exp (19 / 800 : ℝ) =
      -(Real.pi * Real.exp (19 / 800 : ℝ) - (9 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 400 : ℝ)) := by
    have h := hpThetaJensenCell18_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (248156354861 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell18_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 800 : ℝ) (19 / 1600 : ℝ) ≤ (17932798511 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 800 : ℝ)) (16085494588199491 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell18_product_upper
  have hD : (1976668573 / 80000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 400 : ℝ) - (19 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell18_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell18_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 400 : ℝ) - (19 / 3200 : ℝ)) ≤
      (1 / (1976668573 / 80000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1976668573 / 80000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 3200 : ℝ) - Real.pi * Real.exp (9 / 400 : ℝ)) ≤
      (2 / (1976668573 / 80000000 : ℝ) : ℝ) := by
    rw [show (19 / 3200 : ℝ) - Real.pi * Real.exp (9 / 400 : ℝ) =
      -(Real.pi * Real.exp (9 / 400 : ℝ) - (19 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16085494588199491 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16085494588199491 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell18_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 800 : ℝ) (19 / 1600 : ℝ)) :
    (8872242383 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17932798511 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell18_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell18_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell19_leftExp :
    (10240342773 / 10000000000 : ℝ) ≤ Real.exp (19 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 800 : ℝ) (1000742462989 / 1000000000000 : ℝ)
    (10240342773 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell19_rightExp :
    Real.exp (1 / 40 : ℝ) ≤ (5126575603 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 40 : ℝ) (125097694407 / 125000000000 : ℝ)
    (5126575603 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell19_denomUpper :
    Real.exp (16075926528355579 / 5000000000000000 : ℝ) ≤ (62269767651 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16075926528355579 / 5000000000000000 : ℝ) (552847745613
    / 500000000000 : ℝ) (62269767651 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell19_denomLower :
    (248001051551 / 10000000000 : ℝ) ≤ Real.exp (4013559866614327 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4013559866614327 / 1250000000000000 : ℝ) (1105545630841
    / 1000000000000 : ℝ) (248001051551 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell19_product_lower :
    (4021372366614327 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell19_leftExp
    (by norm_num : (0 : ℝ) ≤ (10240342773 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell19_product_upper :
    Real.pi * Real.exp (1 / 40 : ℝ) ≤ (16105614028355579 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell19_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell19_endpointLower :
    (4435597099 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 1600 : ℝ) (1 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4021372366614327 / 1250000000000000 : ℝ) (Real.pi * Real.exp (19 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell19_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 40 : ℝ) - (19 / 3200 : ℝ)) ≤
      (62269767651 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell19_denomUpper
    linarith [hpThetaJensenCell19_product_upper]
  have hi : (1 / (62269767651 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 40 : ℝ) - (19 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (62269767651 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (62269767651 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 3200 : ℝ) - Real.pi * Real.exp (1 / 40 : ℝ)) := by
    rw [show (19 / 3200 : ℝ) - Real.pi * Real.exp (1 / 40 : ℝ) =
      -(Real.pi * Real.exp (1 / 40 : ℝ) - (19 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 800 : ℝ)) := by
    have h := hpThetaJensenCell19_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (62269767651 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell19_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 1600 : ℝ) (1 / 80 : ℝ) ≤ (1120670261 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 40 : ℝ)) (16105614028355579 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell19_product_upper
  have hD : (248001051551 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 800 : ℝ) - (1 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell19_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell19_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 800 : ℝ) - (1 / 160 : ℝ)) ≤
      (1 / (248001051551 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (248001051551 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 160 : ℝ) - Real.pi * Real.exp (19 / 800 : ℝ)) ≤
      (2 / (248001051551 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 160 : ℝ) - Real.pi * Real.exp (19 / 800 : ℝ) =
      -(Real.pi * Real.exp (19 / 800 : ℝ) - (1 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16105614028355579 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16105614028355579 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell19_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 1600 : ℝ) (1 / 80 : ℝ)) :
    (4435597099 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1120670261 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell19_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell19_endpointUpper

def hpThetaJensenCellsBatch000Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2219892623 / 1250000000 : ℝ)
  | 1 => (3551895531 / 2000000000 : ℝ)
  | 2 => (17759678591 / 10000000000 : ℝ)
  | 3 => (17759743841 / 10000000000 : ℝ)
  | 4 => (8879836727 / 5000000000 : ℝ)
  | 5 => (17759467503 / 10000000000 : ℝ)
  | 6 => (17759126049 / 10000000000 : ℝ)
  | 7 => (8879324573 / 5000000000 : ℝ)
  | 8 => (17758036873 / 10000000000 : ℝ)
  | 9 => (17757289297 / 10000000000 : ℝ)
  | 10 => (8878203241 / 5000000000 : ℝ)
  | 11 => (17755388503 / 10000000000 : ℝ)
  | 12 => (17754235449 / 10000000000 : ℝ)
  | 13 => (17752947379 / 10000000000 : ℝ)
  | 14 => (17751524381 / 10000000000 : ℝ)
  | 15 => (3549993307 / 2000000000 : ℝ)
  | 16 => (1774827393 / 1000000000 : ℝ)
  | 17 => (17746446643 / 10000000000 : ℝ)
  | 18 => (8872242383 / 5000000000 : ℝ)
  | 19 => (4435597099 / 2500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch000Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17946859257 / 10000000000 : ℝ)
  | 1 => (2243404857 / 1250000000 : ℝ)
  | 2 => (1121717597 / 625000000 : ℝ)
  | 3 => (17947587403 / 10000000000 : ℝ)
  | 4 => (17947556479 / 10000000000 : ℝ)
  | 5 => (4486847207 / 2500000000 : ℝ)
  | 6 => (560846391 / 312500000 : ℝ)
  | 7 => (8973321803 / 5000000000 : ℝ)
  | 8 => (17946066163 / 10000000000 : ℝ)
  | 9 => (4486338063 / 2500000000 : ℝ)
  | 10 => (3588900391 / 2000000000 : ℝ)
  | 11 => (17943515337 / 10000000000 : ℝ)
  | 12 => (17942392463 / 10000000000 : ℝ)
  | 13 => (717645337 / 400000000 : ℝ)
  | 14 => (3587947659 / 2000000000 : ℝ)
  | 15 => (4484551789 / 2500000000 : ℝ)
  | 16 => (4484135021 / 2500000000 : ℝ)
  | 17 => (717389487 / 400000000 : ℝ)
  | 18 => (17932798511 / 10000000000 : ℝ)
  | 19 => (1120670261 / 625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch000_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch000Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch000Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell0_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell2_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell3_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell4_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell5_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell6_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell7_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell8_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell9_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell10_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell11_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell12_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell13_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell14_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell15_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell16_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell17_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell18_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell19_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper] at h ⊢
    exact h

end HodgeProofHP
