import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell20_leftExp :
    (2050630241 / 2000000000 : ℝ) ≤ Real.exp (1 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 40 : ℝ) (200156311051 / 200000000000 : ℝ)
    (2050630241 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell20_rightExp :
    Real.exp (21 / 800 : ℝ) ≤ (10265975659 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 800 : ℝ) (1000820649049 / 1000000000000 : ℝ)
    (10265975659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell20_denomUpper :
    Real.exp (32189017268484787 / 10000000000000000 : ℝ) ≤ (250006475583 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32189017268484787 / 10000000000000000 : ℝ) (8846591297 /
    8000000000 : ℝ) (250006475583 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell20_denomLower :
    (31115398689 / 1250000000 : ℝ) ≤ Real.exp (803639820010459 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (803639820010459 / 250000000000000 : ℝ) (1105673860383 /
    1000000000000 : ℝ) (31115398689 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell20_product_lower :
    (805280445010459 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell20_leftExp
    (by norm_num : (0 : ℝ) ≤ (2050630241 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell20_product_upper :
    Real.pi * Real.exp (21 / 800 : ℝ) ≤ (32251517268484787 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell20_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell20_endpointLower :
    (8870078807 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 80 : ℝ) (21 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (805280445010459 / 250000000000000 : ℝ) (Real.pi * Real.exp (1 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell20_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 800 : ℝ) - (1 / 160 : ℝ)) ≤
      (250006475583 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell20_denomUpper
    linarith [hpThetaJensenCell20_product_upper]
  have hi : (1 / (250006475583 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 800 : ℝ) - (1 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (250006475583 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (250006475583 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 160 : ℝ) - Real.pi * Real.exp (21 / 800 : ℝ)) := by
    rw [show (1 / 160 : ℝ) - Real.pi * Real.exp (21 / 800 : ℝ) =
      -(Real.pi * Real.exp (21 / 800 : ℝ) - (1 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 40 : ℝ)) := by
    have h := hpThetaJensenCell20_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (250006475583 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell20_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 80 : ℝ) (21 / 1600 : ℝ) ≤ (17928514273 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 800 : ℝ)) (32251517268484787 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell20_product_upper
  have hD : (31115398689 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 40 : ℝ) - (21 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell20_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell20_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 40 : ℝ) - (21 / 3200 : ℝ)) ≤
      (1 / (31115398689 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31115398689 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 3200 : ℝ) - Real.pi * Real.exp (1 / 40 : ℝ)) ≤
      (2 / (31115398689 / 1250000000 : ℝ) : ℝ) := by
    rw [show (21 / 3200 : ℝ) - Real.pi * Real.exp (1 / 40 : ℝ) =
      -(Real.pi * Real.exp (1 / 40 : ℝ) - (21 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32251517268484787 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32251517268484787 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell20_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 80 : ℝ) (21 / 1600 : ℝ)) :
    (8870078807 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17928514273 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell20_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell20_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell21_leftExp :
    (10265975657 / 10000000000 : ℝ) ≤ Real.exp (21 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 800 : ℝ) (125102581131 / 125000000000 : ℝ)
    (10265975657 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell21_rightExp :
    Real.exp (11 / 400 : ℝ) ≤ (1284852019 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 400 : ℝ) (1000859744369 / 1000000000000 : ℝ)
    (1284852019 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell21_denomUpper :
    Real.exp (4028278983926267 / 1250000000000000 : ℝ) ≤ (50187719621 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4028278983926267 / 1250000000000000 : ℝ) (69122032631 /
    62500000000 : ℝ) (50187719621 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell21_denomLower :
    (124925006849 / 5000000000 : ℝ) ≤ Real.exp (4022844624528243 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4022844624528243 / 1250000000000000 : ℝ) (221160455743 /
    200000000000 : ℝ) (124925006849 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell21_product_lower :
    (4031438374528243 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell21_leftExp
    (by norm_num : (0 : ℝ) ≤ (10265975657 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell21_product_upper :
    Real.pi * Real.exp (11 / 400 : ℝ) ≤ (4036482108926267 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell21_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell21_endpointLower :
    (443444813 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 1600 : ℝ) (11 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4031438374528243 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell21_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 400 : ℝ) - (21 / 3200 : ℝ)) ≤
      (50187719621 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell21_denomUpper
    linarith [hpThetaJensenCell21_product_upper]
  have hi : (1 / (50187719621 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 400 : ℝ) - (21 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (50187719621 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (50187719621 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 3200 : ℝ) - Real.pi * Real.exp (11 / 400 : ℝ)) := by
    rw [show (21 / 3200 : ℝ) - Real.pi * Real.exp (11 / 400 : ℝ) =
      -(Real.pi * Real.exp (11 / 400 : ℝ) - (21 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 800 : ℝ)) := by
    have h := hpThetaJensenCell21_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (50187719621 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell21_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 1600 : ℝ) (11 / 800 : ℝ) ≤ (17926168889 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 400 : ℝ)) (4036482108926267 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell21_product_upper
  have hD : (124925006849 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 800 : ℝ) - (11 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell21_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell21_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 800 : ℝ) - (11 / 1600 : ℝ)) ≤
      (1 / (124925006849 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (124925006849 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 1600 : ℝ) - Real.pi * Real.exp (21 / 800 : ℝ)) ≤
      (2 / (124925006849 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 1600 : ℝ) - Real.pi * Real.exp (21 / 800 : ℝ) =
      -(Real.pi * Real.exp (21 / 800 : ℝ) - (11 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4036482108926267 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4036482108926267 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell21_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 1600 : ℝ) (11 / 800 : ℝ)) :
    (443444813 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17926168889 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell21_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell21_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell22_leftExp :
    (205576323 / 200000000 : ℝ) ≤ Real.exp (11 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 400 : ℝ) (62553734023 / 62500000000 : ℝ) (205576323
    / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell22_rightExp :
    Real.exp (23 / 800 : ℝ) ≤ (2058334541 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 800 : ℝ) (7819522197 / 7812500000 : ℝ)
    (2058334541 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell22_denomUpper :
    Real.exp (6452699385663813 / 2000000000000000 : ℝ) ≤ (125937733381 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6452699385663813 / 2000000000000000 : ℝ) (55304066071 /
    50000000000 : ℝ) (125937733381 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell22_denomLower :
    (125390776271 / 5000000000 : ℝ) ≤ Real.exp (80549928965777 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (80549928965777 / 25000000000000 : ℝ) (8847447089 /
    8000000000 : ℝ) (125390776271 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell22_product_lower :
    (80729616465777 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell22_leftExp
    (by norm_num : (0 : ℝ) ≤ (205576323 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell22_product_upper :
    Real.pi * Real.exp (23 / 800 : ℝ) ≤ (6466449385663813 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell22_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell22_endpointLower :
    (17735293217 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 800 : ℝ) (23 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (80729616465777 / 25000000000000 : ℝ) (Real.pi * Real.exp (11 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell22_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 800 : ℝ) - (11 / 1600 : ℝ)) ≤
      (125937733381 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell22_denomUpper
    linarith [hpThetaJensenCell22_product_upper]
  have hi : (1 / (125937733381 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 800 : ℝ) - (11 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (125937733381 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (125937733381 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 1600 : ℝ) - Real.pi * Real.exp (23 / 800 : ℝ)) := by
    rw [show (11 / 1600 : ℝ) - Real.pi * Real.exp (23 / 800 : ℝ) =
      -(Real.pi * Real.exp (23 / 800 : ℝ) - (11 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 400 : ℝ)) := by
    have h := hpThetaJensenCell22_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (125937733381 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell22_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 800 : ℝ) (23 / 1600 : ℝ) ≤ (4480922029 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 800 : ℝ)) (6466449385663813 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell22_product_upper
  have hD : (125390776271 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 400 : ℝ) - (23 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell22_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell22_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 400 : ℝ) - (23 / 3200 : ℝ)) ≤
      (1 / (125390776271 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (125390776271 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 3200 : ℝ) - Real.pi * Real.exp (11 / 400 : ℝ)) ≤
      (2 / (125390776271 / 5000000000 : ℝ) : ℝ) := by
    rw [show (23 / 3200 : ℝ) - Real.pi * Real.exp (11 / 400 : ℝ) =
      -(Real.pi * Real.exp (11 / 400 : ℝ) - (23 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6466449385663813 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (6466449385663813 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell22_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 800 : ℝ) (23 / 1600 : ℝ)) :
    (17735293217 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4480922029 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell22_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell22_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell23_leftExp :
    (80403693 / 78125000 : ℝ) ≤ Real.exp (23 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 800 : ℝ) (200179768243 / 200000000000 : ℝ)
    (80403693 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell23_rightExp :
    Real.exp (3 / 100 : ℝ) ≤ (515227267 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 100 : ℝ) (1000937939591 / 1000000000000 : ℝ)
    (515227267 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell23_denomUpper :
    Real.exp (1615040625416331 / 500000000000000 : ℝ) ≤ (126408555241 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1615040625416331 / 500000000000000 : ℝ) (1106210310397 /
    1000000000000 : ℝ) (126408555241 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell23_denomLower :
    (125858917317 / 5000000000 : ℝ) ≤ Real.exp (31501207649907 / 9765625000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31501207649907 / 9765625000000 : ℝ) (69128730181 /
    62500000000 : ℝ) (125858917317 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell23_product_lower :
    (31574449837407 / 9765625000000 : ℝ) ≤ Real.pi * Real.exp (23 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell23_leftExp
    (by norm_num : (0 : ℝ) ≤ (80403693 / 78125000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell23_product_upper :
    Real.pi * Real.exp (3 / 100 : ℝ) ≤ (1618634375416331 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell23_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell23_endpointLower :
    (1108291237 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 1600 : ℝ) (3 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (31574449837407 / 9765625000000 : ℝ) (Real.pi * Real.exp (23 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell23_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 100 : ℝ) - (23 / 3200 : ℝ)) ≤
      (126408555241 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell23_denomUpper
    linarith [hpThetaJensenCell23_product_upper]
  have hi : (1 / (126408555241 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 100 : ℝ) - (23 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (126408555241 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (126408555241 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 3200 : ℝ) - Real.pi * Real.exp (3 / 100 : ℝ)) := by
    rw [show (23 / 3200 : ℝ) - Real.pi * Real.exp (3 / 100 : ℝ) =
      -(Real.pi * Real.exp (3 / 100 : ℝ) - (23 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 800 : ℝ)) := by
    have h := hpThetaJensenCell23_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (126408555241 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell23_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 1600 : ℝ) (3 / 200 : ℝ) ≤ (896053603 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 100 : ℝ)) (1618634375416331 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell23_product_upper
  have hD : (125858917317 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 800 : ℝ) - (3 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell23_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell23_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 800 : ℝ) - (3 / 400 : ℝ)) ≤
      (1 / (125858917317 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (125858917317 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 400 : ℝ) - Real.pi * Real.exp (23 / 800 : ℝ)) ≤
      (2 / (125858917317 / 5000000000 : ℝ) : ℝ) := by
    rw [show (3 / 400 : ℝ) - Real.pi * Real.exp (23 / 800 : ℝ) =
      -(Real.pi * Real.exp (23 / 800 : ℝ) - (3 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1618634375416331 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1618634375416331 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell23_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 1600 : ℝ) (3 / 200 : ℝ)) :
    (1108291237 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (896053603 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell23_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell23_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell24_leftExp :
    (10304545339 / 10000000000 : ℝ) ≤ Real.exp (3 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 100 : ℝ) (100093793959 / 100000000000 : ℝ)
    (10304545339 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell24_rightExp :
    Real.exp (1 / 32 : ℝ) ≤ (2579358519 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 32 : ℝ) (1000977039493 / 1000000000000 : ℝ)
    (2579358519 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell24_denomUpper :
    Real.exp (8084544667780767 / 2500000000000000 : ℝ) ≤ (31720444771 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8084544667780767 / 2500000000000000 : ℝ) (1106339489297
    / 1000000000000 : ℝ) (31720444771 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell24_denomLower :
    (50531777743 / 2000000000 : ℝ) ≤ Real.exp (4036819025079961 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4036819025079961 / 1250000000000000 : ℝ) (221237733861 /
    200000000000 : ℝ) (50531777743 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell24_product_lower :
    (4046584650079961 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell24_leftExp
    (by norm_num : (0 : ℝ) ≤ (10304545339 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell24_product_upper :
    Real.pi * Real.exp (1 / 32 : ℝ) ≤ (8103294667780767 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell24_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell24_endpointLower :
    (17729892351 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 200 : ℝ) (1 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4046584650079961 / 1250000000000000 : ℝ) (Real.pi * Real.exp (3 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell24_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 32 : ℝ) - (3 / 400 : ℝ)) ≤
      (31720444771 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell24_denomUpper
    linarith [hpThetaJensenCell24_product_upper]
  have hi : (1 / (31720444771 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 32 : ℝ) - (3 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31720444771 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31720444771 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 400 : ℝ) - Real.pi * Real.exp (1 / 32 : ℝ)) := by
    rw [show (3 / 400 : ℝ) - Real.pi * Real.exp (1 / 32 : ℝ) =
      -(Real.pi * Real.exp (1 / 32 : ℝ) - (3 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 100 : ℝ)) := by
    have h := hpThetaJensenCell24_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31720444771 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell24_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 200 : ℝ) (1 / 64 : ℝ) ≤ (17918320817 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 32 : ℝ)) (8103294667780767 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell24_product_upper
  have hD : (50531777743 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 100 : ℝ) - (1 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell24_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell24_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 100 : ℝ) - (1 / 128 : ℝ)) ≤
      (1 / (50531777743 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (50531777743 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 128 : ℝ) - Real.pi * Real.exp (3 / 100 : ℝ)) ≤
      (2 / (50531777743 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1 / 128 : ℝ) - Real.pi * Real.exp (3 / 100 : ℝ) =
      -(Real.pi * Real.exp (3 / 100 : ℝ) - (1 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8103294667780767 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8103294667780767 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell24_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 200 : ℝ) (1 / 64 : ℝ)) :
    (17729892351 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17918320817 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell24_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell24_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell25_leftExp :
    (5158717037 / 5000000000 : ℝ) ≤ Real.exp (1 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 32 : ℝ) (250244259873 / 250000000000 : ℝ)
    (5158717037 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell25_rightExp :
    Real.exp (13 / 400 : ℝ) ≤ (2582584733 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 400 : ℝ) (500508070461 / 500000000000 : ℝ)
    (2582584733 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell25_denomUpper :
    Real.exp (8093898869099669 / 2500000000000000 : ℝ) ≤ (63678709729 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8093898869099669 / 2500000000000000 : ℝ) (1106468858389
    / 1000000000000 : ℝ) (63678709729 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell25_denomLower :
    (31700592959 / 1250000000 : ℝ) ≤ Real.exp (2020744896712863 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2020744896712863 / 625000000000000 : ℝ) (553158922811 /
    500000000000 : ℝ) (31700592959 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell25_product_lower :
    (2025823021712863 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell25_leftExp
    (by norm_num : (0 : ℝ) ≤ (5158717037 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell25_product_upper :
    Real.pi * Real.exp (13 / 400 : ℝ) ≤ (8113430119099669 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell25_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell25_endpointLower :
    (17726990999 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 64 : ℝ) (13 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2025823021712863 / 625000000000000 : ℝ) (Real.pi * Real.exp (1 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell25_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 400 : ℝ) - (1 / 128 : ℝ)) ≤
      (63678709729 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell25_denomUpper
    linarith [hpThetaJensenCell25_product_upper]
  have hi : (1 / (63678709729 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 400 : ℝ) - (1 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (63678709729 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (63678709729 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 128 : ℝ) - Real.pi * Real.exp (13 / 400 : ℝ)) := by
    rw [show (1 / 128 : ℝ) - Real.pi * Real.exp (13 / 400 : ℝ) =
      -(Real.pi * Real.exp (13 / 400 : ℝ) - (1 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 32 : ℝ)) := by
    have h := hpThetaJensenCell25_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (63678709729 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell25_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 64 : ℝ) (13 / 800 : ℝ) ≤ (1791543449 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 400 : ℝ)) (8113430119099669 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell25_product_upper
  have hD : (31700592959 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 32 : ℝ) - (13 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell25_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell25_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 32 : ℝ) - (13 / 1600 : ℝ)) ≤
      (1 / (31700592959 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31700592959 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 1600 : ℝ) - Real.pi * Real.exp (1 / 32 : ℝ)) ≤
      (2 / (31700592959 / 1250000000 : ℝ) : ℝ) := by
    rw [show (13 / 1600 : ℝ) - Real.pi * Real.exp (1 / 32 : ℝ) =
      -(Real.pi * Real.exp (1 / 32 : ℝ) - (13 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8113430119099669 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8113430119099669 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell25_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 64 : ℝ) (13 / 800 : ℝ)) :
    (17726990999 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1791543449 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell25_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell25_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell26_leftExp :
    (10330338931 / 10000000000 : ℝ) ≤ Real.exp (13 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 400 : ℝ) (1001016140921 / 1000000000000 : ℝ)
    (10330338931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell26_rightExp :
    Real.exp (27 / 800 : ℝ) ≤ (1034325993 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 800 : ℝ) (1001055243879 / 1000000000000 : ℝ)
    (1034325993 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell26_denomUpper :
    Real.exp (3241306299326849 / 1000000000000000 : ℝ) ≤ (255670982261 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3241306299326849 / 1000000000000000 : ℝ) (44263936719 /
    40000000000 : ℝ) (255670982261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell26_denomLower :
    (254555428823 / 10000000000 : ℝ) ≤ Real.exp (4046166892864769 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4046166892864769 / 1250000000000000 : ℝ) (1106447212149
    / 1000000000000 : ℝ) (254555428823 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell26_product_lower :
    (4056713767864769 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell26_leftExp
    (by norm_num : (0 : ℝ) ≤ (10330338931 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell26_product_upper :
    Real.pi * Real.exp (27 / 800 : ℝ) ≤ (3249431299326849 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell26_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell26_endpointLower :
    (27693681 / 15625000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 800 : ℝ) (27 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4056713767864769 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell26_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 800 : ℝ) - (13 / 1600 : ℝ)) ≤
      (255670982261 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell26_denomUpper
    linarith [hpThetaJensenCell26_product_upper]
  have hi : (1 / (255670982261 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 800 : ℝ) - (13 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (255670982261 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (255670982261 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 1600 : ℝ) - Real.pi * Real.exp (27 / 800 : ℝ)) := by
    rw [show (13 / 1600 : ℝ) - Real.pi * Real.exp (27 / 800 : ℝ) =
      -(Real.pi * Real.exp (27 / 800 : ℝ) - (13 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 400 : ℝ)) := by
    have h := hpThetaJensenCell26_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (255670982261 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell26_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 800 : ℝ) (27 / 1600 : ℝ) ≤ (17912413183 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 800 : ℝ)) (3249431299326849 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell26_product_upper
  have hD : (254555428823 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 400 : ℝ) - (27 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell26_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell26_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 400 : ℝ) - (27 / 3200 : ℝ)) ≤
      (1 / (254555428823 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (254555428823 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 3200 : ℝ) - Real.pi * Real.exp (13 / 400 : ℝ)) ≤
      (2 / (254555428823 / 10000000000 : ℝ) : ℝ) := by
    rw [show (27 / 3200 : ℝ) - Real.pi * Real.exp (13 / 400 : ℝ) =
      -(Real.pi * Real.exp (13 / 400 : ℝ) - (27 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3249431299326849 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3249431299326849 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell26_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 800 : ℝ) (27 / 1600 : ℝ)) :
    (27693681 / 15625000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17912413183 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell26_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell26_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell27_leftExp :
    (1292907491 / 1250000000 : ℝ) ≤ Real.exp (27 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 800 : ℝ) (500527621939 / 500000000000 : ℝ)
    (1292907491 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell27_rightExp :
    Real.exp (7 / 200 : ℝ) ≤ (10356197089 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 200 : ℝ) (1001094348363 / 1000000000000 : ℝ)
    (10356197089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell27_denomUpper :
    Real.exp (32450581281422777 / 10000000000000000 : ℝ) ≤ (128316008857 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32450581281422777 / 10000000000000000 : ℝ) (553364084163
    / 500000000000 : ℝ) (128316008857 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell27_denomLower :
    (3992358959 / 156250000 : ℝ) ≤ Real.exp (506356291308209 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (506356291308209 / 156250000000000 : ℝ) (553288384573 /
    500000000000 : ℝ) (3992358959 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell27_product_lower :
    (507723478808209 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell27_leftExp
    (by norm_num : (0 : ℝ) ≤ (1292907491 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell27_product_upper :
    Real.pi * Real.exp (7 / 200 : ℝ) ≤ (32534956281422777 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell27_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell27_endpointLower :
    (553774593 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 1600 : ℝ) (7 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (507723478808209 / 156250000000000 : ℝ) (Real.pi * Real.exp (27 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell27_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 200 : ℝ) - (27 / 3200 : ℝ)) ≤
      (128316008857 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell27_denomUpper
    linarith [hpThetaJensenCell27_product_upper]
  have hi : (1 / (128316008857 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 200 : ℝ) - (27 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (128316008857 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (128316008857 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 3200 : ℝ) - Real.pi * Real.exp (7 / 200 : ℝ)) := by
    rw [show (27 / 3200 : ℝ) - Real.pi * Real.exp (7 / 200 : ℝ) =
      -(Real.pi * Real.exp (7 / 200 : ℝ) - (27 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 800 : ℝ)) := by
    have h := hpThetaJensenCell27_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (128316008857 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell27_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 1600 : ℝ) (7 / 400 : ℝ) ≤ (17909257007 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 200 : ℝ)) (32534956281422777 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell27_product_upper
  have hD : (3992358959 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 800 : ℝ) - (7 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell27_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell27_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 800 : ℝ) - (7 / 800 : ℝ)) ≤
      (1 / (3992358959 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3992358959 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 800 : ℝ) - Real.pi * Real.exp (27 / 800 : ℝ)) ≤
      (2 / (3992358959 / 156250000 : ℝ) : ℝ) := by
    rw [show (7 / 800 : ℝ) - Real.pi * Real.exp (27 / 800 : ℝ) =
      -(Real.pi * Real.exp (27 / 800 : ℝ) - (7 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32534956281422777 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32534956281422777 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell27_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 1600 : ℝ) (7 / 400 : ℝ)) :
    (553774593 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17909257007 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell27_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell27_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell28_leftExp :
    (10356197087 / 10000000000 : ℝ) ≤ Real.exp (7 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 200 : ℝ) (500547174181 / 500000000000 : ℝ)
    (10356197087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell28_rightExp :
    Real.exp (29 / 800 : ℝ) ≤ (10369150429 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 800 : ℝ) (1601813527 / 1600000000 : ℝ)
    (10369150429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell28_denomUpper :
    Real.exp (32488150403693397 / 10000000000000000 : ℝ) ≤ (257597975051 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32488150403693397 / 10000000000000000 : ℝ) (553429054861
    / 500000000000 : ℝ) (257597975051 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell28_denomLower :
    (64117851761 / 2500000000 : ℝ) ≤ Real.exp (4055540114867813 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4055540114867813 / 1250000000000000 : ℝ) (553353258457 /
    500000000000 : ℝ) (64117851761 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell28_product_lower :
    (4066868239867813 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell28_leftExp
    (by norm_num : (0 : ℝ) ≤ (10356197087 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell28_product_upper :
    Real.pi * Real.exp (29 / 800 : ℝ) ≤ (32575650403693397 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell28_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell28_endpointLower :
    (17717484527 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 400 : ℝ) (29 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4066868239867813 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell28_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 800 : ℝ) - (7 / 800 : ℝ)) ≤
      (257597975051 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell28_denomUpper
    linarith [hpThetaJensenCell28_product_upper]
  have hi : (1 / (257597975051 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 800 : ℝ) - (7 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (257597975051 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (257597975051 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 800 : ℝ) - Real.pi * Real.exp (29 / 800 : ℝ)) := by
    rw [show (7 / 800 : ℝ) - Real.pi * Real.exp (29 / 800 : ℝ) =
      -(Real.pi * Real.exp (29 / 800 : ℝ) - (7 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 200 : ℝ)) := by
    have h := hpThetaJensenCell28_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (257597975051 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell28_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 400 : ℝ) (29 / 1600 : ℝ) ≤ (895298303 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 800 : ℝ)) (32575650403693397 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell28_product_upper
  have hD : (64117851761 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 200 : ℝ) - (29 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell28_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell28_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 200 : ℝ) - (29 / 3200 : ℝ)) ≤
      (1 / (64117851761 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (64117851761 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 3200 : ℝ) - Real.pi * Real.exp (7 / 200 : ℝ)) ≤
      (2 / (64117851761 / 2500000000 : ℝ) : ℝ) := by
    rw [show (29 / 3200 : ℝ) - Real.pi * Real.exp (7 / 200 : ℝ) =
      -(Real.pi * Real.exp (7 / 200 : ℝ) - (29 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32575650403693397 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32575650403693397 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell28_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 400 : ℝ) (29 / 1600 : ℝ)) :
    (17717484527 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (895298303 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell28_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell28_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell29_leftExp :
    (2592287607 / 2500000000 : ℝ) ≤ Real.exp (29 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 800 : ℝ) (500566727187 / 500000000000 : ℝ)
    (2592287607 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell29_rightExp :
    Real.exp (3 / 80 : ℝ) ≤ (10382119971 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 80 : ℝ) (500586280957 / 500000000000 : ℝ)
    (10382119971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell29_denomUpper :
    Real.exp (32525770426053803 / 10000000000000000 : ℝ) ≤ (51713776869 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32525770426053803 / 10000000000000000 : ℝ) (221397648491
    / 200000000000 : ℝ) (51713776869 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell29_denomLower :
    (128718379797 / 5000000000 : ℝ) ≤ Real.exp (1015059063481293 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1015059063481293 / 312500000000000 : ℝ) (553418227867 /
    500000000000 : ℝ) (128718379797 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell29_product_lower :
    (1017988750981293 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell29_leftExp
    (by norm_num : (0 : ℝ) ≤ (2592287607 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell29_product_upper :
    Real.pi * Real.exp (3 / 80 : ℝ) ≤ (32616395426053803 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell29_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell29_endpointLower :
    (88570243 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 1600 : ℝ) (3 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1017988750981293 / 312500000000000 : ℝ) (Real.pi * Real.exp (29 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell29_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 80 : ℝ) - (29 / 3200 : ℝ)) ≤
      (51713776869 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell29_denomUpper
    linarith [hpThetaJensenCell29_product_upper]
  have hi : (1 / (51713776869 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 80 : ℝ) - (29 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51713776869 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51713776869 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 3200 : ℝ) - Real.pi * Real.exp (3 / 80 : ℝ)) := by
    rw [show (29 / 3200 : ℝ) - Real.pi * Real.exp (3 / 80 : ℝ) =
      -(Real.pi * Real.exp (3 / 80 : ℝ) - (29 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 800 : ℝ)) := by
    have h := hpThetaJensenCell29_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51713776869 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell29_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 1600 : ℝ) (3 / 160 : ℝ) ≤ (17902540459 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 80 : ℝ)) (32616395426053803 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell29_product_upper
  have hD : (128718379797 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 800 : ℝ) - (3 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell29_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell29_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 800 : ℝ) - (3 / 320 : ℝ)) ≤
      (1 / (128718379797 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (128718379797 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 320 : ℝ) - Real.pi * Real.exp (29 / 800 : ℝ)) ≤
      (2 / (128718379797 / 5000000000 : ℝ) : ℝ) := by
    rw [show (3 / 320 : ℝ) - Real.pi * Real.exp (29 / 800 : ℝ) =
      -(Real.pi * Real.exp (29 / 800 : ℝ) - (3 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32616395426053803 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32616395426053803 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell29_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 1600 : ℝ) (3 / 160 : ℝ)) :
    (88570243 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17902540459 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell29_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell29_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell30_leftExp :
    (1038211997 / 1000000000 : ℝ) ≤ Real.exp (3 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 80 : ℝ) (1001172561913 / 1000000000000 : ℝ)
    (1038211997 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell30_rightExp :
    Real.exp (31 / 800 : ℝ) ≤ (1299388217 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 800 : ℝ) (1001211670981 / 1000000000000 : ℝ)
    (1299388217 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell30_denomUpper :
    Real.exp (4070430176809681 / 1250000000000000 : ℝ) ≤ (259544775881 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4070430176809681 / 1250000000000000 : ℝ) (553559283409 /
    500000000000 : ℝ) (259544775881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell30_denomLower :
    (51681412183 / 2000000000 : ℝ) ≤ Real.exp (406493875509903 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (406493875509903 / 125000000000000 : ℝ) (276741646469 /
    250000000000 : ℝ) (51681412183 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell30_product_lower :
    (407704813009903 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell30_leftExp
    (by norm_num : (0 : ℝ) ≤ (1038211997 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell30_product_upper :
    Real.pi * Real.exp (31 / 800 : ℝ) ≤ (4082148926809681 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell30_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell30_endpointLower :
    (17710479297 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 160 : ℝ) (31 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (407704813009903 / 125000000000000 : ℝ) (Real.pi * Real.exp (3 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell30_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 800 : ℝ) - (3 / 320 : ℝ)) ≤
      (259544775881 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell30_denomUpper
    linarith [hpThetaJensenCell30_product_upper]
  have hi : (1 / (259544775881 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 800 : ℝ) - (3 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (259544775881 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (259544775881 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 320 : ℝ) - Real.pi * Real.exp (31 / 800 : ℝ)) := by
    rw [show (3 / 320 : ℝ) - Real.pi * Real.exp (31 / 800 : ℝ) =
      -(Real.pi * Real.exp (31 / 800 : ℝ) - (3 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 80 : ℝ)) := by
    have h := hpThetaJensenCell30_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (259544775881 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell30_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 160 : ℝ) (31 / 1600 : ℝ) ≤ (17898980327 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 800 : ℝ)) (4082148926809681 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell30_product_upper
  have hD : (51681412183 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 80 : ℝ) - (31 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell30_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell30_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 80 : ℝ) - (31 / 3200 : ℝ)) ≤
      (1 / (51681412183 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (51681412183 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 3200 : ℝ) - Real.pi * Real.exp (3 / 80 : ℝ)) ≤
      (2 / (51681412183 / 2000000000 : ℝ) : ℝ) := by
    rw [show (31 / 3200 : ℝ) - Real.pi * Real.exp (3 / 80 : ℝ) =
      -(Real.pi * Real.exp (3 / 80 : ℝ) - (31 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4082148926809681 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4082148926809681 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell30_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 160 : ℝ) (31 / 1600 : ℝ)) :
    (17710479297 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17898980327 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell30_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell30_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell31_leftExp :
    (5197552867 / 5000000000 : ℝ) ≤ Real.exp (31 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 800 : ℝ) (50060583549 / 50000000000 : ℝ)
    (5197552867 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell31_rightExp :
    Real.exp (1 / 25 : ℝ) ≤ (10408107743 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 25 : ℝ) (125156347697 / 125000000000 : ℝ)
    (10408107743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell31_denomUpper :
    Real.exp (32601163428654599 / 10000000000000000 : ℝ) ≤ (65131419993 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32601163428654599 / 10000000000000000 : ℝ) (27681227077
    / 25000000000 : ℝ) (65131419993 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell31_denomLower :
    (129691170637 / 5000000000 : ℝ) ≤ Real.exp (2034823813318033 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2034823813318033 / 625000000000000 : ℝ) (1107096907633 /
    1000000000000 : ℝ) (129691170637 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell31_product_lower :
    (2041073813318033 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell31_leftExp
    (by norm_num : (0 : ℝ) ≤ (5197552867 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell31_product_upper :
    Real.pi * Real.exp (1 / 25 : ℝ) ≤ (32698038428654599 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell31_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell31_endpointLower :
    (17706776747 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 1600 : ℝ) (1 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2041073813318033 / 625000000000000 : ℝ) (Real.pi * Real.exp (31 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell31_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 25 : ℝ) - (31 / 3200 : ℝ)) ≤
      (65131419993 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell31_denomUpper
    linarith [hpThetaJensenCell31_product_upper]
  have hi : (1 / (65131419993 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 25 : ℝ) - (31 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65131419993 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65131419993 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 3200 : ℝ) - Real.pi * Real.exp (1 / 25 : ℝ)) := by
    rw [show (31 / 3200 : ℝ) - Real.pi * Real.exp (1 / 25 : ℝ) =
      -(Real.pi * Real.exp (1 / 25 : ℝ) - (31 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 800 : ℝ)) := by
    have h := hpThetaJensenCell31_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65131419993 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell31_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 1600 : ℝ) (1 / 50 : ℝ) ≤ (17895285769 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 25 : ℝ)) (32698038428654599 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell31_product_upper
  have hD : (129691170637 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 800 : ℝ) - (1 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell31_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell31_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 800 : ℝ) - (1 / 100 : ℝ)) ≤
      (1 / (129691170637 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (129691170637 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 100 : ℝ) - Real.pi * Real.exp (31 / 800 : ℝ)) ≤
      (2 / (129691170637 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 100 : ℝ) - Real.pi * Real.exp (31 / 800 : ℝ) =
      -(Real.pi * Real.exp (31 / 800 : ℝ) - (1 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32698038428654599 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (32698038428654599 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell31_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 1600 : ℝ) (1 / 50 : ℝ)) :
    (17706776747 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17895285769 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell31_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell31_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell32_leftExp :
    (10408107741 / 10000000000 : ℝ) ≤ Real.exp (1 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 25 : ℝ) (40050031263 / 40000000000 : ℝ) (10408107741
    / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell32_rightExp :
    Real.exp (33 / 800 : ℝ) ≤ (2605281503 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 800 : ℝ) (1001289893699 / 1000000000000 : ℝ)
    (2605281503 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell32_denomUpper :
    Real.exp (8159734132854279 / 2500000000000000 : ℝ) ≤ (65377906811 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8159734132854279 / 2500000000000000 : ℝ) (276844947881 /
    250000000000 : ℝ) (65377906811 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell32_denomLower :
    (8136332223 / 312500000 : ℝ) ≤ Real.exp (4074362876782959 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4074362876782959 / 1250000000000000 : ℝ) (1107227421297
    / 1000000000000 : ℝ) (8136332223 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell32_product_lower :
    (4087253501782959 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell32_leftExp
    (by norm_num : (0 : ℝ) ≤ (10408107741 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell32_product_upper :
    Real.pi * Real.exp (33 / 800 : ℝ) ≤ (8184734132854279 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell32_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell32_endpointLower :
    (1770294107 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 50 : ℝ) (33 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4087253501782959 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell32_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 800 : ℝ) - (1 / 100 : ℝ)) ≤
      (65377906811 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell32_denomUpper
    linarith [hpThetaJensenCell32_product_upper]
  have hi : (1 / (65377906811 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 800 : ℝ) - (1 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65377906811 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65377906811 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 100 : ℝ) - Real.pi * Real.exp (33 / 800 : ℝ)) := by
    rw [show (1 / 100 : ℝ) - Real.pi * Real.exp (33 / 800 : ℝ) =
      -(Real.pi * Real.exp (33 / 800 : ℝ) - (1 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 25 : ℝ)) := by
    have h := hpThetaJensenCell32_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65377906811 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell32_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 50 : ℝ) (33 / 1600 : ℝ) ≤ (3578291379 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 800 : ℝ)) (8184734132854279 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell32_product_upper
  have hD : (8136332223 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 25 : ℝ) - (33 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell32_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell32_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 25 : ℝ) - (33 / 3200 : ℝ)) ≤
      (1 / (8136332223 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8136332223 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 3200 : ℝ) - Real.pi * Real.exp (1 / 25 : ℝ)) ≤
      (2 / (8136332223 / 312500000 : ℝ) : ℝ) := by
    rw [show (33 / 3200 : ℝ) - Real.pi * Real.exp (1 / 25 : ℝ) =
      -(Real.pi * Real.exp (1 / 25 : ℝ) - (33 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8184734132854279 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8184734132854279 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell32_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 50 : ℝ) (33 / 1600 : ℝ)) :
    (1770294107 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3578291379 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell32_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell32_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell33_leftExp :
    (10421126011 / 10000000000 : ℝ) ≤ Real.exp (33 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 800 : ℝ) (500644946849 / 500000000000 : ℝ)
    (10421126011 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell33_rightExp :
    Real.exp (17 / 400 : ℝ) ≤ (2608540141 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 400 : ℝ) (1001329007349 / 1000000000000 : ℝ)
    (2608540141 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell33_denomUpper :
    Real.exp (8169190197184613 / 2500000000000000 : ℝ) ≤ (65625662149 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8169190197184613 / 2500000000000000 : ℝ) (1107510692441
    / 1000000000000 : ℝ) (65625662149 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell33_denomLower :
    (130673980547 / 5000000000 : ℝ) ≤ Real.exp (4079084513393689 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4079084513393689 / 1250000000000000 : ℝ) (1107358127149
    / 1000000000000 : ℝ) (130673980547 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell33_product_lower :
    (4092365763393689 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell33_leftExp
    (by norm_num : (0 : ℝ) ≤ (10421126011 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell33_product_upper :
    Real.pi * Real.exp (17 / 400 : ℝ) ≤ (8194971447184613 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell33_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell33_endpointLower :
    (553092887 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 1600 : ℝ) (17 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4092365763393689 / 1250000000000000 : ℝ) (Real.pi * Real.exp (33 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell33_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 400 : ℝ) - (33 / 3200 : ℝ)) ≤
      (65625662149 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell33_denomUpper
    linarith [hpThetaJensenCell33_product_upper]
  have hi : (1 / (65625662149 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 400 : ℝ) - (33 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65625662149 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65625662149 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 3200 : ℝ) - Real.pi * Real.exp (17 / 400 : ℝ)) := by
    rw [show (33 / 3200 : ℝ) - Real.pi * Real.exp (17 / 400 : ℝ) =
      -(Real.pi * Real.exp (17 / 400 : ℝ) - (33 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 800 : ℝ)) := by
    have h := hpThetaJensenCell33_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65625662149 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell33_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 1600 : ℝ) (17 / 800 : ℝ) ≤ (2235936729 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 400 : ℝ)) (8194971447184613 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell33_product_upper
  have hD : (130673980547 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 800 : ℝ) - (17 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell33_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell33_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 800 : ℝ) - (17 / 1600 : ℝ)) ≤
      (1 / (130673980547 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (130673980547 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 1600 : ℝ) - Real.pi * Real.exp (33 / 800 : ℝ)) ≤
      (2 / (130673980547 / 5000000000 : ℝ) : ℝ) := by
    rw [show (17 / 1600 : ℝ) - Real.pi * Real.exp (33 / 800 : ℝ) =
      -(Real.pi * Real.exp (33 / 800 : ℝ) - (17 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8194971447184613 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8194971447184613 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell33_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 1600 : ℝ) (17 / 800 : ℝ)) :
    (553092887 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2235936729 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell33_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell33_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell34_leftExp :
    (10434160563 / 10000000000 : ℝ) ≤ Real.exp (17 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 400 : ℝ) (250332251837 / 250000000000 : ℝ)
    (10434160563 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell34_rightExp :
    Real.exp (7 / 160 : ℝ) ≤ (522360571 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 160 : ℝ) (1001368122527 / 1000000000000 : ℝ)
    (522360571 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell34_denomUpper :
    Real.exp (1635731813329603 / 500000000000000 : ℝ) ≤ (10539951007 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1635731813329603 / 500000000000000 : ℝ) (1107641786127 /
    1000000000000 : ℝ) (10539951007 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell34_denomLower :
    (65584590471 / 2500000000 : ℝ) ≤ Real.exp (4083812543929537 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4083812543929537 / 1250000000000000 : ℝ) (1107489025461
    / 1000000000000 : ℝ) (65584590471 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell34_product_lower :
    (4097484418929537 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell34_leftExp
    (by norm_num : (0 : ℝ) ≤ (10434160563 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell34_product_upper :
    Real.pi * Real.exp (7 / 160 : ℝ) ≤ (1641044313329603 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell34_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell34_endpointLower :
    (8847435399 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 800 : ℝ) (7 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4097484418929537 / 1250000000000000 : ℝ) (Real.pi * Real.exp (17 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell34_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 160 : ℝ) - (17 / 1600 : ℝ)) ≤
      (10539951007 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell34_denomUpper
    linarith [hpThetaJensenCell34_product_upper]
  have hi : (1 / (10539951007 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 160 : ℝ) - (17 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10539951007 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10539951007 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 1600 : ℝ) - Real.pi * Real.exp (7 / 160 : ℝ)) := by
    rw [show (17 / 1600 : ℝ) - Real.pi * Real.exp (7 / 160 : ℝ) =
      -(Real.pi * Real.exp (7 / 160 : ℝ) - (17 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 400 : ℝ)) := by
    have h := hpThetaJensenCell34_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10539951007 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell34_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 800 : ℝ) (7 / 320 : ℝ) ≤ (17883396711 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 160 : ℝ)) (1641044313329603 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell34_product_upper
  have hD : (65584590471 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 400 : ℝ) - (7 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell34_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell34_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 400 : ℝ) - (7 / 640 : ℝ)) ≤
      (1 / (65584590471 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (65584590471 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 640 : ℝ) - Real.pi * Real.exp (17 / 400 : ℝ)) ≤
      (2 / (65584590471 / 2500000000 : ℝ) : ℝ) := by
    rw [show (7 / 640 : ℝ) - Real.pi * Real.exp (17 / 400 : ℝ) =
      -(Real.pi * Real.exp (17 / 400 : ℝ) - (7 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1641044313329603 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1641044313329603 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell34_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 800 : ℝ) (7 / 320 : ℝ)) :
    (8847435399 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17883396711 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell34_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell34_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell35_leftExp :
    (10447211419 / 10000000000 : ℝ) ≤ Real.exp (7 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 160 : ℝ) (500684061263 / 500000000000 : ℝ)
    (10447211419 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell35_rightExp :
    Real.exp (9 / 200 : ℝ) ≤ (52301393 / 50000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 200 : ℝ) (500703619617 / 500000000000 : ℝ)
    (52301393 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell35_denomUpper :
    Real.exp (163762815139049 / 50000000000000 : ℝ) ≤ (52900007643 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (163762815139049 / 50000000000000 : ℝ) (1107773072861 /
    1000000000000 : ℝ) (52900007643 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell35_denomLower :
    (263333864687 / 10000000000 : ℝ) ≤ Real.exp (4088546977029881 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4088546977029881 / 1250000000000000 : ℝ) (138452514567 /
    125000000000 : ℝ) (263333864687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell35_product_lower :
    (4102609477029881 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell35_leftExp
    (by norm_num : (0 : ℝ) ≤ (10447211419 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell35_product_upper :
    Real.pi * Real.exp (9 / 200 : ℝ) ≤ (164309690139049 / 50000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell35_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell35_endpointLower :
    (17690636449 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 320 : ℝ) (9 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4102609477029881 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell35_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 200 : ℝ) - (7 / 640 : ℝ)) ≤
      (52900007643 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell35_denomUpper
    linarith [hpThetaJensenCell35_product_upper]
  have hi : (1 / (52900007643 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 200 : ℝ) - (7 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (52900007643 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (52900007643 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 640 : ℝ) - Real.pi * Real.exp (9 / 200 : ℝ)) := by
    rw [show (7 / 640 : ℝ) - Real.pi * Real.exp (9 / 200 : ℝ) =
      -(Real.pi * Real.exp (9 / 200 : ℝ) - (7 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 160 : ℝ)) := by
    have h := hpThetaJensenCell35_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (52900007643 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell35_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 320 : ℝ) (9 / 400 : ℝ) ≤ (3575833129 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 200 : ℝ)) (164309690139049 / 50000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell35_product_upper
  have hD : (263333864687 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 160 : ℝ) - (9 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell35_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell35_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 160 : ℝ) - (9 / 800 : ℝ)) ≤
      (1 / (263333864687 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (263333864687 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 800 : ℝ) - Real.pi * Real.exp (7 / 160 : ℝ)) ≤
      (2 / (263333864687 / 10000000000 : ℝ) : ℝ) := by
    rw [show (9 / 800 : ℝ) - Real.pi * Real.exp (7 / 160 : ℝ) =
      -(Real.pi * Real.exp (7 / 160 : ℝ) - (9 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (164309690139049 / 50000000000000 : ℝ) ^ 2 - 6 *
      (164309690139049 / 50000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell35_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 320 : ℝ) (9 / 400 : ℝ)) :
    (17690636449 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3575833129 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell35_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell35_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell36_leftExp :
    (10460278599 / 10000000000 : ℝ) ≤ Real.exp (9 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 200 : ℝ) (1001407239233 / 1000000000000 : ℝ)
    (10460278599 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell36_rightExp :
    Real.exp (37 / 800 : ℝ) ≤ (2618340531 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 800 : ℝ) (250361589367 / 250000000000 : ℝ)
    (2618340531 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell36_denomUpper :
    Real.exp (8197635283805883 / 2500000000000000 : ℝ) ≤ (26550646921 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8197635283805883 / 2500000000000000 : ℝ) (34622017279 /
    31250000000 : ℝ) (26550646921 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell36_denomLower :
    (264334500747 / 10000000000 : ℝ) ≤ Real.exp (4093287820548701 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4093287820548701 / 1250000000000000 : ℝ) (1107751400657
    / 1000000000000 : ℝ) (264334500747 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell36_product_lower :
    (4107740945548701 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell36_leftExp
    (by norm_num : (0 : ℝ) ≤ (10460278599 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell36_product_upper :
    Real.pi * Real.exp (37 / 800 : ℝ) ≤ (8225760283805883 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell36_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell36_endpointLower :
    (17686269461 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 400 : ℝ) (37 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4107740945548701 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell36_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 800 : ℝ) - (9 / 800 : ℝ)) ≤
      (26550646921 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell36_denomUpper
    linarith [hpThetaJensenCell36_product_upper]
  have hi : (1 / (26550646921 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 800 : ℝ) - (9 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26550646921 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26550646921 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 800 : ℝ) - Real.pi * Real.exp (37 / 800 : ℝ)) := by
    rw [show (9 / 800 : ℝ) - Real.pi * Real.exp (37 / 800 : ℝ) =
      -(Real.pi * Real.exp (37 / 800 : ℝ) - (9 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 200 : ℝ)) := by
    have h := hpThetaJensenCell36_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26550646921 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell36_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 400 : ℝ) (37 / 1600 : ℝ) ≤ (446870019 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 800 : ℝ)) (8225760283805883 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell36_product_upper
  have hD : (264334500747 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 200 : ℝ) - (37 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell36_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell36_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 200 : ℝ) - (37 / 3200 : ℝ)) ≤
      (1 / (264334500747 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (264334500747 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 3200 : ℝ) - Real.pi * Real.exp (9 / 200 : ℝ)) ≤
      (2 / (264334500747 / 10000000000 : ℝ) : ℝ) := by
    rw [show (37 / 3200 : ℝ) - Real.pi * Real.exp (9 / 200 : ℝ) =
      -(Real.pi * Real.exp (9 / 200 : ℝ) - (37 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8225760283805883 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8225760283805883 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell36_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 400 : ℝ) (37 / 1600 : ℝ)) :
    (17686269461 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (446870019 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell36_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell36_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell37_leftExp :
    (5236681061 / 5000000000 : ℝ) ≤ Real.exp (37 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 800 : ℝ) (1001446357467 / 1000000000000 : ℝ)
    (5236681061 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell37_rightExp :
    Real.exp (19 / 400 : ℝ) ≤ (2621615503 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 400 : ℝ) (100148547723 / 100000000000 : ℝ)
    (2621615503 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell37_denomUpper :
    Real.exp (8207142662916279 / 2500000000000000 : ℝ) ≤ (266518099849 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8207142662916279 / 2500000000000000 : ℝ) (110803622661 /
    100000000000 : ℝ) (266518099849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell37_denomLower :
    (414594221 / 15625000 : ℝ) ≤ Real.exp (2049017540973639 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2049017540973639 / 625000000000000 : ℝ) (69242679881 /
    62500000000 : ℝ) (414594221 / 15625000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell37_product_lower :
    (2056439415973639 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell37_leftExp
    (by norm_num : (0 : ℝ) ≤ (5236681061 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell37_product_upper :
    Real.pi * Real.exp (19 / 400 : ℝ) ≤ (8236048912916279 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell37_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell37_endpointLower :
    (442044249 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 1600 : ℝ) (19 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2056439415973639 / 625000000000000 : ℝ) (Real.pi * Real.exp (37 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell37_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 400 : ℝ) - (37 / 3200 : ℝ)) ≤
      (266518099849 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell37_denomUpper
    linarith [hpThetaJensenCell37_product_upper]
  have hi : (1 / (266518099849 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 400 : ℝ) - (37 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (266518099849 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (266518099849 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 3200 : ℝ) - Real.pi * Real.exp (19 / 400 : ℝ)) := by
    rw [show (37 / 3200 : ℝ) - Real.pi * Real.exp (19 / 400 : ℝ) =
      -(Real.pi * Real.exp (19 / 400 : ℝ) - (37 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 800 : ℝ)) := by
    have h := hpThetaJensenCell37_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (266518099849 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell37_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 1600 : ℝ) (19 / 800 : ℝ) ≤ (17870302189 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 400 : ℝ)) (8236048912916279 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell37_product_upper
  have hD : (414594221 / 15625000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 800 : ℝ) - (19 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell37_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell37_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 800 : ℝ) - (19 / 1600 : ℝ)) ≤
      (1 / (414594221 / 15625000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (414594221 / 15625000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 1600 : ℝ) - Real.pi * Real.exp (37 / 800 : ℝ)) ≤
      (2 / (414594221 / 15625000 : ℝ) : ℝ) := by
    rw [show (19 / 1600 : ℝ) - Real.pi * Real.exp (37 / 800 : ℝ) =
      -(Real.pi * Real.exp (37 / 800 : ℝ) - (19 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8236048912916279 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8236048912916279 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell37_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 1600 : ℝ) (19 / 800 : ℝ)) :
    (442044249 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17870302189 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell37_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell37_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell38_leftExp :
    (1048646201 / 1000000000 : ℝ) ≤ Real.exp (19 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 400 : ℝ) (1001485477229 / 1000000000000 : ℝ)
    (1048646201 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell38_rightExp :
    Real.exp (39 / 800 : ℝ) ≤ (2099915657 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 800 : ℝ) (1001524598521 / 1000000000000 : ℝ)
    (2099915657 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell38_denomUpper :
    Real.exp (6573330328621601 / 2000000000000000 : ℝ) ≤ (267534962123 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6573330328621601 / 2000000000000000 : ℝ) (5540840471 /
    5000000000 : ℝ) (267534962123 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell38_denomLower :
    (133175649297 / 5000000000 : ℝ) ≤ Real.exp (410278876986499 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (410278876986499 / 125000000000000 : ℝ) (277003637289 /
    250000000000 : ℝ) (133175649297 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell38_product_lower :
    (411802314486499 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell38_leftExp
    (by norm_num : (0 : ℝ) ≤ (1048646201 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell38_product_upper :
    Real.pi * Real.exp (39 / 800 : ℝ) ≤ (6597080328621601 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell38_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell38_endpointLower :
    (8838569041 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 800 : ℝ) (39 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (411802314486499 / 125000000000000 : ℝ) (Real.pi * Real.exp (19 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell38_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 800 : ℝ) - (19 / 1600 : ℝ)) ≤
      (267534962123 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell38_denomUpper
    linarith [hpThetaJensenCell38_product_upper]
  have hi : (1 / (267534962123 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 800 : ℝ) - (19 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (267534962123 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (267534962123 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 1600 : ℝ) - Real.pi * Real.exp (39 / 800 : ℝ)) := by
    rw [show (19 / 1600 : ℝ) - Real.pi * Real.exp (39 / 800 : ℝ) =
      -(Real.pi * Real.exp (39 / 800 : ℝ) - (19 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 400 : ℝ)) := by
    have h := hpThetaJensenCell38_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (267534962123 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell38_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 800 : ℝ) (39 / 1600 : ℝ) ≤ (17865670057 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 800 : ℝ)) (6597080328621601 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell38_product_upper
  have hD : (133175649297 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 400 : ℝ) - (39 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell38_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell38_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 400 : ℝ) - (39 / 3200 : ℝ)) ≤
      (1 / (133175649297 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (133175649297 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 3200 : ℝ) - Real.pi * Real.exp (19 / 400 : ℝ)) ≤
      (2 / (133175649297 / 5000000000 : ℝ) : ℝ) := by
    rw [show (39 / 3200 : ℝ) - Real.pi * Real.exp (19 / 400 : ℝ) =
      -(Real.pi * Real.exp (19 / 400 : ℝ) - (39 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6597080328621601 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (6597080328621601 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell38_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 800 : ℝ) (39 / 1600 : ℝ)) :
    (8838569041 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17865670057 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell38_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell38_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell39_leftExp :
    (2624894571 / 2500000000 : ℝ) ≤ Real.exp (39 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 800 : ℝ) (25038114963 / 25000000000 : ℝ)
    (2624894571 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell39_rightExp :
    Real.exp (1 / 20 : ℝ) ≤ (2102542193 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 20 : ℝ) (50078186067 / 50000000000 : ℝ)
    (2102542193 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell39_denomUpper :
    Real.exp (6580956835733449 / 2000000000000000 : ℝ) ≤ (268557088347 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6580956835733449 / 2000000000000000 : ℝ) (277075039001 /
    250000000000 : ℝ) (268557088347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell39_denomLower :
    (133683762099 / 5000000000 : ℝ) ≤ Real.exp (1026887223137129 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1026887223137129 / 312500000000000 : ℝ) (277036603533 /
    250000000000 : ℝ) (133683762099 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell39_product_lower :
    (1030793473137129 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell39_leftExp
    (by norm_num : (0 : ℝ) ≤ (2624894571 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell39_product_upper :
    Real.pi * Real.exp (1 / 20 : ℝ) ≤ (6605331835733449 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell39_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell39_endpointLower :
    (17672373951 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 1600 : ℝ) (1 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1030793473137129 / 312500000000000 : ℝ) (Real.pi * Real.exp (39 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell39_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 20 : ℝ) - (39 / 3200 : ℝ)) ≤
      (268557088347 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell39_denomUpper
    linarith [hpThetaJensenCell39_product_upper]
  have hi : (1 / (268557088347 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 20 : ℝ) - (39 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (268557088347 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (268557088347 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 3200 : ℝ) - Real.pi * Real.exp (1 / 20 : ℝ)) := by
    rw [show (39 / 3200 : ℝ) - Real.pi * Real.exp (1 / 20 : ℝ) =
      -(Real.pi * Real.exp (1 / 20 : ℝ) - (39 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 800 : ℝ)) := by
    have h := hpThetaJensenCell39_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (268557088347 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell39_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 1600 : ℝ) (1 / 40 : ℝ) ≤ (35721809 / 20000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 20 : ℝ)) (6605331835733449 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell39_product_upper
  have hD : (133683762099 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 800 : ℝ) - (1 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell39_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell39_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 800 : ℝ) - (1 / 80 : ℝ)) ≤
      (1 / (133683762099 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (133683762099 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 80 : ℝ) - Real.pi * Real.exp (39 / 800 : ℝ)) ≤
      (2 / (133683762099 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 80 : ℝ) - Real.pi * Real.exp (39 / 800 : ℝ) =
      -(Real.pi * Real.exp (39 / 800 : ℝ) - (1 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6605331835733449 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (6605331835733449 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell39_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 1600 : ℝ) (1 / 40 : ℝ)) :
    (17672373951 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (35721809 / 20000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell39_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell39_endpointUpper

def hpThetaJensenCellsBatch001Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8870078807 / 5000000000 : ℝ)
  | 1 => (443444813 / 250000000 : ℝ)
  | 2 => (17735293217 / 10000000000 : ℝ)
  | 3 => (1108291237 / 625000000 : ℝ)
  | 4 => (17729892351 / 10000000000 : ℝ)
  | 5 => (17726990999 / 10000000000 : ℝ)
  | 6 => (27693681 / 15625000 : ℝ)
  | 7 => (553774593 / 312500000 : ℝ)
  | 8 => (17717484527 / 10000000000 : ℝ)
  | 9 => (88570243 / 50000000 : ℝ)
  | 10 => (17710479297 / 10000000000 : ℝ)
  | 11 => (17706776747 / 10000000000 : ℝ)
  | 12 => (1770294107 / 1000000000 : ℝ)
  | 13 => (553092887 / 312500000 : ℝ)
  | 14 => (8847435399 / 5000000000 : ℝ)
  | 15 => (17690636449 / 10000000000 : ℝ)
  | 16 => (17686269461 / 10000000000 : ℝ)
  | 17 => (442044249 / 250000000 : ℝ)
  | 18 => (8838569041 / 5000000000 : ℝ)
  | 19 => (17672373951 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch001Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17928514273 / 10000000000 : ℝ)
  | 1 => (17926168889 / 10000000000 : ℝ)
  | 2 => (4480922029 / 2500000000 : ℝ)
  | 3 => (896053603 / 500000000 : ℝ)
  | 4 => (17918320817 / 10000000000 : ℝ)
  | 5 => (1791543449 / 1000000000 : ℝ)
  | 6 => (17912413183 / 10000000000 : ℝ)
  | 7 => (17909257007 / 10000000000 : ℝ)
  | 8 => (895298303 / 500000000 : ℝ)
  | 9 => (17902540459 / 10000000000 : ℝ)
  | 10 => (17898980327 / 10000000000 : ℝ)
  | 11 => (17895285769 / 10000000000 : ℝ)
  | 12 => (3578291379 / 2000000000 : ℝ)
  | 13 => (2235936729 / 1250000000 : ℝ)
  | 14 => (17883396711 / 10000000000 : ℝ)
  | 15 => (3575833129 / 2000000000 : ℝ)
  | 16 => (446870019 / 250000000 : ℝ)
  | 17 => (17870302189 / 10000000000 : ℝ)
  | 18 => (17865670057 / 10000000000 : ℝ)
  | 19 => (35721809 / 20000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch001_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch001Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch001Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell20_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell21_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell22_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell23_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell24_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell25_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell26_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell27_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell28_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell29_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell30_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell31_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell32_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell33_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell34_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell35_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell36_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell37_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell38_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell39_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper] at h ⊢
    exact h

end HodgeProofHP
