import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell640_leftExp :
    (5563852321 / 2500000000 : ℝ) ≤ Real.exp (4 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4 / 5 : ℝ) (256328780131 / 250000000000 : ℝ) (5563852321
    / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell640_rightExp :
    Real.exp (641 / 800 : ℝ) ≤ (11141622971 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (641 / 800 : ℝ) (1025355172679 / 1000000000000 : ℝ)
    (11141622971 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell640_denomUpper :
    Real.exp (34002444734332803 / 5000000000000000 : ℝ) ≤ (2245715996571 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34002444734332803 / 5000000000000000 : ℝ) (1236785010989
    / 1000000000000 : ℝ) (2245715996571 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell640_denomLower :
    (2225461988233 / 2500000000 : ℝ) ≤ Real.exp (2122321586354379 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2122321586354379 / 312500000000000 : ℝ) (772771813 /
    625000000 : ℝ) (2225461988233 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell640_product_lower :
    (2184919242604379 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (4 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell640_leftExp
    (by norm_num : (0 : ℝ) ≤ (5563852321 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell640_product_upper :
    Real.pi * Real.exp (641 / 800 : ℝ) ≤ (35002444734332803 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell640_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell640_endpointLower :
    (3419563111 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (2 / 5 : ℝ) (641 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2184919242604379 / 312500000000000 : ℝ) (Real.pi * Real.exp (4 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell640_product_lower
  have hD : Real.exp (Real.pi * Real.exp (641 / 800 : ℝ) - (1 / 5 : ℝ)) ≤
      (2245715996571 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell640_denomUpper
    linarith [hpThetaJensenCell640_product_upper]
  have hi : (1 / (2245715996571 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (641 / 800 : ℝ) - (1 / 5 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2245715996571 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2245715996571 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 5 : ℝ) - Real.pi * Real.exp (641 / 800 : ℝ)) := by
    rw [show (1 / 5 : ℝ) - Real.pi * Real.exp (641 / 800 : ℝ) =
      -(Real.pi * Real.exp (641 / 800 : ℝ) - (1 / 5 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (4 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (4 / 5 : ℝ)) := by
    have h := hpThetaJensenCell640_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2245715996571 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell640_endpointUpper :
    hpThetaJensenKernelEndpointUpper (2 / 5 : ℝ) (641 / 1600 : ℝ) ≤ (3469618373 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (641 / 800 : ℝ)) (35002444734332803 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (641 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell640_product_upper
  have hD : (2225461988233 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (4 / 5 : ℝ) - (641 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell640_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell640_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (4 / 5 : ℝ) - (641 / 3200 : ℝ)) ≤
      (1 / (2225461988233 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2225461988233 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((641 / 3200 : ℝ) - Real.pi * Real.exp (4 / 5 : ℝ)) ≤
      (2 / (2225461988233 / 2500000000 : ℝ) : ℝ) := by
    rw [show (641 / 3200 : ℝ) - Real.pi * Real.exp (4 / 5 : ℝ) =
      -(Real.pi * Real.exp (4 / 5 : ℝ) - (641 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35002444734332803 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (35002444734332803 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell640_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (2 / 5 : ℝ) (641 / 1600 : ℝ)) :
    (3419563111 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3469618373 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell640_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell640_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell641_leftExp :
    (1114162297 / 500000000 : ℝ) ≤ Real.exp (641 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (641 / 800 : ℝ) (512677586339 / 500000000000 : ℝ)
    (1114162297 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell641_rightExp :
    Real.exp (321 / 400 : ℝ) ≤ (4462223483 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (321 / 400 : ℝ) (512697613199 / 500000000000 : ℝ)
    (4462223483 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell641_denomUpper :
    Real.exp (13617865058628419 / 2000000000000000 : ℝ) ≤ (566189540919 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13617865058628419 / 2000000000000000 : ℝ) (618555697277
    / 500000000000 : ℝ) (566189540919 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell641_denomLower :
    (8977231440229 / 10000000000 : ℝ) ≤ Real.exp (424991357369603 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (424991357369603 / 62500000000000 : ℝ) (7729754807 /
    6250000000 : ℝ) (8977231440229 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell641_product_lower :
    (437530419869603 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (641 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell641_leftExp
    (by norm_num : (0 : ℝ) ≤ (1114162297 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell641_product_upper :
    Real.pi * Real.exp (321 / 400 : ℝ) ≤ (14018490058628419 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell641_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell641_endpointLower :
    (1700229403 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (641 / 1600 : ℝ) (321 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (437530419869603 / 62500000000000 : ℝ) (Real.pi * Real.exp (641 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell641_product_lower
  have hD : Real.exp (Real.pi * Real.exp (321 / 400 : ℝ) - (641 / 3200 : ℝ)) ≤
      (566189540919 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell641_denomUpper
    linarith [hpThetaJensenCell641_product_upper]
  have hi : (1 / (566189540919 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (321 / 400 : ℝ) - (641 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (566189540919 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (566189540919 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((641 / 3200 : ℝ) - Real.pi * Real.exp (321 / 400 : ℝ)) := by
    rw [show (641 / 3200 : ℝ) - Real.pi * Real.exp (321 / 400 : ℝ) =
      -(Real.pi * Real.exp (321 / 400 : ℝ) - (641 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (641 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (641 / 800 : ℝ)) := by
    have h := hpThetaJensenCell641_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (566189540919 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell641_endpointUpper :
    hpThetaJensenKernelEndpointUpper (641 / 1600 : ℝ) (321 / 800 : ℝ) ≤ (3450270297 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (321 / 400 : ℝ)) (14018490058628419 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (321 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell641_product_upper
  have hD : (8977231440229 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (641 / 800 : ℝ) - (321 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell641_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell641_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (641 / 800 : ℝ) - (321 / 1600 : ℝ)) ≤
      (1 / (8977231440229 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8977231440229 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((321 / 1600 : ℝ) - Real.pi * Real.exp (641 / 800 : ℝ)) ≤
      (2 / (8977231440229 / 10000000000 : ℝ) : ℝ) := by
    rw [show (321 / 1600 : ℝ) - Real.pi * Real.exp (641 / 800 : ℝ) =
      -(Real.pi * Real.exp (641 / 800 : ℝ) - (321 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14018490058628419 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (14018490058628419 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell641_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (641 / 1600 : ℝ) (321 / 800 : ℝ)) :
    (1700229403 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3450270297 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell641_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell641_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell642_leftExp :
    (11155558707 / 5000000000 : ℝ) ≤ Real.exp (321 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (321 / 400 : ℝ) (1025395226397 / 1000000000000 : ℝ)
    (11155558707 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell642_rightExp :
    Real.exp (643 / 800 : ℝ) ≤ (17871219 / 8000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (643 / 800 : ℝ) (1025435281681 / 1000000000000 : ℝ)
    (17871219 / 8000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell642_denomUpper :
    Real.exp (54539096511867 / 8000000000000 : ℝ) ≤ (9135947240699 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (54539096511867 / 8000000000000 : ℝ) (309359571943 /
    250000000000 : ℝ) (9135947240699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell642_denomLower :
    (9053352326033 / 10000000000 : ℝ) ≤ Real.exp (4255190811180193 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4255190811180193 / 625000000000000 : ℝ) (77317946637 /
    62500000000 : ℝ) (9053352326033 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell642_product_lower :
    (4380776748680193 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (321 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell642_leftExp
    (by norm_num : (0 : ℝ) ≤ (11155558707 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell642_product_upper :
    Real.pi * Real.exp (643 / 800 : ℝ) ≤ (56144096511867 / 8000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell642_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell642_endpointLower :
    (845355591 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (321 / 800 : ℝ) (643 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4380776748680193 / 625000000000000 : ℝ) (Real.pi * Real.exp (321 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell642_product_lower
  have hD : Real.exp (Real.pi * Real.exp (643 / 800 : ℝ) - (321 / 1600 : ℝ)) ≤
      (9135947240699 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell642_denomUpper
    linarith [hpThetaJensenCell642_product_upper]
  have hi : (1 / (9135947240699 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (643 / 800 : ℝ) - (321 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9135947240699 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9135947240699 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((321 / 1600 : ℝ) - Real.pi * Real.exp (643 / 800 : ℝ)) := by
    rw [show (321 / 1600 : ℝ) - Real.pi * Real.exp (643 / 800 : ℝ) =
      -(Real.pi * Real.exp (643 / 800 : ℝ) - (321 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (321 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (321 / 400 : ℝ)) := by
    have h := hpThetaJensenCell642_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9135947240699 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell642_endpointUpper :
    hpThetaJensenKernelEndpointUpper (321 / 800 : ℝ) (643 / 1600 : ℝ) ≤ (3430990729 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (643 / 800 : ℝ)) (56144096511867 / 8000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (643 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell642_product_upper
  have hD : (9053352326033 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (321 / 400 : ℝ) - (643 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell642_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell642_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (321 / 400 : ℝ) - (643 / 3200 : ℝ)) ≤
      (1 / (9053352326033 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9053352326033 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((643 / 3200 : ℝ) - Real.pi * Real.exp (321 / 400 : ℝ)) ≤
      (2 / (9053352326033 / 10000000000 : ℝ) : ℝ) := by
    rw [show (643 / 3200 : ℝ) - Real.pi * Real.exp (321 / 400 : ℝ) =
      -(Real.pi * Real.exp (321 / 400 : ℝ) - (643 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56144096511867 / 8000000000000 : ℝ) ^ 2 - 6 *
      (56144096511867 / 8000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell642_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (321 / 800 : ℝ) (643 / 1600 : ℝ)) :
    (845355591 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3430990729 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell642_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell642_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell643_leftExp :
    (5584755937 / 2500000000 : ℝ) ≤ Real.exp (643 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (643 / 800 : ℝ) (12817941021 / 12500000000 : ℝ)
    (5584755937 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell643_rightExp :
    Real.exp (161 / 200 : ℝ) ≤ (22366964989 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (161 / 200 : ℝ) (1025475338529 / 1000000000000 : ℝ)
    (22366964989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell643_denomUpper :
    Real.exp (68258525640687477 / 10000000000000000 : ℝ) ≤ (575850993183 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (68258525640687477 / 10000000000000000 : ℝ) (154720711439
    / 125000000000 : ℝ) (575850993183 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell643_denomLower :
    (9130218655659 / 10000000000 : ℝ) ≤ Real.exp (2130237446703963 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2130237446703963 / 312500000000000 : ℝ) (1237414032883 /
    1000000000000 : ℝ) (9130218655659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell643_product_lower :
    (2193128071703963 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (643 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell643_leftExp
    (by norm_num : (0 : ℝ) ≤ (5584755937 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell643_product_upper :
    Real.pi * Real.exp (161 / 200 : ℝ) ≤ (70267900640687477 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell643_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell643_endpointLower :
    (3362453801 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (643 / 1600 : ℝ) (161 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2193128071703963 / 312500000000000 : ℝ) (Real.pi * Real.exp (643 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell643_product_lower
  have hD : Real.exp (Real.pi * Real.exp (161 / 200 : ℝ) - (643 / 3200 : ℝ)) ≤
      (575850993183 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell643_denomUpper
    linarith [hpThetaJensenCell643_product_upper]
  have hi : (1 / (575850993183 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (161 / 200 : ℝ) - (643 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (575850993183 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (575850993183 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((643 / 3200 : ℝ) - Real.pi * Real.exp (161 / 200 : ℝ)) := by
    rw [show (643 / 3200 : ℝ) - Real.pi * Real.exp (161 / 200 : ℝ) =
      -(Real.pi * Real.exp (161 / 200 : ℝ) - (643 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (643 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (643 / 800 : ℝ)) := by
    have h := hpThetaJensenCell643_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (575850993183 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell643_endpointUpper :
    hpThetaJensenKernelEndpointUpper (643 / 1600 : ℝ) (161 / 400 : ℝ) ≤ (3411779683 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (161 / 200 : ℝ)) (70267900640687477 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (161 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell643_product_upper
  have hD : (9130218655659 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (643 / 800 : ℝ) - (161 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell643_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell643_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (643 / 800 : ℝ) - (161 / 800 : ℝ)) ≤
      (1 / (9130218655659 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9130218655659 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((161 / 800 : ℝ) - Real.pi * Real.exp (643 / 800 : ℝ)) ≤
      (2 / (9130218655659 / 10000000000 : ℝ) : ℝ) := by
    rw [show (161 / 800 : ℝ) - Real.pi * Real.exp (643 / 800 : ℝ) =
      -(Real.pi * Real.exp (643 / 800 : ℝ) - (161 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70267900640687477 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (70267900640687477 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell643_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (643 / 1600 : ℝ) (161 / 400 : ℝ)) :
    (3362453801 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3411779683 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell643_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell643_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell644_leftExp :
    (22366964987 / 10000000000 : ℝ) ≤ Real.exp (161 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (161 / 200 : ℝ) (32046104329 / 31250000000 : ℝ)
    (22366964987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell644_rightExp :
    Real.exp (129 / 160 : ℝ) ≤ (22394941177 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (129 / 160 : ℝ) (512757698471 / 500000000000 : ℝ)
    (22394941177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell644_denomUpper :
    Real.exp (68343290437074961 / 10000000000000000 : ℝ) ≤ (9292046858099 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (68343290437074961 / 10000000000000000 : ℝ)
    (1238093606681 / 1000000000000 : ℝ) (9292046858099 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell644_denomLower :
    (184156771577 / 200000000 : ℝ) ≤ Real.exp (8531531658429913 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8531531658429913 / 1250000000000000 : ℝ) (1237741430097
    / 1000000000000 : ℝ) (184156771577 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell644_product_lower :
    (8783484783429913 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (161 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell644_leftExp
    (by norm_num : (0 : ℝ) ≤ (22366964987 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell644_product_upper :
    Real.pi * Real.exp (129 / 160 : ℝ) ≤ (70355790437074961 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell644_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell644_endpointLower :
    (3343553127 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (161 / 400 : ℝ) (129 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8783484783429913 / 1250000000000000 : ℝ) (Real.pi * Real.exp (161 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell644_product_lower
  have hD : Real.exp (Real.pi * Real.exp (129 / 160 : ℝ) - (161 / 800 : ℝ)) ≤
      (9292046858099 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell644_denomUpper
    linarith [hpThetaJensenCell644_product_upper]
  have hi : (1 / (9292046858099 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (129 / 160 : ℝ) - (161 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9292046858099 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9292046858099 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((161 / 800 : ℝ) - Real.pi * Real.exp (129 / 160 : ℝ)) := by
    rw [show (161 / 800 : ℝ) - Real.pi * Real.exp (129 / 160 : ℝ) =
      -(Real.pi * Real.exp (129 / 160 : ℝ) - (161 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (161 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (161 / 200 : ℝ)) := by
    have h := hpThetaJensenCell644_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9292046858099 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell644_endpointUpper :
    hpThetaJensenKernelEndpointUpper (161 / 400 : ℝ) (129 / 320 : ℝ) ≤ (1696318587 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (129 / 160 : ℝ)) (70355790437074961 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (129 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell644_product_upper
  have hD : (184156771577 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (161 / 200 : ℝ) - (129 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell644_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell644_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (161 / 200 : ℝ) - (129 / 640 : ℝ)) ≤
      (1 / (184156771577 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (184156771577 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((129 / 640 : ℝ) - Real.pi * Real.exp (161 / 200 : ℝ)) ≤
      (2 / (184156771577 / 200000000 : ℝ) : ℝ) := by
    rw [show (129 / 640 : ℝ) - Real.pi * Real.exp (161 / 200 : ℝ) =
      -(Real.pi * Real.exp (161 / 200 : ℝ) - (129 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70355790437074961 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (70355790437074961 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell644_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (161 / 400 : ℝ) (129 / 320 : ℝ)) :
    (3343553127 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1696318587 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell644_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell644_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell645_leftExp :
    (895797647 / 400000000 : ℝ) ≤ Real.exp (129 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (129 / 160 : ℝ) (1025515396941 / 1000000000000 : ℝ)
    (895797647 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell645_rightExp :
    Real.exp (323 / 400 : ℝ) ≤ (22422952357 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (323 / 400 : ℝ) (25638886423 / 25000000000 : ℝ)
    (22422952357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell645_denomUpper :
    Real.exp (68428165164084701 / 10000000000000000 : ℝ) ≤ (585703030473 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (68428165164084701 / 10000000000000000 : ℝ) (619211017081
    / 500000000000 : ℝ) (585703030473 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell645_denomLower :
    (4643110170401 / 5000000000 : ℝ) ≤ Real.exp (341685090179253 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (341685090179253 / 50000000000000 : ℝ) (1238069338731 /
    1000000000000 : ℝ) (4643110170401 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell645_product_lower :
    (351778840179253 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (129 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell645_leftExp
    (by norm_num : (0 : ℝ) ≤ (895797647 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell645_product_upper :
    Real.pi * Real.exp (323 / 400 : ℝ) ≤ (70443790164084701 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell645_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell645_endpointLower :
    (664944071 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (129 / 320 : ℝ) (323 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (351778840179253 / 50000000000000 : ℝ) (Real.pi * Real.exp (129 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell645_product_lower
  have hD : Real.exp (Real.pi * Real.exp (323 / 400 : ℝ) - (129 / 640 : ℝ)) ≤
      (585703030473 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell645_denomUpper
    linarith [hpThetaJensenCell645_product_upper]
  have hi : (1 / (585703030473 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (323 / 400 : ℝ) - (129 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (585703030473 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (585703030473 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((129 / 640 : ℝ) - Real.pi * Real.exp (323 / 400 : ℝ)) := by
    rw [show (129 / 640 : ℝ) - Real.pi * Real.exp (323 / 400 : ℝ) =
      -(Real.pi * Real.exp (323 / 400 : ℝ) - (129 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (129 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (129 / 160 : ℝ)) := by
    have h := hpThetaJensenCell645_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (585703030473 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell645_endpointUpper :
    hpThetaJensenKernelEndpointUpper (129 / 320 : ℝ) (323 / 800 : ℝ) ≤ (3373563211 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (323 / 400 : ℝ)) (70443790164084701 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (323 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell645_product_upper
  have hD : (4643110170401 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (129 / 160 : ℝ) - (323 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell645_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell645_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (129 / 160 : ℝ) - (323 / 1600 : ℝ)) ≤
      (1 / (4643110170401 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4643110170401 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((323 / 1600 : ℝ) - Real.pi * Real.exp (129 / 160 : ℝ)) ≤
      (2 / (4643110170401 / 5000000000 : ℝ) : ℝ) := by
    rw [show (323 / 1600 : ℝ) - Real.pi * Real.exp (129 / 160 : ℝ) =
      -(Real.pi * Real.exp (129 / 160 : ℝ) - (323 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70443790164084701 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (70443790164084701 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell645_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (129 / 320 : ℝ) (323 / 800 : ℝ)) :
    (664944071 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3373563211 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell645_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell645_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell646_leftExp :
    (4484590471 / 2000000000 : ℝ) ≤ Real.exp (323 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (323 / 400 : ℝ) (1025555456919 / 1000000000000 : ℝ)
    (4484590471 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell646_rightExp :
    Real.exp (647 / 800 : ℝ) ≤ (5612749643 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (647 / 800 : ℝ) (512797759231 / 500000000000 : ℝ)
    (5612749643 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell646_denomUpper :
    Real.exp (17128287489201299 / 2500000000000000 : ℝ) ≤ (4725614612231 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17128287489201299 / 2500000000000000 : ℝ) (1238750974839
    / 1000000000000 : ℝ) (4725614612231 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell646_denomLower :
    (4682686140457 / 5000000000 : ℝ) ≤ Real.exp (1710547318371229 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1710547318371229 / 250000000000000 : ℝ) (247679551933 /
    200000000000 : ℝ) (4682686140457 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell646_product_lower :
    (1761094193371229 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (323 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell646_leftExp
    (by norm_num : (0 : ℝ) ≤ (4484590471 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell646_product_upper :
    Real.pi * Real.exp (647 / 800 : ℝ) ≤ (17632974989201299 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell646_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell646_endpointLower :
    (3305955493 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (323 / 800 : ℝ) (647 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1761094193371229 / 250000000000000 : ℝ) (Real.pi * Real.exp (323 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell646_product_lower
  have hD : Real.exp (Real.pi * Real.exp (647 / 800 : ℝ) - (323 / 1600 : ℝ)) ≤
      (4725614612231 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell646_denomUpper
    linarith [hpThetaJensenCell646_product_upper]
  have hi : (1 / (4725614612231 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (647 / 800 : ℝ) - (323 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4725614612231 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4725614612231 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((323 / 1600 : ℝ) - Real.pi * Real.exp (647 / 800 : ℝ)) := by
    rw [show (323 / 1600 : ℝ) - Real.pi * Real.exp (647 / 800 : ℝ) =
      -(Real.pi * Real.exp (647 / 800 : ℝ) - (323 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (323 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (323 / 400 : ℝ)) := by
    have h := hpThetaJensenCell646_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4725614612231 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell646_endpointUpper :
    hpThetaJensenKernelEndpointUpper (323 / 800 : ℝ) (647 / 1600 : ℝ) ≤ (3354557807 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (647 / 800 : ℝ)) (17632974989201299 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (647 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell646_product_upper
  have hD : (4682686140457 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (323 / 400 : ℝ) - (647 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell646_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell646_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (323 / 400 : ℝ) - (647 / 3200 : ℝ)) ≤
      (1 / (4682686140457 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4682686140457 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((647 / 3200 : ℝ) - Real.pi * Real.exp (323 / 400 : ℝ)) ≤
      (2 / (4682686140457 / 5000000000 : ℝ) : ℝ) := by
    rw [show (647 / 3200 : ℝ) - Real.pi * Real.exp (323 / 400 : ℝ) =
      -(Real.pi * Real.exp (323 / 400 : ℝ) - (647 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17632974989201299 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (17632974989201299 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell646_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (323 / 800 : ℝ) (647 / 1600 : ℝ)) :
    (3305955493 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3354557807 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell646_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell646_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell647_leftExp :
    (2245099857 / 1000000000 : ℝ) ≤ Real.exp (647 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (647 / 800 : ℝ) (1025595518461 / 1000000000000 : ℝ)
    (2245099857 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell647_rightExp :
    Real.exp (81 / 100 : ℝ) ≤ (5619769967 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81 / 100 : ℝ) (102563558157 / 100000000000 : ℝ)
    (5619769967 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell647_denomUpper :
    Real.exp (17149561239937431 / 2500000000000000 : ℝ) ≤ (1861718286 / 1953125 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17149561239937431 / 2500000000000000 : ℝ) (247816085927
    / 200000000000 : ℝ) (1861718286 / 1953125 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell647_denomLower :
    (9445302839981 / 10000000000 : ℝ) ≤ Real.exp (856335968744043 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (856335968744043 / 125000000000000 : ℝ) (1238726693787 /
    1000000000000 : ℝ) (9445302839981 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell647_product_lower :
    (881648468744043 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (647 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell647_leftExp
    (by norm_num : (0 : ℝ) ≤ (2245099857 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell647_product_upper :
    Real.pi * Real.exp (81 / 100 : ℝ) ≤ (17655029989937431 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell647_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell647_endpointLower :
    (657451709 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (647 / 1600 : ℝ) (81 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (881648468744043 / 125000000000000 : ℝ) (Real.pi * Real.exp (647 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell647_product_lower
  have hD : Real.exp (Real.pi * Real.exp (81 / 100 : ℝ) - (647 / 3200 : ℝ)) ≤
      (1861718286 / 1953125 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell647_denomUpper
    linarith [hpThetaJensenCell647_product_upper]
  have hi : (1 / (1861718286 / 1953125 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (81 / 100 : ℝ) - (647 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1861718286 / 1953125 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1861718286 / 1953125 : ℝ) : ℝ) ≤
      2 * Real.exp ((647 / 3200 : ℝ) - Real.pi * Real.exp (81 / 100 : ℝ)) := by
    rw [show (647 / 3200 : ℝ) - Real.pi * Real.exp (81 / 100 : ℝ) =
      -(Real.pi * Real.exp (81 / 100 : ℝ) - (647 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (647 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (647 / 800 : ℝ)) := by
    have h := hpThetaJensenCell647_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1861718286 / 1953125 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell647_endpointUpper :
    hpThetaJensenKernelEndpointUpper (647 / 1600 : ℝ) (81 / 200 : ℝ) ≤ (333562097 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (81 / 100 : ℝ)) (17655029989937431 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (81 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell647_product_upper
  have hD : (9445302839981 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (647 / 800 : ℝ) - (81 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell647_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell647_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (647 / 800 : ℝ) - (81 / 400 : ℝ)) ≤
      (1 / (9445302839981 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9445302839981 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((81 / 400 : ℝ) - Real.pi * Real.exp (647 / 800 : ℝ)) ≤
      (2 / (9445302839981 / 10000000000 : ℝ) : ℝ) := by
    rw [show (81 / 400 : ℝ) - Real.pi * Real.exp (647 / 800 : ℝ) =
      -(Real.pi * Real.exp (647 / 800 : ℝ) - (81 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17655029989937431 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (17655029989937431 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell647_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (647 / 1600 : ℝ) (81 / 200 : ℝ)) :
    (657451709 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (333562097 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell647_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell647_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell648_leftExp :
    (11239539933 / 5000000000 : ℝ) ≤ Real.exp (81 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (81 / 100 : ℝ) (1025635581569 / 1000000000000 : ℝ)
    (11239539933 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell648_rightExp :
    Real.exp (649 / 800 : ℝ) ≤ (22507196287 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (649 / 800 : ℝ) (512837823121 / 500000000000 : ℝ)
    (22507196287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell648_denomUpper :
    Real.exp (68683450304865191 / 10000000000000000 : ℝ) ≤ (4806781166471 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (68683450304865191 / 10000000000000000 : ℝ) (19365787491
    / 15625000000 : ℝ) (4806781166471 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell648_denomLower :
    (1905204113441 / 2000000000 : ℝ) ≤ Real.exp (4286998279649167 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4286998279649167 / 625000000000000 : ℝ) (19360252219 /
    15625000000 : ℝ) (1905204113441 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell648_product_lower :
    (4413756092149167 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (81 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell648_leftExp
    (by norm_num : (0 : ℝ) ≤ (11239539933 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell648_product_upper :
    Real.pi * Real.exp (649 / 800 : ℝ) ≤ (70708450304865191 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell648_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell648_endpointLower :
    (40857869 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 200 : ℝ) (649 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4413756092149167 / 625000000000000 : ℝ) (Real.pi * Real.exp (81 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell648_product_lower
  have hD : Real.exp (Real.pi * Real.exp (649 / 800 : ℝ) - (81 / 400 : ℝ)) ≤
      (4806781166471 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell648_denomUpper
    linarith [hpThetaJensenCell648_product_upper]
  have hi : (1 / (4806781166471 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (649 / 800 : ℝ) - (81 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4806781166471 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4806781166471 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((81 / 400 : ℝ) - Real.pi * Real.exp (649 / 800 : ℝ)) := by
    rw [show (81 / 400 : ℝ) - Real.pi * Real.exp (649 / 800 : ℝ) =
      -(Real.pi * Real.exp (649 / 800 : ℝ) - (81 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (81 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (81 / 100 : ℝ)) := by
    have h := hpThetaJensenCell648_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4806781166471 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell648_endpointUpper :
    hpThetaJensenKernelEndpointUpper (81 / 200 : ℝ) (649 / 1600 : ℝ) ≤ (663350541 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (649 / 800 : ℝ)) (70708450304865191 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (649 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell648_product_upper
  have hD : (1905204113441 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (81 / 100 : ℝ) - (649 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell648_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell648_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (81 / 100 : ℝ) - (649 / 3200 : ℝ)) ≤
      (1 / (1905204113441 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1905204113441 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((649 / 3200 : ℝ) - Real.pi * Real.exp (81 / 100 : ℝ)) ≤
      (2 / (1905204113441 / 2000000000 : ℝ) : ℝ) := by
    rw [show (649 / 3200 : ℝ) - Real.pi * Real.exp (81 / 100 : ℝ) =
      -(Real.pi * Real.exp (81 / 100 : ℝ) - (649 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70708450304865191 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (70708450304865191 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell648_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (81 / 200 : ℝ) (649 / 1600 : ℝ)) :
    (40857869 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (663350541 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell648_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell648_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell649_leftExp :
    (4501439257 / 2000000000 : ℝ) ≤ Real.exp (649 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (649 / 800 : ℝ) (1025675646241 / 1000000000000 : ℝ)
    (4501439257 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell649_rightExp :
    Real.exp (13 / 16 : ℝ) ≤ (22535347873 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 16 : ℝ) (1025715712479 / 1000000000000 : ℝ)
    (22535347873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell649_denomUpper :
    Real.exp (68768766130381689 / 10000000000000000 : ℝ) ≤ (1211991513277 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (68768766130381689 / 10000000000000000 : ℝ)
    (1239740885107 / 1000000000000 : ℝ) (1211991513277 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell649_denomLower :
    (9607534103693 / 10000000000 : ℝ) ≤ Real.exp (1716929444784643 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1716929444784643 / 250000000000000 : ℝ) (1239386105229 /
    1000000000000 : ℝ) (9607534103693 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell649_product_lower :
    (1767710694784643 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (649 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell649_leftExp
    (by norm_num : (0 : ℝ) ≤ (4501439257 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell649_product_upper :
    Real.pi * Real.exp (13 / 16 : ℝ) ≤ (70796891130381689 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell649_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell649_endpointLower :
    (3250068421 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (649 / 1600 : ℝ) (13 / 32 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1767710694784643 / 250000000000000 : ℝ) (Real.pi * Real.exp (649 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell649_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 16 : ℝ) - (649 / 3200 : ℝ)) ≤
      (1211991513277 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell649_denomUpper
    linarith [hpThetaJensenCell649_product_upper]
  have hi : (1 / (1211991513277 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 16 : ℝ) - (649 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1211991513277 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1211991513277 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((649 / 3200 : ℝ) - Real.pi * Real.exp (13 / 16 : ℝ)) := by
    rw [show (649 / 3200 : ℝ) - Real.pi * Real.exp (13 / 16 : ℝ) =
      -(Real.pi * Real.exp (13 / 16 : ℝ) - (649 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (649 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (649 / 800 : ℝ)) := by
    have h := hpThetaJensenCell649_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1211991513277 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell649_endpointUpper :
    hpThetaJensenKernelEndpointUpper (649 / 1600 : ℝ) (13 / 32 : ℝ) ≤ (3297953019 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 16 : ℝ)) (70796891130381689 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell649_product_upper
  have hD : (9607534103693 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (649 / 800 : ℝ) - (13 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell649_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell649_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (649 / 800 : ℝ) - (13 / 64 : ℝ)) ≤
      (1 / (9607534103693 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9607534103693 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 64 : ℝ) - Real.pi * Real.exp (649 / 800 : ℝ)) ≤
      (2 / (9607534103693 / 10000000000 : ℝ) : ℝ) := by
    rw [show (13 / 64 : ℝ) - Real.pi * Real.exp (649 / 800 : ℝ) =
      -(Real.pi * Real.exp (649 / 800 : ℝ) - (13 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70796891130381689 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (70796891130381689 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell649_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (649 / 1600 : ℝ) (13 / 32 : ℝ)) :
    (3250068421 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3297953019 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell649_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell649_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell650_leftExp :
    (22535347871 / 10000000000 : ℝ) ≤ Real.exp (13 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 16 : ℝ) (512857856239 / 500000000000 : ℝ)
    (22535347871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell650_rightExp :
    Real.exp (651 / 800 : ℝ) ≤ (22563534671 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (651 / 800 : ℝ) (512877890141 / 500000000000 : ℝ)
    (22563534671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell650_denomUpper :
    Real.exp (68854192577670903 / 10000000000000000 : ℝ) ≤ (48895579041 / 50000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (68854192577670903 / 10000000000000000 : ℝ) (620035943799
    / 500000000000 : ℝ) (48895579041 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell650_denomLower :
    (9689852199349 / 10000000000 : ℝ) ≤ Real.exp (8595311698593829 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8595311698593829 / 1250000000000000 : ℝ) (49588663373 /
    40000000000 : ℝ) (9689852199349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell650_product_lower :
    (8849608573593829 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell650_leftExp
    (by norm_num : (0 : ℝ) ≤ (22535347871 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell650_product_upper :
    Real.pi * Real.exp (651 / 800 : ℝ) ≤ (70885442577670903 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell650_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell650_endpointLower :
    (3231575247 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 32 : ℝ) (651 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8849608573593829 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell650_product_lower
  have hD : Real.exp (Real.pi * Real.exp (651 / 800 : ℝ) - (13 / 64 : ℝ)) ≤
      (48895579041 / 50000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell650_denomUpper
    linarith [hpThetaJensenCell650_product_upper]
  have hi : (1 / (48895579041 / 50000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (651 / 800 : ℝ) - (13 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (48895579041 / 50000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (48895579041 / 50000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 64 : ℝ) - Real.pi * Real.exp (651 / 800 : ℝ)) := by
    rw [show (13 / 64 : ℝ) - Real.pi * Real.exp (651 / 800 : ℝ) =
      -(Real.pi * Real.exp (651 / 800 : ℝ) - (13 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 16 : ℝ)) := by
    have h := hpThetaJensenCell650_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (48895579041 / 50000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell650_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 32 : ℝ) (651 / 1600 : ℝ) ≤ (1639610957 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (651 / 800 : ℝ)) (70885442577670903 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (651 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell650_product_upper
  have hD : (9689852199349 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 16 : ℝ) - (651 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell650_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell650_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 16 : ℝ) - (651 / 3200 : ℝ)) ≤
      (1 / (9689852199349 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9689852199349 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((651 / 3200 : ℝ) - Real.pi * Real.exp (13 / 16 : ℝ)) ≤
      (2 / (9689852199349 / 10000000000 : ℝ) : ℝ) := by
    rw [show (651 / 3200 : ℝ) - Real.pi * Real.exp (13 / 16 : ℝ) =
      -(Real.pi * Real.exp (13 / 16 : ℝ) - (651 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70885442577670903 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (70885442577670903 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell650_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 32 : ℝ) (651 / 1600 : ℝ)) :
    (3231575247 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1639610957 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell650_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell650_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell651_leftExp :
    (22563534669 / 10000000000 : ℝ) ≤ Real.exp (651 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (651 / 800 : ℝ) (1025755780281 / 1000000000000 : ℝ)
    (22563534669 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell651_rightExp :
    Real.exp (163 / 200 : ℝ) ≤ (903670269 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (163 / 200 : ℝ) (20515916993 / 20000000000 : ℝ)
    (903670269 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell651_denomUpper :
    Real.exp (2757589191398517 / 400000000000000 : ℝ) ≤ (308222575187 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2757589191398517 / 400000000000000 : ℝ) (620201703899 /
    500000000000 : ℝ) (308222575187 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell651_denomLower :
    (1954596742533 / 2000000000 : ℝ) ≤ Real.exp (8605990000981631 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8605990000981631 / 1250000000000000 : ℝ) (620023790109 /
    500000000000 : ℝ) (1954596742533 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell651_product_lower :
    (8860677500981631 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (651 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell651_leftExp
    (by norm_num : (0 : ℝ) ≤ (22563534669 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell651_product_upper :
    Real.pi * Real.exp (163 / 200 : ℝ) ≤ (2838964191398517 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell651_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell651_endpointLower :
    (3213149999 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (651 / 1600 : ℝ) (163 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8860677500981631 / 1250000000000000 : ℝ) (Real.pi * Real.exp (651 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell651_product_lower
  have hD : Real.exp (Real.pi * Real.exp (163 / 200 : ℝ) - (651 / 3200 : ℝ)) ≤
      (308222575187 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell651_denomUpper
    linarith [hpThetaJensenCell651_product_upper]
  have hi : (1 / (308222575187 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (163 / 200 : ℝ) - (651 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (308222575187 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (308222575187 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((651 / 3200 : ℝ) - Real.pi * Real.exp (163 / 200 : ℝ)) := by
    rw [show (651 / 3200 : ℝ) - Real.pi * Real.exp (163 / 200 : ℝ) =
      -(Real.pi * Real.exp (163 / 200 : ℝ) - (651 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (651 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (651 / 800 : ℝ)) := by
    have h := hpThetaJensenCell651_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (308222575187 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell651_endpointUpper :
    hpThetaJensenKernelEndpointUpper (651 / 1600 : ℝ) (163 / 400 : ℝ) ≤ (3260559391 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (163 / 200 : ℝ)) (2838964191398517 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (163 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell651_product_upper
  have hD : (1954596742533 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (651 / 800 : ℝ) - (163 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell651_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell651_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (651 / 800 : ℝ) - (163 / 800 : ℝ)) ≤
      (1 / (1954596742533 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1954596742533 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((163 / 800 : ℝ) - Real.pi * Real.exp (651 / 800 : ℝ)) ≤
      (2 / (1954596742533 / 2000000000 : ℝ) : ℝ) := by
    rw [show (163 / 800 : ℝ) - Real.pi * Real.exp (651 / 800 : ℝ) =
      -(Real.pi * Real.exp (651 / 800 : ℝ) - (163 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2838964191398517 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2838964191398517 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell651_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (651 / 1600 : ℝ) (163 / 400 : ℝ)) :
    (3213149999 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3260559391 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell651_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell651_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell652_leftExp :
    (22591756723 / 10000000000 : ℝ) ≤ Real.exp (163 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (163 / 200 : ℝ) (1025795849649 / 1000000000000 : ℝ)
    (22591756723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell652_rightExp :
    Real.exp (653 / 800 : ℝ) ≤ (11310007039 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (653 / 800 : ℝ) (1025835920583 / 1000000000000 : ℝ)
    (11310007039 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell652_denomUpper :
    Real.exp (34512688943673127 / 5000000000000000 : ℝ) ≤ (994796097221 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34512688943673127 / 5000000000000000 : ℝ) (6203677233 /
    5000000000 : ℝ) (994796097221 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell652_denomLower :
    (4928468802677 / 5000000000 : ℝ) ≤ Real.exp (8616682148365377 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8616682148365377 / 1250000000000000 : ℝ) (124037909381 /
    100000000000 : ℝ) (4928468802677 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell652_product_lower :
    (8871760273365377 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (163 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell652_leftExp
    (by norm_num : (0 : ℝ) ≤ (22591756723 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell652_product_upper :
    Real.pi * Real.exp (653 / 800 : ℝ) ≤ (35531438943673127 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell652_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell652_endpointLower :
    (1597396339 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (163 / 400 : ℝ) (653 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8871760273365377 / 1250000000000000 : ℝ) (Real.pi * Real.exp (163 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell652_product_lower
  have hD : Real.exp (Real.pi * Real.exp (653 / 800 : ℝ) - (163 / 800 : ℝ)) ≤
      (994796097221 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell652_denomUpper
    linarith [hpThetaJensenCell652_product_upper]
  have hi : (1 / (994796097221 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (653 / 800 : ℝ) - (163 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (994796097221 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (994796097221 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((163 / 800 : ℝ) - Real.pi * Real.exp (653 / 800 : ℝ)) := by
    rw [show (163 / 800 : ℝ) - Real.pi * Real.exp (653 / 800 : ℝ) =
      -(Real.pi * Real.exp (653 / 800 : ℝ) - (163 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (163 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (163 / 200 : ℝ)) := by
    have h := hpThetaJensenCell652_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (994796097221 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell652_endpointUpper :
    hpThetaJensenKernelEndpointUpper (163 / 400 : ℝ) (653 / 1600 : ℝ) ≤ (3241965449 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (653 / 800 : ℝ)) (35531438943673127 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (653 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell652_product_upper
  have hD : (4928468802677 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (163 / 200 : ℝ) - (653 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell652_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell652_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (163 / 200 : ℝ) - (653 / 3200 : ℝ)) ≤
      (1 / (4928468802677 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4928468802677 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((653 / 3200 : ℝ) - Real.pi * Real.exp (163 / 200 : ℝ)) ≤
      (2 / (4928468802677 / 5000000000 : ℝ) : ℝ) := by
    rw [show (653 / 3200 : ℝ) - Real.pi * Real.exp (163 / 200 : ℝ) =
      -(Real.pi * Real.exp (163 / 200 : ℝ) - (653 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35531438943673127 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (35531438943673127 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell652_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (163 / 400 : ℝ) (653 / 1600 : ℝ)) :
    (1597396339 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3241965449 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell652_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell652_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell653_leftExp :
    (5655003519 / 2500000000 : ℝ) ≤ Real.exp (653 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (653 / 800 : ℝ) (512917960291 / 500000000000 : ℝ)
    (5655003519 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell653_rightExp :
    Real.exp (327 / 400 : ℝ) ≤ (11324153387 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (327 / 400 : ℝ) (1025875993081 / 1000000000000 : ℝ)
    (11324153387 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell653_denomUpper :
    Real.exp (34555568511525491 / 5000000000000000 : ℝ) ≤ (10033640691543 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34555568511525491 / 5000000000000000 : ℝ) (1241068004909
    / 1000000000000 : ℝ) (10033640691543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell653_denomLower :
    (621357684023 / 625000000 : ℝ) ≤ Real.exp (2156847039407781 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2156847039407781 / 312500000000000 : ℝ) (620355562997 /
    500000000000 : ℝ) (621357684023 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell653_product_lower :
    (2220714226907781 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (653 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell653_leftExp
    (by norm_num : (0 : ℝ) ≤ (5655003519 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell653_product_upper :
    Real.pi * Real.exp (327 / 400 : ℝ) ≤ (35575881011525491 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell653_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell653_endpointLower :
    (1588251639 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (653 / 1600 : ℝ) (327 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2220714226907781 / 312500000000000 : ℝ) (Real.pi * Real.exp (653 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell653_product_lower
  have hD : Real.exp (Real.pi * Real.exp (327 / 400 : ℝ) - (653 / 3200 : ℝ)) ≤
      (10033640691543 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell653_denomUpper
    linarith [hpThetaJensenCell653_product_upper]
  have hi : (1 / (10033640691543 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (327 / 400 : ℝ) - (653 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10033640691543 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10033640691543 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((653 / 3200 : ℝ) - Real.pi * Real.exp (327 / 400 : ℝ)) := by
    rw [show (653 / 3200 : ℝ) - Real.pi * Real.exp (327 / 400 : ℝ) =
      -(Real.pi * Real.exp (327 / 400 : ℝ) - (653 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (653 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (653 / 800 : ℝ)) := by
    have h := hpThetaJensenCell653_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10033640691543 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell653_endpointUpper :
    hpThetaJensenKernelEndpointUpper (653 / 1600 : ℝ) (327 / 800 : ℝ) ≤ (402930011 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (327 / 400 : ℝ)) (35575881011525491 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (327 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell653_product_upper
  have hD : (621357684023 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (653 / 800 : ℝ) - (327 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell653_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell653_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (653 / 800 : ℝ) - (327 / 1600 : ℝ)) ≤
      (1 / (621357684023 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (621357684023 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((327 / 1600 : ℝ) - Real.pi * Real.exp (653 / 800 : ℝ)) ≤
      (2 / (621357684023 / 625000000 : ℝ) : ℝ) := by
    rw [show (327 / 1600 : ℝ) - Real.pi * Real.exp (653 / 800 : ℝ) =
      -(Real.pi * Real.exp (653 / 800 : ℝ) - (327 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35575881011525491 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (35575881011525491 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell653_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (653 / 1600 : ℝ) (327 / 800 : ℝ)) :
    (1588251639 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (402930011 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell653_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell653_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell654_leftExp :
    (22648306773 / 10000000000 : ℝ) ≤ Real.exp (327 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (327 / 400 : ℝ) (25646899827 / 25000000000 : ℝ)
    (22648306773 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell654_rightExp :
    Real.exp (131 / 160 : ℝ) ≤ (22676634859 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (131 / 160 : ℝ) (205183213429 / 200000000000 : ℝ)
    (22676634859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell654_denomUpper :
    Real.exp (69197007336590387 / 10000000000000000 : ℝ) ≤ (506008543293 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69197007336590387 / 10000000000000000 : ℝ) (155175135457
    / 125000000000 : ℝ) (506008543293 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell654_denomLower :
    (2005469782343 / 2000000000 : ℝ) ≤ Real.exp (8638108046450327 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8638108046450327 / 1250000000000000 : ℝ) (1241043677687
    / 1000000000000 : ℝ) (2005469782343 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell654_product_lower :
    (8893967421450327 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (327 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell654_leftExp
    (by norm_num : (0 : ℝ) ≤ (22648306773 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell654_product_upper :
    Real.pi * Real.exp (131 / 160 : ℝ) ≤ (71240757336590387 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell654_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell654_endpointLower :
    (1579140897 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (327 / 800 : ℝ) (131 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8893967421450327 / 1250000000000000 : ℝ) (Real.pi * Real.exp (327 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell654_product_lower
  have hD : Real.exp (Real.pi * Real.exp (131 / 160 : ℝ) - (327 / 1600 : ℝ)) ≤
      (506008543293 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell654_denomUpper
    linarith [hpThetaJensenCell654_product_upper]
  have hi : (1 / (506008543293 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (131 / 160 : ℝ) - (327 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (506008543293 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (506008543293 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((327 / 1600 : ℝ) - Real.pi * Real.exp (131 / 160 : ℝ)) := by
    rw [show (327 / 1600 : ℝ) - Real.pi * Real.exp (131 / 160 : ℝ) =
      -(Real.pi * Real.exp (131 / 160 : ℝ) - (327 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (327 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (327 / 400 : ℝ)) := by
    have h := hpThetaJensenCell654_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (506008543293 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell654_endpointUpper :
    hpThetaJensenKernelEndpointUpper (327 / 800 : ℝ) (131 / 320 : ℝ) ≤ (400622913 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (131 / 160 : ℝ)) (71240757336590387 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (131 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell654_product_upper
  have hD : (2005469782343 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (327 / 400 : ℝ) - (131 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell654_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell654_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (327 / 400 : ℝ) - (131 / 640 : ℝ)) ≤
      (1 / (2005469782343 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2005469782343 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((131 / 640 : ℝ) - Real.pi * Real.exp (327 / 400 : ℝ)) ≤
      (2 / (2005469782343 / 2000000000 : ℝ) : ℝ) := by
    rw [show (131 / 640 : ℝ) - Real.pi * Real.exp (327 / 400 : ℝ) =
      -(Real.pi * Real.exp (327 / 400 : ℝ) - (131 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (71240757336590387 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (71240757336590387 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell654_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (327 / 800 : ℝ) (131 / 320 : ℝ)) :
    (1579140897 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (400622913 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell654_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell654_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell655_leftExp :
    (11338317429 / 5000000000 : ℝ) ≤ Real.exp (131 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (131 / 160 : ℝ) (128239508393 / 125000000000 : ℝ)
    (11338317429 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell655_rightExp :
    Real.exp (41 / 50 : ℝ) ≤ (2838124797 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 50 : ℝ) (512978071387 / 500000000000 : ℝ)
    (2838124797 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell655_denomUpper :
    Real.exp (8660373620381621 / 1250000000000000 : ℝ) ≤ (1275945112423 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8660373620381621 / 1250000000000000 : ℝ) (248346936747 /
    200000000000 : ℝ) (1275945112423 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell655_denomLower :
    (5056912398499 / 5000000000 : ℝ) ≤ Real.exp (4324420916050871 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4324420916050871 / 625000000000000 : ℝ) (248275349959 /
    200000000000 : ℝ) (5056912398499 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell655_product_lower :
    (4452545916050871 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (131 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell655_leftExp
    (by norm_num : (0 : ℝ) ≤ (11338317429 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell655_product_upper :
    Real.pi * Real.exp (41 / 50 : ℝ) ≤ (8916232995381621 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell655_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell655_endpointLower :
    (3140128219 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (131 / 320 : ℝ) (41 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4452545916050871 / 625000000000000 : ℝ) (Real.pi * Real.exp (131 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell655_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 50 : ℝ) - (131 / 640 : ℝ)) ≤
      (1275945112423 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell655_denomUpper
    linarith [hpThetaJensenCell655_product_upper]
  have hi : (1 / (1275945112423 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 50 : ℝ) - (131 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1275945112423 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1275945112423 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((131 / 640 : ℝ) - Real.pi * Real.exp (41 / 50 : ℝ)) := by
    rw [show (131 / 640 : ℝ) - Real.pi * Real.exp (41 / 50 : ℝ) =
      -(Real.pi * Real.exp (41 / 50 : ℝ) - (131 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (131 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (131 / 160 : ℝ)) := by
    have h := hpThetaJensenCell655_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1275945112423 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell655_endpointUpper :
    hpThetaJensenKernelEndpointUpper (131 / 320 : ℝ) (41 / 100 : ℝ) ≤ (3186595089 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 50 : ℝ)) (8916232995381621 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell655_product_upper
  have hD : (5056912398499 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (131 / 160 : ℝ) - (41 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell655_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell655_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (131 / 160 : ℝ) - (41 / 200 : ℝ)) ≤
      (1 / (5056912398499 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5056912398499 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 200 : ℝ) - Real.pi * Real.exp (131 / 160 : ℝ)) ≤
      (2 / (5056912398499 / 5000000000 : ℝ) : ℝ) := by
    rw [show (41 / 200 : ℝ) - Real.pi * Real.exp (131 / 160 : ℝ) =
      -(Real.pi * Real.exp (131 / 160 : ℝ) - (41 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8916232995381621 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (8916232995381621 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell655_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (131 / 320 : ℝ) (41 / 100 : ℝ)) :
    (3140128219 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3186595089 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell655_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell655_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell656_leftExp :
    (181639987 / 80000000 : ℝ) ≤ Real.exp (41 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 50 : ℝ) (1025956142773 / 1000000000000 : ℝ)
    (181639987 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell656_rightExp :
    Real.exp (657 / 800 : ℝ) ≤ (2273339737 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (657 / 800 : ℝ) (16031190937 / 15625000000 : ℝ)
    (2273339737 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell656_denomUpper :
    Real.exp (6936908204381041 / 1000000000000000 : ℝ) ≤ (10295820316967 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6936908204381041 / 1000000000000000 : ℝ) (310517201517 /
    250000000000 : ℝ) (10295820316967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell656_denomLower :
    (5100580000937 / 5000000000 : ℝ) ≤ Real.exp (69276716254913 / 10000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69276716254913 / 10000000000000 : ℝ) (49668413729 /
    40000000000 : ℝ) (5100580000937 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell656_product_lower :
    (71329841254913 / 10000000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell656_leftExp
    (by norm_num : (0 : ℝ) ≤ (181639987 / 80000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell656_product_upper :
    Real.pi * Real.exp (657 / 800 : ℝ) ≤ (7141908204381041 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell656_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell656_endpointLower :
    (1561021273 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 100 : ℝ) (657 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (71329841254913 / 10000000000000 : ℝ) (Real.pi * Real.exp (41 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell656_product_lower
  have hD : Real.exp (Real.pi * Real.exp (657 / 800 : ℝ) - (41 / 200 : ℝ)) ≤
      (10295820316967 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell656_denomUpper
    linarith [hpThetaJensenCell656_product_upper]
  have hi : (1 / (10295820316967 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (657 / 800 : ℝ) - (41 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10295820316967 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10295820316967 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 200 : ℝ) - Real.pi * Real.exp (657 / 800 : ℝ)) := by
    rw [show (41 / 200 : ℝ) - Real.pi * Real.exp (657 / 800 : ℝ) =
      -(Real.pi * Real.exp (657 / 800 : ℝ) - (41 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 50 : ℝ)) := by
    have h := hpThetaJensenCell656_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10295820316967 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell656_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 100 : ℝ) (657 / 1600 : ℝ) ≤ (3168275439 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (657 / 800 : ℝ)) (7141908204381041 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (657 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell656_product_upper
  have hD : (5100580000937 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 50 : ℝ) - (657 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell656_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell656_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 50 : ℝ) - (657 / 3200 : ℝ)) ≤
      (1 / (5100580000937 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5100580000937 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((657 / 3200 : ℝ) - Real.pi * Real.exp (41 / 50 : ℝ)) ≤
      (2 / (5100580000937 / 5000000000 : ℝ) : ℝ) := by
    rw [show (657 / 3200 : ℝ) - Real.pi * Real.exp (41 / 50 : ℝ) =
      -(Real.pi * Real.exp (41 / 50 : ℝ) - (657 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7141908204381041 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (7141908204381041 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell656_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 100 : ℝ) (657 / 1600 : ℝ)) :
    (1561021273 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3168275439 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell656_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell656_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell657_leftExp :
    (2841674671 / 1250000000 : ℝ) ≤ Real.exp (657 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (657 / 800 : ℝ) (1025996219967 / 1000000000000 : ℝ)
    (2841674671 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell657_rightExp :
    Real.exp (329 / 400 : ℝ) ≤ (4552366377 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (329 / 400 : ℝ) (1026036298729 / 1000000000000 : ℝ)
    (4552366377 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell657_denomUpper :
    Real.exp (13891057343418561 / 2000000000000000 : ℝ) ≤ (1038495875517 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13891057343418561 / 2000000000000000 : ℝ) (248480690313
    / 200000000000 : ℝ) (1038495875517 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell657_denomLower :
    (5144682020889 / 5000000000 : ℝ) ≤ Real.exp (1083793895377029 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1083793895377029 / 156250000000000 : ℝ) (621022229443 /
    500000000000 : ℝ) (5144682020889 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell657_product_lower :
    (1115922801627029 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (657 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell657_leftExp
    (by norm_num : (0 : ℝ) ≤ (2841674671 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell657_product_upper :
    Real.pi * Real.exp (329 / 400 : ℝ) ≤ (14301682343418561 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell657_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell657_endpointLower :
    (1552012381 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (657 / 1600 : ℝ) (329 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1115922801627029 / 156250000000000 : ℝ) (Real.pi * Real.exp (657 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell657_product_lower
  have hD : Real.exp (Real.pi * Real.exp (329 / 400 : ℝ) - (657 / 3200 : ℝ)) ≤
      (1038495875517 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell657_denomUpper
    linarith [hpThetaJensenCell657_product_upper]
  have hi : (1 / (1038495875517 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (329 / 400 : ℝ) - (657 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1038495875517 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1038495875517 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((657 / 3200 : ℝ) - Real.pi * Real.exp (329 / 400 : ℝ)) := by
    rw [show (657 / 3200 : ℝ) - Real.pi * Real.exp (329 / 400 : ℝ) =
      -(Real.pi * Real.exp (329 / 400 : ℝ) - (657 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (657 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (657 / 800 : ℝ)) := by
    have h := hpThetaJensenCell657_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1038495875517 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell657_endpointUpper :
    hpThetaJensenKernelEndpointUpper (657 / 1600 : ℝ) (329 / 800 : ℝ) ≤ (393753043 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (329 / 400 : ℝ)) (14301682343418561 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (329 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell657_product_upper
  have hD : (5144682020889 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (657 / 800 : ℝ) - (329 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell657_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell657_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (657 / 800 : ℝ) - (329 / 1600 : ℝ)) ≤
      (1 / (5144682020889 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5144682020889 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((329 / 1600 : ℝ) - Real.pi * Real.exp (657 / 800 : ℝ)) ≤
      (2 / (5144682020889 / 5000000000 : ℝ) : ℝ) := by
    rw [show (329 / 1600 : ℝ) - Real.pi * Real.exp (657 / 800 : ℝ) =
      -(Real.pi * Real.exp (657 / 800 : ℝ) - (329 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14301682343418561 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (14301682343418561 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell657_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (657 / 1600 : ℝ) (329 / 800 : ℝ)) :
    (1552012381 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (393753043 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell657_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell657_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell658_leftExp :
    (22761831883 / 10000000000 : ℝ) ≤ Real.exp (329 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (329 / 400 : ℝ) (128254537341 / 125000000000 : ℝ)
    (22761831883 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell658_rightExp :
    Real.exp (659 / 800 : ℝ) ≤ (5697575491 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (659 / 800 : ℝ) (513038189527 / 500000000000 : ℝ)
    (5697575491 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell658_denomUpper :
    Real.exp (17385400779497163 / 2500000000000000 : ℝ) ≤ (1309373245451 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17385400779497163 / 2500000000000000 : ℝ) (310684655281
    / 250000000000 : ℝ) (1309373245451 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell658_denomLower :
    (10378446553553 / 10000000000 : ℝ) ≤ Real.exp (8681126743622217 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8681126743622217 / 1250000000000000 : ℝ) (77648693607 /
    62500000000 : ℝ) (10378446553553 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell658_product_lower :
    (8938548618622217 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (329 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell658_leftExp
    (by norm_num : (0 : ℝ) ≤ (22761831883 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell658_product_upper :
    Real.pi * Real.exp (659 / 800 : ℝ) ≤ (17899463279497163 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell658_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell658_endpointLower :
    (154303743 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (329 / 800 : ℝ) (659 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8938548618622217 / 1250000000000000 : ℝ) (Real.pi * Real.exp (329 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell658_product_lower
  have hD : Real.exp (Real.pi * Real.exp (659 / 800 : ℝ) - (329 / 1600 : ℝ)) ≤
      (1309373245451 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell658_denomUpper
    linarith [hpThetaJensenCell658_product_upper]
  have hi : (1 / (1309373245451 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (659 / 800 : ℝ) - (329 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1309373245451 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1309373245451 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((329 / 1600 : ℝ) - Real.pi * Real.exp (659 / 800 : ℝ)) := by
    rw [show (329 / 1600 : ℝ) - Real.pi * Real.exp (659 / 800 : ℝ) =
      -(Real.pi * Real.exp (659 / 800 : ℝ) - (329 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (329 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (329 / 400 : ℝ)) := by
    have h := hpThetaJensenCell658_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1309373245451 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell658_endpointUpper :
    hpThetaJensenKernelEndpointUpper (329 / 800 : ℝ) (659 / 1600 : ℝ) ≤ (3131841791 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (659 / 800 : ℝ)) (17899463279497163 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (659 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell658_product_upper
  have hD : (10378446553553 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (329 / 400 : ℝ) - (659 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell658_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell658_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (329 / 400 : ℝ) - (659 / 3200 : ℝ)) ≤
      (1 / (10378446553553 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10378446553553 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((659 / 3200 : ℝ) - Real.pi * Real.exp (329 / 400 : ℝ)) ≤
      (2 / (10378446553553 / 10000000000 : ℝ) : ℝ) := by
    rw [show (659 / 3200 : ℝ) - Real.pi * Real.exp (329 / 400 : ℝ) =
      -(Real.pi * Real.exp (329 / 400 : ℝ) - (659 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17899463279497163 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (17899463279497163 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell658_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (329 / 800 : ℝ) (659 / 1600 : ℝ)) :
    (154303743 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3131841791 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell658_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell658_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell659_leftExp :
    (11395150981 / 5000000000 : ℝ) ≤ Real.exp (659 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (659 / 800 : ℝ) (1026076379053 / 1000000000000 : ℝ)
    (11395150981 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell659_rightExp :
    Real.exp (33 / 40 : ℝ) ≤ (11409403827 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 40 : ℝ) (513058230473 / 500000000000 : ℝ)
    (11409403827 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell659_denomUpper :
    Real.exp (34814015697076411 / 5000000000000000 : ℝ) ≤ (10565911824009 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34814015697076411 / 5000000000000000 : ℝ) (77692144731 /
    62500000000 : ℝ) (10565911824009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell659_denomLower :
    (10468417278081 / 10000000000 : ℝ) ≤ Real.exp (4345958145087719 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4345958145087719 / 625000000000000 : ℝ) (1242714260591 /
    1000000000000 : ℝ) (10468417278081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell659_product_lower :
    (4474864395087719 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (659 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell659_leftExp
    (by norm_num : (0 : ℝ) ≤ (11395150981 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell659_product_upper :
    Real.pi * Real.exp (33 / 40 : ℝ) ≤ (35843703197076411 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell659_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell659_endpointLower :
    (3068192821 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (659 / 1600 : ℝ) (33 / 80 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4474864395087719 / 625000000000000 : ℝ) (Real.pi * Real.exp (659 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell659_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 40 : ℝ) - (659 / 3200 : ℝ)) ≤
      (10565911824009 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell659_denomUpper
    linarith [hpThetaJensenCell659_product_upper]
  have hi : (1 / (10565911824009 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 40 : ℝ) - (659 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10565911824009 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10565911824009 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((659 / 3200 : ℝ) - Real.pi * Real.exp (33 / 40 : ℝ)) := by
    rw [show (659 / 3200 : ℝ) - Real.pi * Real.exp (33 / 40 : ℝ) =
      -(Real.pi * Real.exp (33 / 40 : ℝ) - (659 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (659 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (659 / 800 : ℝ)) := by
    have h := hpThetaJensenCell659_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10565911824009 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell659_endpointUpper :
    hpThetaJensenKernelEndpointUpper (659 / 1600 : ℝ) (33 / 80 : ℝ) ≤ (778431943 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 40 : ℝ)) (35843703197076411 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell659_product_upper
  have hD : (10468417278081 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (659 / 800 : ℝ) - (33 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell659_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell659_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (659 / 800 : ℝ) - (33 / 160 : ℝ)) ≤
      (1 / (10468417278081 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10468417278081 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 160 : ℝ) - Real.pi * Real.exp (659 / 800 : ℝ)) ≤
      (2 / (10468417278081 / 10000000000 : ℝ) : ℝ) := by
    rw [show (33 / 160 : ℝ) - Real.pi * Real.exp (659 / 800 : ℝ) =
      -(Real.pi * Real.exp (659 / 800 : ℝ) - (33 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35843703197076411 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (35843703197076411 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell659_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (659 / 1600 : ℝ) (33 / 80 : ℝ)) :
    (3068192821 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (778431943 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell659_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell659_endpointUpper

def hpThetaJensenCellsBatch032Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3419563111 / 10000000000 : ℝ)
  | 1 => (1700229403 / 5000000000 : ℝ)
  | 2 => (845355591 / 2500000000 : ℝ)
  | 3 => (3362453801 / 10000000000 : ℝ)
  | 4 => (3343553127 / 10000000000 : ℝ)
  | 5 => (664944071 / 2000000000 : ℝ)
  | 6 => (3305955493 / 10000000000 : ℝ)
  | 7 => (657451709 / 2000000000 : ℝ)
  | 8 => (40857869 / 125000000 : ℝ)
  | 9 => (3250068421 / 10000000000 : ℝ)
  | 10 => (3231575247 / 10000000000 : ℝ)
  | 11 => (3213149999 / 10000000000 : ℝ)
  | 12 => (1597396339 / 5000000000 : ℝ)
  | 13 => (1588251639 / 5000000000 : ℝ)
  | 14 => (1579140897 / 5000000000 : ℝ)
  | 15 => (3140128219 / 10000000000 : ℝ)
  | 16 => (1561021273 / 5000000000 : ℝ)
  | 17 => (1552012381 / 5000000000 : ℝ)
  | 18 => (154303743 / 500000000 : ℝ)
  | 19 => (3068192821 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch032Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3469618373 / 10000000000 : ℝ)
  | 1 => (3450270297 / 10000000000 : ℝ)
  | 2 => (3430990729 / 10000000000 : ℝ)
  | 3 => (3411779683 / 10000000000 : ℝ)
  | 4 => (1696318587 / 5000000000 : ℝ)
  | 5 => (3373563211 / 10000000000 : ℝ)
  | 6 => (3354557807 / 10000000000 : ℝ)
  | 7 => (333562097 / 1000000000 : ℝ)
  | 8 => (663350541 / 2000000000 : ℝ)
  | 9 => (3297953019 / 10000000000 : ℝ)
  | 10 => (1639610957 / 5000000000 : ℝ)
  | 11 => (3260559391 / 10000000000 : ℝ)
  | 12 => (3241965449 / 10000000000 : ℝ)
  | 13 => (402930011 / 1250000000 : ℝ)
  | 14 => (400622913 / 1250000000 : ℝ)
  | 15 => (3186595089 / 10000000000 : ℝ)
  | 16 => (3168275439 / 10000000000 : ℝ)
  | 17 => (393753043 / 1250000000 : ℝ)
  | 18 => (3131841791 / 10000000000 : ℝ)
  | 19 => (778431943 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch032_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch032Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch032Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell640_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell641_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell642_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell643_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell644_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell645_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell646_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell647_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell648_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell649_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell650_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell651_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell652_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell653_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell654_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell655_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell656_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell657_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell658_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell659_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper] at h ⊢
    exact h

end HodgeProofHP
