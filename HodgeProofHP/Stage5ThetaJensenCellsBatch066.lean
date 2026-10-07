import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1320_leftExp :
    (5206979827 / 1000000000 : ℝ) ≤ Real.exp (33 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 20 : ℝ) (526457495711 / 500000000000 : ℝ)
    (5206979827 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1320_rightExp :
    Real.exp (1321 / 800 : ℝ) ≤ (52134926217 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1321 / 800 : ℝ) (526478060859 / 500000000000 : ℝ)
    (52134926217 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1320_denomUpper :
    Real.exp (159661719258843681 / 10000000000000000 : ℝ) ≤ (4295269012565957 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (159661719258843681 / 10000000000000000 : ℝ)
    (823489641661 / 500000000000 : ℝ) (4295269012565957 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1320_denomLower :
    (84138832608112247 / 10000000000 : ℝ) ≤ Real.exp (1993174208583073 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1993174208583073 / 125000000000000 : ℝ) (205738776621 /
    125000000000 : ℝ) (84138832608112247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1320_product_lower :
    (2044775771083073 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1320_leftExp
    (by norm_num : (0 : ℝ) ≤ (5206979827 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1320_product_upper :
    Real.pi * Real.exp (1321 / 800 : ℝ) ≤ (163786719258843681 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1320_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1320_endpointLower :
    (1131727 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 40 : ℝ) (1321 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2044775771083073 / 125000000000000 : ℝ) (Real.pi * Real.exp (33 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell1320_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1321 / 800 : ℝ) - (33 / 80 : ℝ)) ≤
      (4295269012565957 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1320_denomUpper
    linarith [hpThetaJensenCell1320_product_upper]
  have hi : (1 / (4295269012565957 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1321 / 800 : ℝ) - (33 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4295269012565957 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4295269012565957 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 80 : ℝ) - Real.pi * Real.exp (1321 / 800 : ℝ)) := by
    rw [show (33 / 80 : ℝ) - Real.pi * Real.exp (1321 / 800 : ℝ) =
      -(Real.pi * Real.exp (1321 / 800 : ℝ) - (33 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 20 : ℝ)) := by
    have h := hpThetaJensenCell1320_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4295269012565957 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1320_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 40 : ℝ) (1321 / 1600 : ℝ) ≤ (1161579 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1321 / 800 : ℝ)) (163786719258843681 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1321 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1320_product_upper
  have hD : (84138832608112247 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 20 : ℝ) - (1321 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1320_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1320_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 20 : ℝ) - (1321 / 3200 : ℝ)) ≤
      (1 / (84138832608112247 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (84138832608112247 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1321 / 3200 : ℝ) - Real.pi * Real.exp (33 / 20 : ℝ)) ≤
      (2 / (84138832608112247 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1321 / 3200 : ℝ) - Real.pi * Real.exp (33 / 20 : ℝ) =
      -(Real.pi * Real.exp (33 / 20 : ℝ) - (1321 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (163786719258843681 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (163786719258843681 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1320_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 40 : ℝ) (1321 / 1600 : ℝ)) :
    (1131727 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1161579 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1320_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1320_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1321_leftExp :
    (26067463107 / 5000000000 : ℝ) ≤ Real.exp (1321 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1321 / 800 : ℝ) (1052956121717 / 1000000000000 : ℝ)
    (26067463107 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1321_rightExp :
    Real.exp (661 / 400 : ℝ) ≤ (26100067811 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (661 / 400 : ℝ) (52649862681 / 50000000000 : ℝ)
    (26100067811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1321_denomUpper :
    Real.exp (79931727834562923 / 5000000000000000 : ℝ) ≤ (87656003405724799 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (79931727834562923 / 5000000000000000 : ℝ) (1648017909703
    / 1000000000000 : ℝ) (87656003405724799 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1321_denomLower :
    (85851258494594249 / 10000000000 : ℝ) ≤ Real.exp (9978463569655793 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9978463569655793 / 625000000000000 : ℝ) (1646946847699 /
    1000000000000 : ℝ) (85851258494594249 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1321_product_lower :
    (10236666694655793 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1321 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1321_leftExp
    (by norm_num : (0 : ℝ) ≤ (26067463107 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1321_product_upper :
    Real.pi * Real.exp (661 / 400 : ℝ) ≤ (81995790334562923 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1321_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1321_endpointLower :
    (1112041 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1321 / 1600 : ℝ) (661 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10236666694655793 / 625000000000000 : ℝ) (Real.pi * Real.exp (1321 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1321_product_lower
  have hD : Real.exp (Real.pi * Real.exp (661 / 400 : ℝ) - (1321 / 3200 : ℝ)) ≤
      (87656003405724799 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1321_denomUpper
    linarith [hpThetaJensenCell1321_product_upper]
  have hi : (1 / (87656003405724799 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (661 / 400 : ℝ) - (1321 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (87656003405724799 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (87656003405724799 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1321 / 3200 : ℝ) - Real.pi * Real.exp (661 / 400 : ℝ)) := by
    rw [show (1321 / 3200 : ℝ) - Real.pi * Real.exp (661 / 400 : ℝ) =
      -(Real.pi * Real.exp (661 / 400 : ℝ) - (1321 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1321 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1321 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1321_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (87656003405724799 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1321_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1321 / 1600 : ℝ) (661 / 800 : ℝ) ≤ (1141403 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (661 / 400 : ℝ)) (81995790334562923 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (661 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1321_product_upper
  have hD : (85851258494594249 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1321 / 800 : ℝ) - (661 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1321_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1321_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1321 / 800 : ℝ) - (661 / 1600 : ℝ)) ≤
      (1 / (85851258494594249 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (85851258494594249 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((661 / 1600 : ℝ) - Real.pi * Real.exp (1321 / 800 : ℝ)) ≤
      (2 / (85851258494594249 / 10000000000 : ℝ) : ℝ) := by
    rw [show (661 / 1600 : ℝ) - Real.pi * Real.exp (1321 / 800 : ℝ) =
      -(Real.pi * Real.exp (1321 / 800 : ℝ) - (661 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (81995790334562923 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (81995790334562923 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1321_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1321 / 1600 : ℝ) (661 / 800 : ℝ)) :
    (1112041 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1141403 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1321_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1321_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1322_leftExp :
    (2610006781 / 500000000 : ℝ) ≤ Real.exp (661 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (661 / 400 : ℝ) (1052997253619 / 1000000000000 : ℝ)
    (2610006781 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1322_rightExp :
    Real.exp (1323 / 800 : ℝ) ≤ (52265426591 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1323 / 800 : ℝ) (1053038387129 / 1000000000000 : ℝ)
    (52265426591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1322_denomUpper :
    Real.exp (160065448320299463 / 10000000000000000 : ℝ) ≤ (89444593547530227 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (160065448320299463 / 10000000000000000 : ℝ)
    (329811702311 / 200000000000 : ℝ) (89444593547530227 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1322_denomLower :
    (87600778183748659 / 10000000000 : ℝ) ≤ Real.exp (999107209141919 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (999107209141919 / 62500000000000 : ℝ) (329597090661 /
    200000000000 : ℝ) (87600778183748659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1322_product_lower :
    (1024947052891919 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (661 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1322_leftExp
    (by norm_num : (0 : ℝ) ≤ (2610006781 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1322_product_upper :
    Real.pi * Real.exp (1323 / 800 : ℝ) ≤ (164196698320299463 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1322_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1322_endpointLower :
    (2185339 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (661 / 800 : ℝ) (1323 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1024947052891919 / 62500000000000 : ℝ) (Real.pi * Real.exp (661 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1322_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1323 / 800 : ℝ) - (661 / 1600 : ℝ)) ≤
      (89444593547530227 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1322_denomUpper
    linarith [hpThetaJensenCell1322_product_upper]
  have hi : (1 / (89444593547530227 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1323 / 800 : ℝ) - (661 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (89444593547530227 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (89444593547530227 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((661 / 1600 : ℝ) - Real.pi * Real.exp (1323 / 800 : ℝ)) := by
    rw [show (661 / 1600 : ℝ) - Real.pi * Real.exp (1323 / 800 : ℝ) =
      -(Real.pi * Real.exp (1323 / 800 : ℝ) - (661 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (661 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (661 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1322_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (89444593547530227 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1322_endpointUpper :
    hpThetaJensenKernelEndpointUpper (661 / 800 : ℝ) (1323 / 1600 : ℝ) ≤ (2243097 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1323 / 800 : ℝ)) (164196698320299463 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1323 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1322_product_upper
  have hD : (87600778183748659 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (661 / 400 : ℝ) - (1323 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1322_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1322_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (661 / 400 : ℝ) - (1323 / 3200 : ℝ)) ≤
      (1 / (87600778183748659 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (87600778183748659 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1323 / 3200 : ℝ) - Real.pi * Real.exp (661 / 400 : ℝ)) ≤
      (2 / (87600778183748659 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1323 / 3200 : ℝ) - Real.pi * Real.exp (661 / 400 : ℝ) =
      -(Real.pi * Real.exp (661 / 400 : ℝ) - (1323 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (164196698320299463 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (164196698320299463 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1322_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (661 / 800 : ℝ) (1323 / 1600 : ℝ)) :
    (2185339 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2243097 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1322_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1322_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1323_leftExp :
    (13066356647 / 2500000000 : ℝ) ≤ Real.exp (1323 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1323 / 800 : ℝ) (131629798391 / 125000000000 : ℝ)
    (13066356647 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1323_rightExp :
    Real.exp (331 / 200 : ℝ) ≤ (52330799223 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (331 / 200 : ℝ) (263269880561 / 250000000000 : ℝ)
    (52330799223 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1323_denomUpper :
    Real.exp (160267697523382239 / 10000000000000000 : ℝ) ≤ (91272020818292201 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (160267697523382239 / 10000000000000000 : ℝ)
    (1650101093397 / 1000000000000 : ℝ) (91272020818292201 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1323_denomLower :
    (89388240863292569 / 10000000000 : ℝ) ≤ Real.exp (5001848313920253 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5001848313920253 / 312500000000000 : ℝ) (1649026034311 /
    1000000000000 : ℝ) (89388240863292569 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1323_product_lower :
    (5131145188920253 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1323 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1323_leftExp
    (by norm_num : (0 : ℝ) ≤ (13066356647 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1323_product_upper :
    Real.pi * Real.exp (331 / 200 : ℝ) ≤ (164402072523382239 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1323_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1323_endpointLower :
    (429443 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1323 / 1600 : ℝ) (331 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5131145188920253 / 312500000000000 : ℝ) (Real.pi * Real.exp (1323 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1323_product_lower
  have hD : Real.exp (Real.pi * Real.exp (331 / 200 : ℝ) - (1323 / 3200 : ℝ)) ≤
      (91272020818292201 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1323_denomUpper
    linarith [hpThetaJensenCell1323_product_upper]
  have hi : (1 / (91272020818292201 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (331 / 200 : ℝ) - (1323 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (91272020818292201 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (91272020818292201 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1323 / 3200 : ℝ) - Real.pi * Real.exp (331 / 200 : ℝ)) := by
    rw [show (1323 / 3200 : ℝ) - Real.pi * Real.exp (331 / 200 : ℝ) =
      -(Real.pi * Real.exp (331 / 200 : ℝ) - (1323 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1323 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1323 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1323_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (91272020818292201 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1323_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1323 / 1600 : ℝ) (331 / 400 : ℝ) ≤ (1102011 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (331 / 200 : ℝ)) (164402072523382239 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (331 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1323_product_upper
  have hD : (89388240863292569 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1323 / 800 : ℝ) - (331 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1323_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1323_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1323 / 800 : ℝ) - (331 / 800 : ℝ)) ≤
      (1 / (89388240863292569 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (89388240863292569 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((331 / 800 : ℝ) - Real.pi * Real.exp (1323 / 800 : ℝ)) ≤
      (2 / (89388240863292569 / 10000000000 : ℝ) : ℝ) := by
    rw [show (331 / 800 : ℝ) - Real.pi * Real.exp (1323 / 800 : ℝ) =
      -(Real.pi * Real.exp (1323 / 800 : ℝ) - (331 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (164402072523382239 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (164402072523382239 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1323_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1323 / 1600 : ℝ) (331 / 400 : ℝ)) :
    (429443 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1102011 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1323_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1323_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1324_leftExp :
    (2616539961 / 500000000 : ℝ) ≤ Real.exp (331 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (331 / 200 : ℝ) (1053079522243 / 1000000000000 : ℝ)
    (2616539961 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1324_rightExp :
    Real.exp (53 / 32 : ℝ) ≤ (26198126811 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 32 : ℝ) (526560329483 / 500000000000 : ℝ)
    (26198126811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1324_denomUpper :
    Real.exp (80235101802549923 / 5000000000000000 : ℝ) ≤ (9313917645932133 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (80235101802549923 / 5000000000000000 : ℝ) (825572829919
    / 500000000000 : ℝ) (9313917645932133 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1324_denomLower :
    (18242903240824619 / 2000000000 : ℝ) ≤ Real.exp (1001633719894739 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1001633719894739 / 62500000000000 : ℝ) (825034297641 /
    500000000000 : ℝ) (18242903240824619 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1324_product_lower :
    (1027512626144739 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (331 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1324_leftExp
    (by norm_num : (0 : ℝ) ≤ (2616539961 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1324_product_upper :
    Real.pi * Real.exp (53 / 32 : ℝ) ≤ (82303851802549923 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1324_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1324_endpointLower :
    (1054851 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (331 / 400 : ℝ) (53 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1027512626144739 / 62500000000000 : ℝ) (Real.pi * Real.exp (331 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1324_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 32 : ℝ) - (331 / 800 : ℝ)) ≤
      (9313917645932133 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1324_denomUpper
    linarith [hpThetaJensenCell1324_product_upper]
  have hi : (1 / (9313917645932133 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 32 : ℝ) - (331 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9313917645932133 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9313917645932133 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((331 / 800 : ℝ) - Real.pi * Real.exp (53 / 32 : ℝ)) := by
    rw [show (331 / 800 : ℝ) - Real.pi * Real.exp (53 / 32 : ℝ) =
      -(Real.pi * Real.exp (53 / 32 : ℝ) - (331 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (331 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (331 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1324_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9313917645932133 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1324_endpointUpper :
    hpThetaJensenKernelEndpointUpper (331 / 400 : ℝ) (53 / 64 : ℝ) ≤ (2165571 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 32 : ℝ)) (82303851802549923 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1324_product_upper
  have hD : (18242903240824619 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (331 / 200 : ℝ) - (53 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1324_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1324_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (331 / 200 : ℝ) - (53 / 128 : ℝ)) ≤
      (1 / (18242903240824619 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18242903240824619 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 128 : ℝ) - Real.pi * Real.exp (331 / 200 : ℝ)) ≤
      (2 / (18242903240824619 / 2000000000 : ℝ) : ℝ) := by
    rw [show (53 / 128 : ℝ) - Real.pi * Real.exp (331 / 200 : ℝ) =
      -(Real.pi * Real.exp (331 / 200 : ℝ) - (53 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (82303851802549923 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (82303851802549923 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1324_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (331 / 400 : ℝ) (53 / 64 : ℝ)) :
    (1054851 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2165571 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1324_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1324_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1325_leftExp :
    (52396253619 / 10000000000 : ℝ) ≤ Real.exp (53 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 32 : ℝ) (210624131793 / 200000000000 : ℝ)
    (52396253619 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1325_rightExp :
    Real.exp (663 / 400 : ℝ) ≤ (13115447473 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (663 / 400 : ℝ) (65822612331 / 62500000000 : ℝ)
    (13115447473 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1325_denomUpper :
    Real.exp (40168241723044489 / 2500000000000000 : ℝ) ≤ (47523486606042491 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (40168241723044489 / 2500000000000000 : ℝ) (3304384431 /
    2000000000 : ℝ) (47523486606042491 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1325_denomLower :
    (93080494863467501 / 10000000000 : ℝ) ≤ Real.exp (20057987649927681 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20057987649927681 / 1250000000000000 : ℝ) (825556570407
    / 500000000000 : ℝ) (93080494863467501 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1325_product_lower :
    (20575956399927681 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1325_leftExp
    (by norm_num : (0 : ℝ) ≤ (52396253619 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1325_product_upper :
    Real.pi * Real.exp (663 / 400 : ℝ) ≤ (41203397973044489 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1325_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1325_endpointLower :
    (2072791 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 64 : ℝ) (663 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20575956399927681 / 1250000000000000 : ℝ) (Real.pi * Real.exp (53 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1325_product_lower
  have hD : Real.exp (Real.pi * Real.exp (663 / 400 : ℝ) - (53 / 128 : ℝ)) ≤
      (47523486606042491 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1325_denomUpper
    linarith [hpThetaJensenCell1325_product_upper]
  have hi : (1 / (47523486606042491 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (663 / 400 : ℝ) - (53 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (47523486606042491 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (47523486606042491 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 128 : ℝ) - Real.pi * Real.exp (663 / 400 : ℝ)) := by
    rw [show (53 / 128 : ℝ) - Real.pi * Real.exp (663 / 400 : ℝ) =
      -(Real.pi * Real.exp (663 / 400 : ℝ) - (53 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1325_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (47523486606042491 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1325_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 64 : ℝ) (663 / 800 : ℝ) ≤ (2127737 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (663 / 400 : ℝ)) (41203397973044489 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (663 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1325_product_upper
  have hD : (93080494863467501 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 32 : ℝ) - (663 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1325_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1325_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 32 : ℝ) - (663 / 1600 : ℝ)) ≤
      (1 / (93080494863467501 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (93080494863467501 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((663 / 1600 : ℝ) - Real.pi * Real.exp (53 / 32 : ℝ)) ≤
      (2 / (93080494863467501 / 10000000000 : ℝ) : ℝ) := by
    rw [show (663 / 1600 : ℝ) - Real.pi * Real.exp (53 / 32 : ℝ) =
      -(Real.pi * Real.exp (53 / 32 : ℝ) - (663 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41203397973044489 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (41203397973044489 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1325_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 64 : ℝ) (663 / 800 : ℝ)) :
    (2072791 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2127737 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1325_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1325_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1326_leftExp :
    (52461789889 / 10000000000 : ℝ) ≤ Real.exp (663 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (663 / 400 : ℝ) (210632359459 / 200000000000 : ℝ)
    (52461789889 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1326_rightExp :
    Real.exp (1327 / 800 : ℝ) ≤ (13131852033 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1327 / 800 : ℝ) (65825183577 / 62500000000 : ℝ)
    (13131852033 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1326_denomUpper :
    Real.exp (40218996923908569 / 2500000000000000 : ℝ) ≤ (96996345701457173 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (40218996923908569 / 2500000000000000 : ℝ) (1653240764933
    / 1000000000000 : ℝ) (96996345701457173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1326_denomLower :
    (23746772249978533 / 2500000000 : ℝ) ≤ Real.exp (20083333052620411 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20083333052620411 / 1250000000000000 : ℝ) (66086387021 /
    40000000000 : ℝ) (23746772249978533 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1326_product_lower :
    (20601692427620411 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (663 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1326_leftExp
    (by norm_num : (0 : ℝ) ≤ (52461789889 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1326_product_upper :
    Real.pi * Real.exp (1327 / 800 : ℝ) ≤ (41254934423908569 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1326_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1326_endpointLower :
    (254559 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (663 / 800 : ℝ) (1327 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20601692427620411 / 1250000000000000 : ℝ) (Real.pi * Real.exp (663 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1326_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1327 / 800 : ℝ) - (663 / 1600 : ℝ)) ≤
      (96996345701457173 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1326_denomUpper
    linarith [hpThetaJensenCell1326_product_upper]
  have hi : (1 / (96996345701457173 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1327 / 800 : ℝ) - (663 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (96996345701457173 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (96996345701457173 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((663 / 1600 : ℝ) - Real.pi * Real.exp (1327 / 800 : ℝ)) := by
    rw [show (663 / 1600 : ℝ) - Real.pi * Real.exp (1327 / 800 : ℝ) =
      -(Real.pi * Real.exp (1327 / 800 : ℝ) - (663 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (663 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (663 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1326_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (96996345701457173 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1326_endpointUpper :
    hpThetaJensenKernelEndpointUpper (663 / 800 : ℝ) (1327 / 1600 : ℝ) ≤ (2090509 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1327 / 800 : ℝ)) (41254934423908569 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1327 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1326_product_upper
  have hD : (23746772249978533 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (663 / 400 : ℝ) - (1327 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1326_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1326_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (663 / 400 : ℝ) - (1327 / 3200 : ℝ)) ≤
      (1 / (23746772249978533 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23746772249978533 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1327 / 3200 : ℝ) - Real.pi * Real.exp (663 / 400 : ℝ)) ≤
      (2 / (23746772249978533 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1327 / 3200 : ℝ) - Real.pi * Real.exp (663 / 400 : ℝ) =
      -(Real.pi * Real.exp (663 / 400 : ℝ) - (1327 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41254934423908569 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (41254934423908569 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1326_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (663 / 800 : ℝ) (1327 / 1600 : ℝ)) :
    (254559 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2090509 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1326_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1326_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1327_leftExp :
    (52527408129 / 10000000000 : ℝ) ≤ Real.exp (1327 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1327 / 800 : ℝ) (1053202937231 / 1000000000000 : ℝ)
    (52527408129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1327_rightExp :
    Real.exp (83 / 50 : ℝ) ≤ (10518621689 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83 / 50 : ℝ) (42129763151 / 40000000000 : ℝ)
    (10518621689 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1327_denomUpper :
    Real.exp (32215853267810577 / 2000000000000000 : ℝ) ≤ (49494125630181253 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (32215853267810577 / 2000000000000000 : ℝ) (1654291312763
    / 1000000000000 : ℝ) (49494125630181253 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1327_denomLower :
    (48467616327106747 / 5000000000 : ℝ) ≤ Real.exp (20108710644850171 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20108710644850171 / 1250000000000000 : ℝ) (25831378187 /
    15625000000 : ℝ) (48467616327106747 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1327_product_lower :
    (20627460644850171 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1327 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1327_leftExp
    (by norm_num : (0 : ℝ) ≤ (52527408129 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1327_product_upper :
    Real.pi * Real.exp (83 / 50 : ℝ) ≤ (33045228267810577 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1327_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1327_endpointLower :
    (1000369 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1327 / 1600 : ℝ) (83 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20627460644850171 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1327 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1327_product_lower
  have hD : Real.exp (Real.pi * Real.exp (83 / 50 : ℝ) - (1327 / 3200 : ℝ)) ≤
      (49494125630181253 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1327_denomUpper
    linarith [hpThetaJensenCell1327_product_upper]
  have hi : (1 / (49494125630181253 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (83 / 50 : ℝ) - (1327 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (49494125630181253 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (49494125630181253 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1327 / 3200 : ℝ) - Real.pi * Real.exp (83 / 50 : ℝ)) := by
    rw [show (1327 / 3200 : ℝ) - Real.pi * Real.exp (83 / 50 : ℝ) =
      -(Real.pi * Real.exp (83 / 50 : ℝ) - (1327 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1327 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1327 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1327_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (49494125630181253 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1327_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1327 / 1600 : ℝ) (83 / 100 : ℝ) ≤ (2053879 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (83 / 50 : ℝ)) (33045228267810577 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (83 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1327_product_upper
  have hD : (48467616327106747 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1327 / 800 : ℝ) - (83 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1327_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1327_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1327 / 800 : ℝ) - (83 / 200 : ℝ)) ≤
      (1 / (48467616327106747 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (48467616327106747 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((83 / 200 : ℝ) - Real.pi * Real.exp (1327 / 800 : ℝ)) ≤
      (2 / (48467616327106747 / 5000000000 : ℝ) : ℝ) := by
    rw [show (83 / 200 : ℝ) - Real.pi * Real.exp (1327 / 800 : ℝ) =
      -(Real.pi * Real.exp (1327 / 800 : ℝ) - (83 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33045228267810577 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (33045228267810577 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1327_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1327 / 1600 : ℝ) (83 / 100 : ℝ)) :
    (1000369 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2053879 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1327_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1327_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1328_leftExp :
    (52593108443 / 10000000000 : ℝ) ≤ Real.exp (83 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (83 / 50 : ℝ) (526622039387 / 500000000000 : ℝ)
    (52593108443 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1328_rightExp :
    Real.exp (1329 / 800 : ℝ) ≤ (52658890937 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1329 / 800 : ℝ) (526642610963 / 500000000000 : ℝ)
    (52658890937 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1328_denomUpper :
    Real.exp (161282803155442641 / 10000000000000000 : ℝ) ≤ (50511835240836089 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (161282803155442641 / 10000000000000000 : ℝ)
    (413835965919 / 250000000000 : ℝ) (50511835240836089 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1328_denomLower :
    (24731470646062853 / 2500000000 : ℝ) ≤ Real.exp (20134120467457657 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20134120467457657 / 1250000000000000 : ℝ) (51695585337 /
    31250000000 : ℝ) (24731470646062853 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1328_product_lower :
    (20653261092457657 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (83 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1328_leftExp
    (by norm_num : (0 : ℝ) ≤ (52593108443 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1328_product_upper :
    Real.pi * Real.exp (1329 / 800 : ℝ) ≤ (165432803155442641 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1328_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1328_endpointLower :
    (98279 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 100 : ℝ) (1329 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20653261092457657 / 1250000000000000 : ℝ) (Real.pi * Real.exp (83 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1328_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1329 / 800 : ℝ) - (83 / 200 : ℝ)) ≤
      (50511835240836089 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1328_denomUpper
    linarith [hpThetaJensenCell1328_product_upper]
  have hi : (1 / (50511835240836089 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1329 / 800 : ℝ) - (83 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (50511835240836089 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (50511835240836089 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((83 / 200 : ℝ) - Real.pi * Real.exp (1329 / 800 : ℝ)) := by
    rw [show (83 / 200 : ℝ) - Real.pi * Real.exp (1329 / 800 : ℝ) =
      -(Real.pi * Real.exp (1329 / 800 : ℝ) - (83 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (83 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (83 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1328_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (50511835240836089 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1328_endpointUpper :
    hpThetaJensenKernelEndpointUpper (83 / 100 : ℝ) (1329 / 1600 : ℝ) ≤ (2017839 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1329 / 800 : ℝ)) (165432803155442641 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1329 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1328_product_upper
  have hD : (24731470646062853 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (83 / 50 : ℝ) - (1329 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1328_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1328_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (83 / 50 : ℝ) - (1329 / 3200 : ℝ)) ≤
      (1 / (24731470646062853 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (24731470646062853 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1329 / 3200 : ℝ) - Real.pi * Real.exp (83 / 50 : ℝ)) ≤
      (2 / (24731470646062853 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1329 / 3200 : ℝ) - Real.pi * Real.exp (83 / 50 : ℝ) =
      -(Real.pi * Real.exp (83 / 50 : ℝ) - (1329 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (165432803155442641 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (165432803155442641 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1328_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (83 / 100 : ℝ) (1329 / 1600 : ℝ)) :
    (98279 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2017839 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1328_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1328_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1329_leftExp :
    (10531778187 / 2000000000 : ℝ) ≤ Real.exp (1329 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1329 / 800 : ℝ) (42131408877 / 40000000000 : ℝ)
    (10531778187 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1329_rightExp :
    Real.exp (133 / 80 : ℝ) ≤ (52724755707 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (133 / 80 : ℝ) (1053326366683 / 1000000000000 : ℝ)
    (52724755707 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1329_denomUpper :
    Real.exp (161486598455821251 / 10000000000000000 : ℝ) ≤ (20620721498273539 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (161486598455821251 / 10000000000000000 : ℝ)
    (103524901391 / 62500000000 : ℝ) (20620721498273539 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1329_denomLower :
    (20192003740360571 / 2000000000 : ℝ) ≤ Real.exp (4031912512256713 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4031912512256713 / 250000000000000 : ℝ) (827655630313 /
    500000000000 : ℝ) (20192003740360571 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1329_product_lower :
    (4135818762256713 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1329 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1329_leftExp
    (by norm_num : (0 : ℝ) ≤ (10531778187 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1329_product_upper :
    Real.pi * Real.exp (133 / 80 : ℝ) ≤ (165639723455821251 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1329_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1329_endpointLower :
    (1930989 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1329 / 1600 : ℝ) (133 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4135818762256713 / 250000000000000 : ℝ) (Real.pi * Real.exp (1329 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1329_product_lower
  have hD : Real.exp (Real.pi * Real.exp (133 / 80 : ℝ) - (1329 / 3200 : ℝ)) ≤
      (20620721498273539 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1329_denomUpper
    linarith [hpThetaJensenCell1329_product_upper]
  have hi : (1 / (20620721498273539 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (133 / 80 : ℝ) - (1329 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (20620721498273539 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (20620721498273539 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1329 / 3200 : ℝ) - Real.pi * Real.exp (133 / 80 : ℝ)) := by
    rw [show (1329 / 3200 : ℝ) - Real.pi * Real.exp (133 / 80 : ℝ) =
      -(Real.pi * Real.exp (133 / 80 : ℝ) - (1329 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1329 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1329 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1329_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (20620721498273539 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1329_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1329 / 1600 : ℝ) (133 / 160 : ℝ) ≤ (99119 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (133 / 80 : ℝ)) (165639723455821251 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (133 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1329_product_upper
  have hD : (20192003740360571 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1329 / 800 : ℝ) - (133 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1329_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1329_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1329 / 800 : ℝ) - (133 / 320 : ℝ)) ≤
      (1 / (20192003740360571 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20192003740360571 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((133 / 320 : ℝ) - Real.pi * Real.exp (1329 / 800 : ℝ)) ≤
      (2 / (20192003740360571 / 2000000000 : ℝ) : ℝ) := by
    rw [show (133 / 320 : ℝ) - Real.pi * Real.exp (1329 / 800 : ℝ) =
      -(Real.pi * Real.exp (1329 / 800 : ℝ) - (133 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (165639723455821251 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (165639723455821251 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1329_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1329 / 1600 : ℝ) (133 / 160 : ℝ)) :
    (1930989 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (99119 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1329_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1329_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1330_leftExp :
    (6590594463 / 1250000000 : ℝ) ≤ Real.exp (133 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (133 / 80 : ℝ) (526663183341 / 500000000000 : ℝ)
    (6590594463 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1330_rightExp :
    Real.exp (1331 / 800 : ℝ) ≤ (2639535143 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1331 / 800 : ℝ) (131670939131 / 125000000000 : ℝ)
    (2639535143 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1330_denomUpper :
    Real.exp (8084532628502799 / 500000000000000 : ℝ) ≤ (105229090952856717 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (8084532628502799 / 500000000000000 : ℝ) (828727496597 /
    500000000000 : ℝ) (105229090952856717 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1330_denomLower :
    (4121545779981283 / 400000000 : ℝ) ≤ Real.exp (2523129620650637 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2523129620650637 / 156250000000000 : ℝ) (1656365798079 /
    1000000000000 : ℝ) (4121545779981283 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1330_product_lower :
    (2588119855025637 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (133 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1330_leftExp
    (by norm_num : (0 : ℝ) ≤ (6590594463 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1330_product_upper :
    Real.pi * Real.exp (1331 / 800 : ℝ) ≤ (8292345128502799 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1330_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1330_endpointLower :
    (948479 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (133 / 160 : ℝ) (1331 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2588119855025637 / 156250000000000 : ℝ) (Real.pi * Real.exp (133 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1330_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1331 / 800 : ℝ) - (133 / 320 : ℝ)) ≤
      (105229090952856717 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1330_denomUpper
    linarith [hpThetaJensenCell1330_product_upper]
  have hi : (1 / (105229090952856717 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1331 / 800 : ℝ) - (133 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (105229090952856717 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (105229090952856717 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((133 / 320 : ℝ) - Real.pi * Real.exp (1331 / 800 : ℝ)) := by
    rw [show (133 / 320 : ℝ) - Real.pi * Real.exp (1331 / 800 : ℝ) =
      -(Real.pi * Real.exp (1331 / 800 : ℝ) - (133 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (133 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (133 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1330_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (105229090952856717 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1330_endpointUpper :
    hpThetaJensenKernelEndpointUpper (133 / 160 : ℝ) (1331 / 1600 : ℝ) ≤ (1947493 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1331 / 800 : ℝ)) (8292345128502799 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1331 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1330_product_upper
  have hD : (4121545779981283 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (133 / 80 : ℝ) - (1331 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1330_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1330_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (133 / 80 : ℝ) - (1331 / 3200 : ℝ)) ≤
      (1 / (4121545779981283 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4121545779981283 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1331 / 3200 : ℝ) - Real.pi * Real.exp (133 / 80 : ℝ)) ≤
      (2 / (4121545779981283 / 400000000 : ℝ) : ℝ) := by
    rw [show (1331 / 3200 : ℝ) - Real.pi * Real.exp (133 / 80 : ℝ) =
      -(Real.pi * Real.exp (133 / 80 : ℝ) - (1331 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8292345128502799 / 500000000000000 : ℝ) ^ 2 - 6 *
      (8292345128502799 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1330_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (133 / 160 : ℝ) (1331 / 1600 : ℝ)) :
    (948479 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1947493 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1330_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1330_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1331_leftExp :
    (26395351429 / 5000000000 : ℝ) ≤ Real.exp (1331 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1331 / 800 : ℝ) (1053367513047 / 1000000000000 : ℝ)
    (26395351429 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1331_rightExp :
    Real.exp (333 / 200 : ℝ) ≤ (52856732499 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (333 / 200 : ℝ) (52670433051 / 50000000000 : ℝ)
    (52856732499 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1331_denomUpper :
    Real.exp (161894965821730907 / 10000000000000000 : ℝ) ≤ (107401174440415287 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (161894965821730907 / 10000000000000000 : ℝ)
    (1658513581161 / 1000000000000 : ℝ) (107401174440415287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1331_denomLower :
    (21032557617512963 / 2000000000 : ℝ) ≤ Real.exp (10105271860816871 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10105271860816871 / 625000000000000 : ℝ) (828711173941 /
    500000000000 : ℝ) (21032557617512963 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1331_product_lower :
    (10365428110816871 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1331 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1331_leftExp
    (by norm_num : (0 : ℝ) ≤ (26395351429 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1331_product_upper :
    Real.pi * Real.exp (333 / 200 : ℝ) ≤ (166054340821730907 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1331_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1331_endpointLower :
    (931739 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1331 / 1600 : ℝ) (333 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10365428110816871 / 625000000000000 : ℝ) (Real.pi * Real.exp (1331 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1331_product_lower
  have hD : Real.exp (Real.pi * Real.exp (333 / 200 : ℝ) - (1331 / 3200 : ℝ)) ≤
      (107401174440415287 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1331_denomUpper
    linarith [hpThetaJensenCell1331_product_upper]
  have hi : (1 / (107401174440415287 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (333 / 200 : ℝ) - (1331 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (107401174440415287 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (107401174440415287 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1331 / 3200 : ℝ) - Real.pi * Real.exp (333 / 200 : ℝ)) := by
    rw [show (1331 / 3200 : ℝ) - Real.pi * Real.exp (333 / 200 : ℝ) =
      -(Real.pi * Real.exp (333 / 200 : ℝ) - (1331 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1331 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1331 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1331_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (107401174440415287 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1331_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1331 / 1600 : ℝ) (333 / 400 : ℝ) ≤ (191317 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (333 / 200 : ℝ)) (166054340821730907 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (333 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1331_product_upper
  have hD : (21032557617512963 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1331 / 800 : ℝ) - (333 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1331_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1331_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1331 / 800 : ℝ) - (333 / 800 : ℝ)) ≤
      (1 / (21032557617512963 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21032557617512963 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((333 / 800 : ℝ) - Real.pi * Real.exp (1331 / 800 : ℝ)) ≤
      (2 / (21032557617512963 / 2000000000 : ℝ) : ℝ) := by
    rw [show (333 / 800 : ℝ) - Real.pi * Real.exp (1331 / 800 : ℝ) =
      -(Real.pi * Real.exp (1331 / 800 : ℝ) - (333 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (166054340821730907 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (166054340821730907 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1331_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1331 / 1600 : ℝ) (333 / 400 : ℝ)) :
    (931739 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (191317 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1331_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1331_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1332_leftExp :
    (3303545781 / 625000000 : ℝ) ≤ Real.exp (333 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (333 / 200 : ℝ) (1053408661019 / 1000000000000 : ℝ)
    (3303545781 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1332_rightExp :
    Real.exp (1333 / 800 : ℝ) ≤ (52922844727 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1333 / 800 : ℝ) (5267249053 / 5000000000 : ℝ)
    (52922844727 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1332_denomUpper :
    Real.exp (162099538534430111 / 10000000000000000 : ℝ) ≤ (109620937130421733 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (162099538534430111 / 10000000000000000 : ℝ)
    (829787095419 / 500000000000 : ℝ) (109620937130421733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1332_denomLower :
    (53666751121403441 / 5000000000 : ℝ) ≤ Real.exp (1264755179340419 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1264755179340419 / 78125000000000 : ℝ) (20731011433 /
    12500000000 : ℝ) (53666751121403441 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1332_product_lower :
    (1297299124652919 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (333 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1332_leftExp
    (by norm_num : (0 : ℝ) ≤ (3303545781 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1332_product_upper :
    Real.pi * Real.exp (1333 / 800 : ℝ) ≤ (166262038534430111 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1332_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1332_endpointLower :
    (1830541 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (333 / 400 : ℝ) (1333 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1297299124652919 / 78125000000000 : ℝ) (Real.pi * Real.exp (333 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1332_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1333 / 800 : ℝ) - (333 / 800 : ℝ)) ≤
      (109620937130421733 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1332_denomUpper
    linarith [hpThetaJensenCell1332_product_upper]
  have hi : (1 / (109620937130421733 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1333 / 800 : ℝ) - (333 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (109620937130421733 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (109620937130421733 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((333 / 800 : ℝ) - Real.pi * Real.exp (1333 / 800 : ℝ)) := by
    rw [show (333 / 800 : ℝ) - Real.pi * Real.exp (1333 / 800 : ℝ) =
      -(Real.pi * Real.exp (1333 / 800 : ℝ) - (333 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (333 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (333 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1332_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (109620937130421733 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1332_endpointUpper :
    hpThetaJensenKernelEndpointUpper (333 / 400 : ℝ) (1333 / 1600 : ℝ) ≤ (469851 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1333 / 800 : ℝ)) (166262038534430111 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1333 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1332_product_upper
  have hD : (53666751121403441 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (333 / 200 : ℝ) - (1333 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1332_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1332_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (333 / 200 : ℝ) - (1333 / 3200 : ℝ)) ≤
      (1 / (53666751121403441 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (53666751121403441 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1333 / 3200 : ℝ) - Real.pi * Real.exp (333 / 200 : ℝ)) ≤
      (2 / (53666751121403441 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1333 / 3200 : ℝ) - Real.pi * Real.exp (333 / 200 : ℝ) =
      -(Real.pi * Real.exp (333 / 200 : ℝ) - (1333 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (166262038534430111 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (166262038534430111 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1332_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (333 / 400 : ℝ) (1333 / 1600 : ℝ)) :
    (1830541 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (469851 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1332_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1332_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1333_leftExp :
    (13230711181 / 2500000000 : ℝ) ≤ Real.exp (1333 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1333 / 800 : ℝ) (1053449810599 / 1000000000000 : ℝ)
    (13230711181 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1333_rightExp :
    Real.exp (667 / 400 : ℝ) ≤ (26494519823 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (667 / 400 : ℝ) (1053490961787 / 1000000000000 : ℝ)
    (26494519823 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1333_denomUpper :
    Real.exp (81152185514298039 / 5000000000000000 : ℝ) ≤ (111889484421719551 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (81152185514298039 / 5000000000000000 : ℝ) (830318413451
    / 500000000000 : ℝ) (111889484421719551 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1333_denomLower :
    (13693983195298261 / 1250000000 : ℝ) ≤ Real.exp (5065413612567519 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5065413612567519 / 312500000000000 : ℝ) (414885375771 /
    250000000000 : ℝ) (13693983195298261 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1333_product_lower :
    (5195687050067519 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1333 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1333_leftExp
    (by norm_num : (0 : ℝ) ≤ (13230711181 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1333_product_upper :
    Real.pi * Real.exp (667 / 400 : ℝ) ≤ (83234998014298039 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1333_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1333_endpointLower :
    (1798139 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1333 / 1600 : ℝ) (667 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5195687050067519 / 312500000000000 : ℝ) (Real.pi * Real.exp (1333 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1333_product_lower
  have hD : Real.exp (Real.pi * Real.exp (667 / 400 : ℝ) - (1333 / 3200 : ℝ)) ≤
      (111889484421719551 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1333_denomUpper
    linarith [hpThetaJensenCell1333_product_upper]
  have hi : (1 / (111889484421719551 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (667 / 400 : ℝ) - (1333 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (111889484421719551 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (111889484421719551 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1333 / 3200 : ℝ) - Real.pi * Real.exp (667 / 400 : ℝ)) := by
    rw [show (1333 / 3200 : ℝ) - Real.pi * Real.exp (667 / 400 : ℝ) =
      -(Real.pi * Real.exp (667 / 400 : ℝ) - (1333 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1333 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1333 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1333_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (111889484421719551 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1333_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1333 / 1600 : ℝ) (667 / 800 : ℝ) ≤ (369237 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (667 / 400 : ℝ)) (83234998014298039 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (667 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1333_product_upper
  have hD : (13693983195298261 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1333 / 800 : ℝ) - (667 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1333_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1333_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1333 / 800 : ℝ) - (667 / 1600 : ℝ)) ≤
      (1 / (13693983195298261 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13693983195298261 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((667 / 1600 : ℝ) - Real.pi * Real.exp (1333 / 800 : ℝ)) ≤
      (2 / (13693983195298261 / 1250000000 : ℝ) : ℝ) := by
    rw [show (667 / 1600 : ℝ) - Real.pi * Real.exp (1333 / 800 : ℝ) =
      -(Real.pi * Real.exp (1333 / 800 : ℝ) - (667 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (83234998014298039 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (83234998014298039 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1333_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1333 / 1600 : ℝ) (667 / 800 : ℝ)) :
    (1798139 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (369237 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1333_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1333_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1334_leftExp :
    (52989039643 / 10000000000 : ℝ) ≤ Real.exp (667 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (667 / 400 : ℝ) (526745480893 / 500000000000 : ℝ)
    (52989039643 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1334_rightExp :
    Real.exp (267 / 160 : ℝ) ≤ (663191467 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (267 / 160 : ℝ) (1053532114581 / 1000000000000 : ℝ)
    (663191467 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1334_denomUpper :
    Real.exp (2031368295386931 / 125000000000000 : ℝ) ≤ (114207948701524413 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (2031368295386931 / 125000000000000 : ℝ) (207712686759 /
    125000000000 : ℝ) (114207948701524413 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1334_denomLower :
    (55909491356639869 / 5000000000 : ℝ) ≤ Real.exp (20287258503766457 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20287258503766457 / 1250000000000000 : ℝ) (830302058937
    / 500000000000 : ℝ) (55909491356639869 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1334_product_lower :
    (20808742878766457 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (667 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1334_leftExp
    (by norm_num : (0 : ℝ) ≤ (52989039643 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1334_product_upper :
    Real.pi * Real.exp (267 / 160 : ℝ) ≤ (2083477670386931 / 125000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1334_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1334_endpointLower :
    (353253 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (667 / 800 : ℝ) (267 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20808742878766457 / 1250000000000000 : ℝ) (Real.pi * Real.exp (667 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1334_product_lower
  have hD : Real.exp (Real.pi * Real.exp (267 / 160 : ℝ) - (667 / 1600 : ℝ)) ≤
      (114207948701524413 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1334_denomUpper
    linarith [hpThetaJensenCell1334_product_upper]
  have hi : (1 / (114207948701524413 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (267 / 160 : ℝ) - (667 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (114207948701524413 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (114207948701524413 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((667 / 1600 : ℝ) - Real.pi * Real.exp (267 / 160 : ℝ)) := by
    rw [show (667 / 1600 : ℝ) - Real.pi * Real.exp (267 / 160 : ℝ) =
      -(Real.pi * Real.exp (267 / 160 : ℝ) - (667 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (667 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (667 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1334_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (114207948701524413 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1334_endpointUpper :
    hpThetaJensenKernelEndpointUpper (667 / 800 : ℝ) (267 / 320 : ℝ) ≤ (362701 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (267 / 160 : ℝ)) (2083477670386931 / 125000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (267 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1334_product_upper
  have hD : (55909491356639869 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (667 / 400 : ℝ) - (267 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1334_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1334_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (667 / 400 : ℝ) - (267 / 640 : ℝ)) ≤
      (1 / (55909491356639869 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (55909491356639869 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((267 / 640 : ℝ) - Real.pi * Real.exp (667 / 400 : ℝ)) ≤
      (2 / (55909491356639869 / 5000000000 : ℝ) : ℝ) := by
    rw [show (267 / 640 : ℝ) - Real.pi * Real.exp (667 / 400 : ℝ) =
      -(Real.pi * Real.exp (667 / 400 : ℝ) - (267 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2083477670386931 / 125000000000000 : ℝ) ^ 2 - 6 *
      (2083477670386931 / 125000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1334_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (667 / 800 : ℝ) (267 / 320 : ℝ)) :
    (353253 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (362701 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1334_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1334_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1335_leftExp :
    (53055317357 / 10000000000 : ℝ) ≤ Real.exp (267 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (267 / 160 : ℝ) (52676605729 / 50000000000 : ℝ)
    (53055317357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1335_rightExp :
    Real.exp (167 / 100 : ℝ) ≤ (53121677973 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (167 / 100 : ℝ) (1053573268983 / 1000000000000 : ℝ)
    (53121677973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1335_denomUpper :
    Real.exp (162714816668230989 / 10000000000000000 : ℝ) ≤ (11657748997275939 / 1000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (162714816668230989 / 10000000000000000 : ℝ) (41569204927
    / 25000000000 : ℝ) (11657748997275939 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1335_denomLower :
    (57067992685265553 / 5000000000 : ℝ) ≤ Real.exp (20312895070776543 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20312895070776543 / 1250000000000000 : ℝ) (166166876373
    / 100000000000 : ℝ) (57067992685265553 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1335_product_lower :
    (20834770070776543 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (267 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1335_leftExp
    (by norm_num : (0 : ℝ) ≤ (53055317357 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1335_product_upper :
    Real.pi * Real.exp (167 / 100 : ℝ) ≤ (166886691668230989 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1335_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1335_endpointLower :
    (173491 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (267 / 320 : ℝ) (167 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20834770070776543 / 1250000000000000 : ℝ) (Real.pi * Real.exp (267 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1335_product_lower
  have hD : Real.exp (Real.pi * Real.exp (167 / 100 : ℝ) - (267 / 640 : ℝ)) ≤
      (11657748997275939 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1335_denomUpper
    linarith [hpThetaJensenCell1335_product_upper]
  have hi : (1 / (11657748997275939 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (167 / 100 : ℝ) - (267 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11657748997275939 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11657748997275939 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((267 / 640 : ℝ) - Real.pi * Real.exp (167 / 100 : ℝ)) := by
    rw [show (267 / 640 : ℝ) - Real.pi * Real.exp (167 / 100 : ℝ) =
      -(Real.pi * Real.exp (167 / 100 : ℝ) - (267 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (267 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (267 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1335_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11657748997275939 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1335_endpointUpper :
    hpThetaJensenKernelEndpointUpper (267 / 320 : ℝ) (167 / 200 : ℝ) ≤ (890679 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (167 / 100 : ℝ)) (166886691668230989 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (167 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1335_product_upper
  have hD : (57067992685265553 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (267 / 160 : ℝ) - (167 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1335_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1335_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (267 / 160 : ℝ) - (167 / 400 : ℝ)) ≤
      (1 / (57067992685265553 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57067992685265553 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((167 / 400 : ℝ) - Real.pi * Real.exp (267 / 160 : ℝ)) ≤
      (2 / (57067992685265553 / 5000000000 : ℝ) : ℝ) := by
    rw [show (167 / 400 : ℝ) - Real.pi * Real.exp (267 / 160 : ℝ) =
      -(Real.pi * Real.exp (267 / 160 : ℝ) - (167 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (166886691668230989 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (166886691668230989 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1335_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (267 / 320 : ℝ) (167 / 200 : ℝ)) :
    (173491 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (890679 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1335_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1335_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1336_leftExp :
    (5312167797 / 1000000000 : ℝ) ≤ Real.exp (167 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (167 / 100 : ℝ) (526786634491 / 500000000000 : ℝ)
    (5312167797 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1336_rightExp :
    Real.exp (1337 / 800 : ℝ) ≤ (5318812159 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1337 / 800 : ℝ) (1053614424993 / 1000000000000 : ℝ)
    (5318812159 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1336_denomUpper :
    Real.exp (16292043047029287 / 1000000000000000 : ℝ) ≤ (59499648294143057 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (16292043047029287 / 1000000000000000 : ℝ) (415959235171
    / 250000000000 : ℝ) (59499648294143057 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1336_denomLower :
    (5825201640046183 / 500000000 : ℝ) ≤ Real.exp (2033856419214103 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2033856419214103 / 125000000000000 : ℝ) (831367722691 /
    500000000000 : ℝ) (5825201640046183 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1336_product_lower :
    (2086082981714103 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (167 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1336_leftExp
    (by norm_num : (0 : ℝ) ≤ (5312167797 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1336_product_upper :
    Real.pi * Real.exp (1337 / 800 : ℝ) ≤ (16709543047029287 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1336_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1336_endpointLower :
    (1704067 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (167 / 200 : ℝ) (1337 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2086082981714103 / 125000000000000 : ℝ) (Real.pi * Real.exp (167 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1336_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1337 / 800 : ℝ) - (167 / 400 : ℝ)) ≤
      (59499648294143057 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1336_denomUpper
    linarith [hpThetaJensenCell1336_product_upper]
  have hi : (1 / (59499648294143057 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1337 / 800 : ℝ) - (167 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (59499648294143057 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (59499648294143057 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((167 / 400 : ℝ) - Real.pi * Real.exp (1337 / 800 : ℝ)) := by
    rw [show (167 / 400 : ℝ) - Real.pi * Real.exp (1337 / 800 : ℝ) =
      -(Real.pi * Real.exp (1337 / 800 : ℝ) - (167 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (167 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (167 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1336_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (59499648294143057 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1336_endpointUpper :
    hpThetaJensenKernelEndpointUpper (167 / 200 : ℝ) (1337 / 1600 : ℝ) ≤ (874867 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1337 / 800 : ℝ)) (16709543047029287 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1337 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1336_product_upper
  have hD : (5825201640046183 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (167 / 100 : ℝ) - (1337 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1336_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1336_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (167 / 100 : ℝ) - (1337 / 3200 : ℝ)) ≤
      (1 / (5825201640046183 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5825201640046183 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1337 / 3200 : ℝ) - Real.pi * Real.exp (167 / 100 : ℝ)) ≤
      (2 / (5825201640046183 / 500000000 : ℝ) : ℝ) := by
    rw [show (1337 / 3200 : ℝ) - Real.pi * Real.exp (167 / 100 : ℝ) =
      -(Real.pi * Real.exp (167 / 100 : ℝ) - (1337 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16709543047029287 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (16709543047029287 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1336_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (167 / 200 : ℝ) (1337 / 1600 : ℝ)) :
    (1704067 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (874867 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1336_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1336_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1337_leftExp :
    (53188121587 / 10000000000 : ℝ) ≤ Real.exp (1337 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1337 / 800 : ℝ) (32925450781 / 31250000000 : ℝ)
    (53188121587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1337_rightExp :
    Real.exp (669 / 400 : ℝ) ≤ (6656831039 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (669 / 400 : ℝ) (105365558261 / 100000000000 : ℝ)
    (6656831039 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1337_denomUpper :
    Real.exp (20390788169305127 / 1250000000000000 : ℝ) ≤ (7592161612187269 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20390788169305127 / 1250000000000000 : ℝ) (166490772959
    / 100000000000 : ℝ) (7592161612187269 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1337_denomLower :
    (3716384769127931 / 312500000 : ℝ) ≤ Real.exp (20364265909093313 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (20364265909093313 / 1250000000000000 : ℝ) (166380416759
    / 100000000000 : ℝ) (3716384769127931 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1337_product_lower :
    (20886922159093313 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1337 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1337_leftExp
    (by norm_num : (0 : ℝ) ≤ (53188121587 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1337_product_upper :
    Real.pi * Real.exp (669 / 400 : ℝ) ≤ (20913053794305127 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1337_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1337_endpointLower :
    (3269 / 19531250 : ℝ) ≤ hpThetaTraceEndpointLower (1337 / 1600 : ℝ) (669 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20886922159093313 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1337 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1337_product_lower
  have hD : Real.exp (Real.pi * Real.exp (669 / 400 : ℝ) - (1337 / 3200 : ℝ)) ≤
      (7592161612187269 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1337_denomUpper
    linarith [hpThetaJensenCell1337_product_upper]
  have hi : (1 / (7592161612187269 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (669 / 400 : ℝ) - (1337 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7592161612187269 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7592161612187269 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1337 / 3200 : ℝ) - Real.pi * Real.exp (669 / 400 : ℝ)) := by
    rw [show (1337 / 3200 : ℝ) - Real.pi * Real.exp (669 / 400 : ℝ) =
      -(Real.pi * Real.exp (669 / 400 : ℝ) - (1337 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1337 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1337 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1337_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7592161612187269 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1337_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1337 / 1600 : ℝ) (669 / 800 : ℝ) ≤ (1718627 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (669 / 400 : ℝ)) (20913053794305127 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (669 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1337_product_upper
  have hD : (3716384769127931 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1337 / 800 : ℝ) - (669 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1337_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1337_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1337 / 800 : ℝ) - (669 / 1600 : ℝ)) ≤
      (1 / (3716384769127931 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3716384769127931 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((669 / 1600 : ℝ) - Real.pi * Real.exp (1337 / 800 : ℝ)) ≤
      (2 / (3716384769127931 / 312500000 : ℝ) : ℝ) := by
    rw [show (669 / 1600 : ℝ) - Real.pi * Real.exp (1337 / 800 : ℝ) =
      -(Real.pi * Real.exp (1337 / 800 : ℝ) - (669 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20913053794305127 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (20913053794305127 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1337_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1337 / 1600 : ℝ) (669 / 800 : ℝ)) :
    (3269 / 19531250 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1718627 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1337_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1337_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1338_leftExp :
    (53254648309 / 10000000000 : ℝ) ≤ Real.exp (669 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (669 / 400 : ℝ) (1053655582609 / 1000000000000 : ℝ)
    (53254648309 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1338_rightExp :
    Real.exp (1339 / 800 : ℝ) ≤ (13330314561 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1339 / 800 : ℝ) (210739348367 / 200000000000 : ℝ)
    (13330314561 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1338_denomUpper :
    Real.exp (40833110412635673 / 2500000000000000 : ℝ) ≤ (24800920952240817 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (40833110412635673 / 2500000000000000 : ℝ) (832990284289
    / 500000000000 : ℝ) (24800920952240817 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1338_denomLower :
    (121398041278511483 / 10000000000 : ℝ) ≤ Real.exp (20390000261295991 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (20390000261295991 / 1250000000000000 : ℝ) (832437467529
    / 500000000000 : ℝ) (121398041278511483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1338_product_lower :
    (20913047136295991 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (669 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1338_leftExp
    (by norm_num : (0 : ℝ) ≤ (53254648309 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1338_product_upper :
    Real.pi * Real.exp (1339 / 800 : ℝ) ≤ (41878422912635673 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1338_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1338_endpointLower :
    (821943 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (669 / 800 : ℝ) (1339 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20913047136295991 / 1250000000000000 : ℝ) (Real.pi * Real.exp (669 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1338_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1339 / 800 : ℝ) - (669 / 1600 : ℝ)) ≤
      (24800920952240817 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1338_denomUpper
    linarith [hpThetaJensenCell1338_product_upper]
  have hi : (1 / (24800920952240817 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1339 / 800 : ℝ) - (669 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24800920952240817 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24800920952240817 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((669 / 1600 : ℝ) - Real.pi * Real.exp (1339 / 800 : ℝ)) := by
    rw [show (669 / 1600 : ℝ) - Real.pi * Real.exp (1339 / 800 : ℝ) =
      -(Real.pi * Real.exp (1339 / 800 : ℝ) - (669 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (669 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (669 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1338_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24800920952240817 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1338_endpointUpper :
    hpThetaJensenKernelEndpointUpper (669 / 800 : ℝ) (1339 / 1600 : ℝ) ≤ (1688029 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1339 / 800 : ℝ)) (41878422912635673 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1339 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1338_product_upper
  have hD : (121398041278511483 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (669 / 400 : ℝ) - (1339 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1338_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1338_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (669 / 400 : ℝ) - (1339 / 3200 : ℝ)) ≤
      (1 / (121398041278511483 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (121398041278511483 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1339 / 3200 : ℝ) - Real.pi * Real.exp (669 / 400 : ℝ)) ≤
      (2 / (121398041278511483 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1339 / 3200 : ℝ) - Real.pi * Real.exp (669 / 400 : ℝ) =
      -(Real.pi * Real.exp (669 / 400 : ℝ) - (1339 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41878422912635673 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (41878422912635673 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1338_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (669 / 800 : ℝ) (1339 / 1600 : ℝ)) :
    (821943 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1688029 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1338_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1338_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1339_leftExp :
    (26660629121 / 5000000000 : ℝ) ≤ Real.exp (1339 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1339 / 800 : ℝ) (526848370917 / 500000000000 : ℝ)
    (26660629121 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1339_rightExp :
    Real.exp (67 / 40 : ℝ) ≤ (13346987873 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 40 : ℝ) (263434475667 / 250000000000 : ℝ)
    (13346987873 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1339_denomUpper :
    Real.exp (40884709922901689 / 2500000000000000 : ℝ) ≤ (63295315624268749 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (40884709922901689 / 2500000000000000 : ℝ) (1667055462459
    / 1000000000000 : ℝ) (63295315624268749 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1339_denomLower :
    (123926465224438999 / 10000000000 : ℝ) ≤ Real.exp (10207883645187579 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10207883645187579 / 625000000000000 : ℝ) (208243469073 /
    125000000000 : ℝ) (123926465224438999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1339_product_lower :
    (10469602395187579 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1339 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1339_leftExp
    (by norm_num : (0 : ℝ) ≤ (26660629121 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1339_product_upper :
    Real.pi * Real.exp (67 / 40 : ℝ) ≤ (41930803672901689 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1339_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1339_endpointLower :
    (807267 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1339 / 1600 : ℝ) (67 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10469602395187579 / 625000000000000 : ℝ) (Real.pi * Real.exp (1339 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1339_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 40 : ℝ) - (1339 / 3200 : ℝ)) ≤
      (63295315624268749 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1339_denomUpper
    linarith [hpThetaJensenCell1339_product_upper]
  have hi : (1 / (63295315624268749 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 40 : ℝ) - (1339 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (63295315624268749 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (63295315624268749 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1339 / 3200 : ℝ) - Real.pi * Real.exp (67 / 40 : ℝ)) := by
    rw [show (1339 / 3200 : ℝ) - Real.pi * Real.exp (67 / 40 : ℝ) =
      -(Real.pi * Real.exp (67 / 40 : ℝ) - (1339 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1339 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1339 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1339_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (63295315624268749 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1339_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1339 / 1600 : ℝ) (67 / 80 : ℝ) ≤ (1657931 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 40 : ℝ)) (41930803672901689 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1339_product_upper
  have hD : (123926465224438999 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1339 / 800 : ℝ) - (67 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1339_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1339_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1339 / 800 : ℝ) - (67 / 160 : ℝ)) ≤
      (1 / (123926465224438999 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (123926465224438999 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 160 : ℝ) - Real.pi * Real.exp (1339 / 800 : ℝ)) ≤
      (2 / (123926465224438999 / 10000000000 : ℝ) : ℝ) := by
    rw [show (67 / 160 : ℝ) - Real.pi * Real.exp (1339 / 800 : ℝ) =
      -(Real.pi * Real.exp (1339 / 800 : ℝ) - (67 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41930803672901689 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (41930803672901689 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1339_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1339 / 1600 : ℝ) (67 / 80 : ℝ)) :
    (807267 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1657931 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1339_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1339_endpointUpper

def hpThetaJensenCellsBatch066Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1131727 / 5000000000 : ℝ)
  | 1 => (1112041 / 5000000000 : ℝ)
  | 2 => (2185339 / 10000000000 : ℝ)
  | 3 => (429443 / 2000000000 : ℝ)
  | 4 => (1054851 / 5000000000 : ℝ)
  | 5 => (2072791 / 10000000000 : ℝ)
  | 6 => (254559 / 1250000000 : ℝ)
  | 7 => (1000369 / 5000000000 : ℝ)
  | 8 => (98279 / 500000000 : ℝ)
  | 9 => (1930989 / 10000000000 : ℝ)
  | 10 => (948479 / 5000000000 : ℝ)
  | 11 => (931739 / 5000000000 : ℝ)
  | 12 => (1830541 / 10000000000 : ℝ)
  | 13 => (1798139 / 10000000000 : ℝ)
  | 14 => (353253 / 2000000000 : ℝ)
  | 15 => (173491 / 1000000000 : ℝ)
  | 16 => (1704067 / 10000000000 : ℝ)
  | 17 => (3269 / 19531250 : ℝ)
  | 18 => (821943 / 5000000000 : ℝ)
  | 19 => (807267 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch066Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1161579 / 5000000000 : ℝ)
  | 1 => (1141403 / 5000000000 : ℝ)
  | 2 => (2243097 / 10000000000 : ℝ)
  | 3 => (1102011 / 5000000000 : ℝ)
  | 4 => (2165571 / 10000000000 : ℝ)
  | 5 => (2127737 / 10000000000 : ℝ)
  | 6 => (2090509 / 10000000000 : ℝ)
  | 7 => (2053879 / 10000000000 : ℝ)
  | 8 => (2017839 / 10000000000 : ℝ)
  | 9 => (99119 / 500000000 : ℝ)
  | 10 => (1947493 / 10000000000 : ℝ)
  | 11 => (191317 / 1000000000 : ℝ)
  | 12 => (469851 / 2500000000 : ℝ)
  | 13 => (369237 / 2000000000 : ℝ)
  | 14 => (362701 / 2000000000 : ℝ)
  | 15 => (890679 / 5000000000 : ℝ)
  | 16 => (874867 / 5000000000 : ℝ)
  | 17 => (1718627 / 10000000000 : ℝ)
  | 18 => (1688029 / 10000000000 : ℝ)
  | 19 => (1657931 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch066_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch066Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch066Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1320_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1321_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1322_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1323_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1324_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1325_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1326_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1327_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1328_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1329_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1330_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1331_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1332_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1333_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1334_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1335_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1336_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1337_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1338_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1339_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper] at h ⊢
    exact h

end HodgeProofHP
