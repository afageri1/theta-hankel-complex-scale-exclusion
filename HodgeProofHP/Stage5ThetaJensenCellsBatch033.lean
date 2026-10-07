import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell660_leftExp :
    (22818807653 / 10000000000 : ℝ) ≤ Real.exp (33 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 40 : ℝ) (205223292189 / 200000000000 : ℝ)
    (22818807653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell660_rightExp :
    Real.exp (661 / 800 : ℝ) ≤ (11423674499 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (661 / 800 : ℝ) (1026156544403 / 1000000000000 : ℝ)
    (11423674499 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell660_denomUpper :
    Real.exp (34857285840336907 / 5000000000000000 : ℝ) ≤ (666109145221 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34857285840336907 / 5000000000000000 : ℝ) (62170526809 /
    50000000000 : ℝ) (666109145221 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell660_denomLower :
    (5279643046807 / 5000000000 : ℝ) ≤ Real.exp (8702719821525447 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8702719821525447 / 1250000000000000 : ℝ) (310762487121 /
    250000000000 : ℝ) (5279643046807 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell660_product_lower :
    (8960922946525447 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell660_leftExp
    (by norm_num : (0 : ℝ) ≤ (22818807653 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell660_product_upper :
    Real.pi * Real.exp (661 / 800 : ℝ) ≤ (35888535840336907 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell660_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell660_endpointLower :
    (1525189317 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 80 : ℝ) (661 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8960922946525447 / 1250000000000000 : ℝ) (Real.pi * Real.exp (33 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell660_product_lower
  have hD : Real.exp (Real.pi * Real.exp (661 / 800 : ℝ) - (33 / 160 : ℝ)) ≤
      (666109145221 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell660_denomUpper
    linarith [hpThetaJensenCell660_product_upper]
  have hi : (1 / (666109145221 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (661 / 800 : ℝ) - (33 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (666109145221 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (666109145221 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 160 : ℝ) - Real.pi * Real.exp (661 / 800 : ℝ)) := by
    rw [show (33 / 160 : ℝ) - Real.pi * Real.exp (661 / 800 : ℝ) =
      -(Real.pi * Real.exp (661 / 800 : ℝ) - (33 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 40 : ℝ)) := by
    have h := hpThetaJensenCell660_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (666109145221 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell660_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 80 : ℝ) (661 / 1600 : ℝ) ≤ (773920567 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (661 / 800 : ℝ)) (35888535840336907 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (661 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell660_product_upper
  have hD : (5279643046807 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 40 : ℝ) - (661 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell660_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell660_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 40 : ℝ) - (661 / 3200 : ℝ)) ≤
      (1 / (5279643046807 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5279643046807 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((661 / 3200 : ℝ) - Real.pi * Real.exp (33 / 40 : ℝ)) ≤
      (2 / (5279643046807 / 5000000000 : ℝ) : ℝ) := by
    rw [show (661 / 3200 : ℝ) - Real.pi * Real.exp (33 / 40 : ℝ) =
      -(Real.pi * Real.exp (33 / 40 : ℝ) - (661 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35888535840336907 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (35888535840336907 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell660_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 80 : ℝ) (661 / 1600 : ℝ)) :
    (1525189317 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (773920567 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell660_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell660_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell661_leftExp :
    (22847348997 / 10000000000 : ℝ) ≤ Real.exp (661 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (661 / 800 : ℝ) (513078272201 / 500000000000 : ℝ)
    (22847348997 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell661_rightExp :
    Real.exp (331 / 400 : ℝ) ≤ (11437963021 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (331 / 400 : ℝ) (513098314713 / 500000000000 : ℝ)
    (11437963021 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell661_denomUpper :
    Real.exp (34900612061032453 / 5000000000000000 : ℝ) ≤ (10750499582029 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34900612061032453 / 5000000000000000 : ℝ) (621873641759
    / 500000000000 : ℝ) (10750499582029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell661_denomLower :
    (10651062974827 / 10000000000 : ℝ) ≤ Real.exp (8713537353772903 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8713537353772903 / 1250000000000000 : ℝ) (1243386162267
    / 1000000000000 : ℝ) (10651062974827 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell661_product_lower :
    (8972131103772903 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (661 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell661_leftExp
    (by norm_num : (0 : ℝ) ≤ (22847348997 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell661_product_upper :
    Real.pi * Real.exp (331 / 400 : ℝ) ≤ (35933424561032453 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell661_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell661_endpointLower :
    (3032632279 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (661 / 1600 : ℝ) (331 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8972131103772903 / 1250000000000000 : ℝ) (Real.pi * Real.exp (661 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell661_product_lower
  have hD : Real.exp (Real.pi * Real.exp (331 / 400 : ℝ) - (661 / 3200 : ℝ)) ≤
      (10750499582029 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell661_denomUpper
    linarith [hpThetaJensenCell661_product_upper]
  have hi : (1 / (10750499582029 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (331 / 400 : ℝ) - (661 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10750499582029 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10750499582029 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((661 / 3200 : ℝ) - Real.pi * Real.exp (331 / 400 : ℝ)) := by
    rw [show (661 / 3200 : ℝ) - Real.pi * Real.exp (331 / 400 : ℝ) =
      -(Real.pi * Real.exp (331 / 400 : ℝ) - (661 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (661 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (661 / 800 : ℝ)) := by
    have h := hpThetaJensenCell661_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10750499582029 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell661_endpointUpper :
    hpThetaJensenKernelEndpointUpper (661 / 1600 : ℝ) (331 / 800 : ℝ) ≤ (769426317 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (331 / 400 : ℝ)) (35933424561032453 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (331 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell661_product_upper
  have hD : (10651062974827 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (661 / 800 : ℝ) - (331 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell661_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell661_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (661 / 800 : ℝ) - (331 / 1600 : ℝ)) ≤
      (1 / (10651062974827 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10651062974827 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((331 / 1600 : ℝ) - Real.pi * Real.exp (661 / 800 : ℝ)) ≤
      (2 / (10651062974827 / 10000000000 : ℝ) : ℝ) := by
    rw [show (331 / 1600 : ℝ) - Real.pi * Real.exp (661 / 800 : ℝ) =
      -(Real.pi * Real.exp (661 / 800 : ℝ) - (331 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35933424561032453 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (35933424561032453 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell661_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (661 / 1600 : ℝ) (331 / 800 : ℝ)) :
    (3032632279 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (769426317 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell661_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell661_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell662_leftExp :
    (571898151 / 250000000 : ℝ) ≤ Real.exp (331 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (331 / 400 : ℝ) (41047865177 / 40000000000 : ℝ)
    (571898151 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell662_rightExp :
    Real.exp (663 / 800 : ℝ) ≤ (22904538829 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (663 / 800 : ℝ) (205247343203 / 200000000000 : ℝ)
    (22904538829 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell662_denomUpper :
    Real.exp (69887988853414597 / 10000000000000000 : ℝ) ≤ (5422090915457 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69887988853414597 / 10000000000000000 : ℝ) (311021139653
    / 250000000000 : ℝ) (5422090915457 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell662_denomLower :
    (429750321383 / 400000000 : ℝ) ≤ Real.exp (218109222624549 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (218109222624549 / 31250000000000 : ℝ) (7773268143 /
    6250000000 : ℝ) (429750321383 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell662_product_lower :
    (224583831999549 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (331 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell662_leftExp
    (by norm_num : (0 : ℝ) ≤ (571898151 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell662_product_upper :
    Real.pi * Real.exp (663 / 800 : ℝ) ≤ (71956738853414597 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell662_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell662_endpointLower :
    (3014953739 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (331 / 800 : ℝ) (663 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (224583831999549 / 31250000000000 : ℝ) (Real.pi * Real.exp (331 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell662_product_lower
  have hD : Real.exp (Real.pi * Real.exp (663 / 800 : ℝ) - (331 / 1600 : ℝ)) ≤
      (5422090915457 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell662_denomUpper
    linarith [hpThetaJensenCell662_product_upper]
  have hi : (1 / (5422090915457 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (663 / 800 : ℝ) - (331 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5422090915457 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5422090915457 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((331 / 1600 : ℝ) - Real.pi * Real.exp (663 / 800 : ℝ)) := by
    rw [show (331 / 1600 : ℝ) - Real.pi * Real.exp (663 / 800 : ℝ) =
      -(Real.pi * Real.exp (663 / 800 : ℝ) - (331 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (331 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (331 / 400 : ℝ)) := by
    have h := hpThetaJensenCell662_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5422090915457 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell662_endpointUpper :
    hpThetaJensenKernelEndpointUpper (331 / 800 : ℝ) (663 / 1600 : ℝ) ≤ (191237297 / 625000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (663 / 800 : ℝ)) (71956738853414597 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (663 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell662_product_upper
  have hD : (429750321383 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (331 / 400 : ℝ) - (663 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell662_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell662_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (331 / 400 : ℝ) - (663 / 3200 : ℝ)) ≤
      (1 / (429750321383 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (429750321383 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((663 / 3200 : ℝ) - Real.pi * Real.exp (331 / 400 : ℝ)) ≤
      (2 / (429750321383 / 400000000 : ℝ) : ℝ) := by
    rw [show (663 / 3200 : ℝ) - Real.pi * Real.exp (331 / 400 : ℝ) =
      -(Real.pi * Real.exp (331 / 400 : ℝ) - (663 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (71956738853414597 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (71956738853414597 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell662_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (331 / 800 : ℝ) (663 / 1600 : ℝ)) :
    (3014953739 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (191237297 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell662_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell662_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell663_leftExp :
    (22904538827 / 10000000000 : ℝ) ≤ Real.exp (663 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (663 / 800 : ℝ) (513118358007 / 500000000000 : ℝ)
    (22904538827 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell663_rightExp :
    Real.exp (83 / 100 : ℝ) ≤ (22933187403 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83 / 100 : ℝ) (1026276804169 / 1000000000000 : ℝ)
    (22933187403 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell663_denomUpper :
    Real.exp (69974866012952979 / 10000000000000000 : ℝ) ≤ (5469401714903 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69974866012952979 / 10000000000000000 : ℝ)
    (1244422362379 / 1000000000000 : ℝ) (5469401714903 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell663_denomLower :
    (541869075251 / 500000000 : ℝ) ≤ Real.exp (8735214492824073 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8735214492824073 / 1250000000000000 : ℝ) (1244060171251
    / 1000000000000 : ℝ) (541869075251 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell663_product_lower :
    (8994589492824073 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (663 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell663_leftExp
    (by norm_num : (0 : ℝ) ≤ (22904538827 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell663_product_upper :
    Real.pi * Real.exp (83 / 100 : ℝ) ≤ (72046741012952979 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell663_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell663_endpointLower :
    (599468599 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (663 / 1600 : ℝ) (83 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8994589492824073 / 1250000000000000 : ℝ) (Real.pi * Real.exp (663 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell663_product_lower
  have hD : Real.exp (Real.pi * Real.exp (83 / 100 : ℝ) - (663 / 3200 : ℝ)) ≤
      (5469401714903 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell663_denomUpper
    linarith [hpThetaJensenCell663_product_upper]
  have hi : (1 / (5469401714903 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (83 / 100 : ℝ) - (663 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5469401714903 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5469401714903 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((663 / 3200 : ℝ) - Real.pi * Real.exp (83 / 100 : ℝ)) := by
    rw [show (663 / 3200 : ℝ) - Real.pi * Real.exp (83 / 100 : ℝ) =
      -(Real.pi * Real.exp (83 / 100 : ℝ) - (663 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (663 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (663 / 800 : ℝ)) := by
    have h := hpThetaJensenCell663_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5469401714903 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell663_endpointUpper :
    hpThetaJensenKernelEndpointUpper (663 / 1600 : ℝ) (83 / 200 : ℝ) ≤ (30419567 / 100000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (83 / 100 : ℝ)) (72046741012952979 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (83 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell663_product_upper
  have hD : (541869075251 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (663 / 800 : ℝ) - (83 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell663_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell663_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (663 / 800 : ℝ) - (83 / 400 : ℝ)) ≤
      (1 / (541869075251 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (541869075251 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((83 / 400 : ℝ) - Real.pi * Real.exp (663 / 800 : ℝ)) ≤
      (2 / (541869075251 / 500000000 : ℝ) : ℝ) := by
    rw [show (83 / 400 : ℝ) - Real.pi * Real.exp (663 / 800 : ℝ) =
      -(Real.pi * Real.exp (663 / 800 : ℝ) - (83 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72046741012952979 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (72046741012952979 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell663_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (663 / 1600 : ℝ) (83 / 200 : ℝ)) :
    (599468599 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (30419567 / 100000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell663_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell663_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell664_leftExp :
    (11466593701 / 5000000000 : ℝ) ≤ Real.exp (83 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (83 / 100 : ℝ) (128284600521 / 125000000000 : ℝ)
    (11466593701 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell664_rightExp :
    Real.exp (133 / 160 : ℝ) ≤ (5740467953 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (133 / 160 : ℝ) (102631689389 / 100000000000 : ℝ)
    (5740467953 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell664_denomUpper :
    Real.exp (17515463937869129 / 2500000000000000 : ℝ) ≤ (5517187439537 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17515463937869129 / 2500000000000000 : ℝ) (1244760695789
    / 1000000000000 : ℝ) (5517187439537 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell664_denomLower :
    (10931943739643 / 10000000000 : ℝ) ≤ Real.exp (4373037067288999 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4373037067288999 / 625000000000000 : ℝ) (622198984149 /
    500000000000 : ℝ) (10931943739643 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell664_product_lower :
    (4502919879788999 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (83 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell664_leftExp
    (by norm_num : (0 : ℝ) ≤ (11466593701 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell664_product_upper :
    Real.pi * Real.exp (133 / 160 : ℝ) ≤ (18034213937869129 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell664_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell664_endpointLower :
    (1489900011 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 200 : ℝ) (133 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4502919879788999 / 625000000000000 : ℝ) (Real.pi * Real.exp (83 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell664_product_lower
  have hD : Real.exp (Real.pi * Real.exp (133 / 160 : ℝ) - (83 / 400 : ℝ)) ≤
      (5517187439537 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell664_denomUpper
    linarith [hpThetaJensenCell664_product_upper]
  have hi : (1 / (5517187439537 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (133 / 160 : ℝ) - (83 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5517187439537 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5517187439537 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((83 / 400 : ℝ) - Real.pi * Real.exp (133 / 160 : ℝ)) := by
    rw [show (83 / 400 : ℝ) - Real.pi * Real.exp (133 / 160 : ℝ) =
      -(Real.pi * Real.exp (133 / 160 : ℝ) - (83 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (83 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (83 / 100 : ℝ)) := by
    have h := hpThetaJensenCell664_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5517187439537 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell664_endpointUpper :
    hpThetaJensenKernelEndpointUpper (83 / 200 : ℝ) (133 / 320 : ℝ) ≤ (604837019 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (133 / 160 : ℝ)) (18034213937869129 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (133 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell664_product_upper
  have hD : (10931943739643 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (83 / 100 : ℝ) - (133 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell664_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell664_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (83 / 100 : ℝ) - (133 / 640 : ℝ)) ≤
      (1 / (10931943739643 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10931943739643 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((133 / 640 : ℝ) - Real.pi * Real.exp (83 / 100 : ℝ)) ≤
      (2 / (10931943739643 / 10000000000 : ℝ) : ℝ) := by
    rw [show (133 / 640 : ℝ) - Real.pi * Real.exp (83 / 100 : ℝ) =
      -(Real.pi * Real.exp (83 / 100 : ℝ) - (133 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18034213937869129 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (18034213937869129 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell664_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (83 / 200 : ℝ) (133 / 320 : ℝ)) :
    (1489900011 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (604837019 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell664_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell664_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell665_leftExp :
    (2296187181 / 1000000000 : ℝ) ≤ Real.exp (133 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (133 / 160 : ℝ) (1026316893889 / 1000000000000 : ℝ)
    (2296187181 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell665_rightExp :
    Real.exp (333 / 400 : ℝ) ≤ (11495296049 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (333 / 400 : ℝ) (1026356985177 / 1000000000000 : ℝ)
    (11495296049 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell665_denomUpper :
    Real.exp (35074479100466057 / 5000000000000000 : ℝ) ≤ (11130906784931 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35074479100466057 / 5000000000000000 : ℝ) (249019911947
    / 200000000000 : ℝ) (11130906784931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell665_denomLower :
    (2205491044197 / 2000000000 : ℝ) ≤ Real.exp (875694784791519 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (875694784791519 / 125000000000000 : ℝ) (1244736294951 /
    1000000000000 : ℝ) (2205491044197 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell665_product_lower :
    (901710409791519 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (133 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell665_leftExp
    (by norm_num : (0 : ℝ) ≤ (2296187181 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell665_product_upper :
    Real.pi * Real.exp (333 / 400 : ℝ) ≤ (36113541600466057 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell665_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell665_endpointLower :
    (1851453 / 6250000 : ℝ) ≤ hpThetaTraceEndpointLower (133 / 320 : ℝ) (333 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (901710409791519 / 125000000000000 : ℝ) (Real.pi * Real.exp (133 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell665_product_lower
  have hD : Real.exp (Real.pi * Real.exp (333 / 400 : ℝ) - (133 / 640 : ℝ)) ≤
      (11130906784931 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell665_denomUpper
    linarith [hpThetaJensenCell665_product_upper]
  have hi : (1 / (11130906784931 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (333 / 400 : ℝ) - (133 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11130906784931 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11130906784931 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((133 / 640 : ℝ) - Real.pi * Real.exp (333 / 400 : ℝ)) := by
    rw [show (133 / 640 : ℝ) - Real.pi * Real.exp (333 / 400 : ℝ) =
      -(Real.pi * Real.exp (333 / 400 : ℝ) - (133 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (133 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (133 / 160 : ℝ)) := by
    have h := hpThetaJensenCell665_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11130906784931 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell665_endpointUpper :
    hpThetaJensenKernelEndpointUpper (133 / 320 : ℝ) (333 / 800 : ℝ) ≤ (3006481911 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (333 / 400 : ℝ)) (36113541600466057 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (333 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell665_product_upper
  have hD : (2205491044197 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (133 / 160 : ℝ) - (333 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell665_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell665_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (133 / 160 : ℝ) - (333 / 1600 : ℝ)) ≤
      (1 / (2205491044197 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2205491044197 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((333 / 1600 : ℝ) - Real.pi * Real.exp (133 / 160 : ℝ)) ≤
      (2 / (2205491044197 / 2000000000 : ℝ) : ℝ) := by
    rw [show (333 / 1600 : ℝ) - Real.pi * Real.exp (133 / 160 : ℝ) =
      -(Real.pi * Real.exp (133 / 160 : ℝ) - (333 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36113541600466057 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (36113541600466057 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell665_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (133 / 320 : ℝ) (333 / 800 : ℝ)) :
    (1851453 / 6250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3006481911 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell665_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell665_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell666_leftExp :
    (22990592097 / 10000000000 : ℝ) ≤ Real.exp (333 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (333 / 400 : ℝ) (128294623147 / 125000000000 : ℝ)
    (22990592097 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell666_rightExp :
    Real.exp (667 / 800 : ℝ) ≤ (23019348307 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (667 / 800 : ℝ) (1026397078029 / 1000000000000 : ℝ)
    (23019348307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell666_denomUpper :
    Real.exp (70236173505833051 / 10000000000000000 : ℝ) ≤ (11228409897959 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (70236173505833051 / 10000000000000000 : ℝ) (311359738791
    / 250000000000 : ℝ) (11228409897959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell666_denomLower :
    (2780981640891 / 2500000000 : ℝ) ≤ Real.exp (8767835650899803 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8767835650899803 / 1250000000000000 : ℝ) (311268788039 /
    250000000000 : ℝ) (2780981640891 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell666_product_lower :
    (9028382525899803 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (333 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell666_leftExp
    (by norm_num : (0 : ℝ) ≤ (22990592097 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell666_product_upper :
    Real.pi * Real.exp (667 / 800 : ℝ) ≤ (72317423505833051 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell666_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell666_endpointLower :
    (1472458651 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (333 / 800 : ℝ) (667 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9028382525899803 / 1250000000000000 : ℝ) (Real.pi * Real.exp (333 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell666_product_lower
  have hD : Real.exp (Real.pi * Real.exp (667 / 800 : ℝ) - (333 / 1600 : ℝ)) ≤
      (11228409897959 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell666_denomUpper
    linarith [hpThetaJensenCell666_product_upper]
  have hi : (1 / (11228409897959 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (667 / 800 : ℝ) - (333 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11228409897959 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11228409897959 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((333 / 1600 : ℝ) - Real.pi * Real.exp (667 / 800 : ℝ)) := by
    rw [show (333 / 1600 : ℝ) - Real.pi * Real.exp (667 / 800 : ℝ) =
      -(Real.pi * Real.exp (667 / 800 : ℝ) - (333 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (333 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (333 / 400 : ℝ)) := by
    have h := hpThetaJensenCell666_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11228409897959 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell666_endpointUpper :
    hpThetaJensenKernelEndpointUpper (333 / 800 : ℝ) (667 / 1600 : ℝ) ≤ (1494423563 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (667 / 800 : ℝ)) (72317423505833051 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (667 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell666_product_upper
  have hD : (2780981640891 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (333 / 400 : ℝ) - (667 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell666_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell666_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (333 / 400 : ℝ) - (667 / 3200 : ℝ)) ≤
      (1 / (2780981640891 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2780981640891 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((667 / 3200 : ℝ) - Real.pi * Real.exp (333 / 400 : ℝ)) ≤
      (2 / (2780981640891 / 2500000000 : ℝ) : ℝ) := by
    rw [show (667 / 3200 : ℝ) - Real.pi * Real.exp (333 / 400 : ℝ) =
      -(Real.pi * Real.exp (333 / 400 : ℝ) - (667 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72317423505833051 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (72317423505833051 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell666_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (333 / 800 : ℝ) (667 / 1600 : ℝ)) :
    (1472458651 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1494423563 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell666_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell666_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell667_leftExp :
    (4603869661 / 2000000000 : ℝ) ≤ Real.exp (667 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (667 / 800 : ℝ) (256599269507 / 250000000000 : ℝ)
    (4603869661 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell667_rightExp :
    Real.exp (167 / 200 : ℝ) ≤ (5762035121 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (167 / 200 : ℝ) (32076161639 / 31250000000 : ℝ)
    (5762035121 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell667_denomUpper :
    Real.exp (17580875451887753 / 2500000000000000 : ℝ) ≤ (1415861887031 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17580875451887753 / 2500000000000000 : ℝ) (1245778883011
    / 1000000000000 : ℝ) (1415861887031 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell667_denomLower :
    (11221368496129 / 10000000000 : ℝ) ≤ Real.exp (1755747512005039 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1755747512005039 / 250000000000000 : ℝ) (1245414540807 /
    1000000000000 : ℝ) (11221368496129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell667_product_lower :
    (1807935012005039 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (667 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell667_leftExp
    (by norm_num : (0 : ℝ) ≤ (4603869661 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell667_product_upper :
    Real.pi * Real.exp (167 / 200 : ℝ) ≤ (18101969201887753 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell667_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell667_endpointLower :
    (2927577501 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (667 / 1600 : ℝ) (167 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1807935012005039 / 250000000000000 : ℝ) (Real.pi * Real.exp (667 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell667_product_lower
  have hD : Real.exp (Real.pi * Real.exp (167 / 200 : ℝ) - (667 / 3200 : ℝ)) ≤
      (1415861887031 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell667_denomUpper
    linarith [hpThetaJensenCell667_product_upper]
  have hi : (1 / (1415861887031 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (167 / 200 : ℝ) - (667 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1415861887031 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1415861887031 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((667 / 3200 : ℝ) - Real.pi * Real.exp (167 / 200 : ℝ)) := by
    rw [show (667 / 3200 : ℝ) - Real.pi * Real.exp (167 / 200 : ℝ) =
      -(Real.pi * Real.exp (167 / 200 : ℝ) - (667 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (667 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (667 / 800 : ℝ)) := by
    have h := hpThetaJensenCell667_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1415861887031 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell667_endpointUpper :
    hpThetaJensenKernelEndpointUpper (667 / 1600 : ℝ) (167 / 400 : ℝ) ≤ (594256143 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (167 / 200 : ℝ)) (18101969201887753 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (167 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell667_product_upper
  have hD : (11221368496129 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (667 / 800 : ℝ) - (167 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell667_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell667_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (667 / 800 : ℝ) - (167 / 800 : ℝ)) ≤
      (1 / (11221368496129 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11221368496129 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((167 / 800 : ℝ) - Real.pi * Real.exp (667 / 800 : ℝ)) ≤
      (2 / (11221368496129 / 10000000000 : ℝ) : ℝ) := by
    rw [show (167 / 800 : ℝ) - Real.pi * Real.exp (667 / 800 : ℝ) =
      -(Real.pi * Real.exp (667 / 800 : ℝ) - (167 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18101969201887753 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (18101969201887753 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell667_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (667 / 1600 : ℝ) (167 / 400 : ℝ)) :
    (2927577501 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (594256143 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell667_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell667_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell668_leftExp :
    (11524070241 / 5000000000 : ℝ) ≤ Real.exp (167 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (167 / 200 : ℝ) (1026437172447 / 1000000000000 : ℝ)
    (11524070241 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell668_rightExp :
    Real.exp (669 / 800 : ℝ) ≤ (23076968673 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (669 / 800 : ℝ) (1026477268433 / 1000000000000 : ℝ)
    (23076968673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell668_denomUpper :
    Real.exp (70410943244316089 / 10000000000000000 : ℝ) ≤ (5713186693333 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (70410943244316089 / 10000000000000000 : ℝ) (623059672099
    / 500000000000 : ℝ) (5713186693333 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell668_denomLower :
    (2829947975273 / 2500000000 : ℝ) ≤ Real.exp (4394826797070459 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4394826797070459 / 625000000000000 : ℝ) (622877230939 /
    500000000000 : ℝ) (2829947975273 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell668_product_lower :
    (4525490859570459 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (167 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell668_leftExp
    (by norm_num : (0 : ℝ) ≤ (11524070241 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell668_product_upper :
    Real.pi * Real.exp (669 / 800 : ℝ) ≤ (72498443244316089 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell668_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell668_endpointLower :
    (291030537 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (167 / 400 : ℝ) (669 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4525490859570459 / 625000000000000 : ℝ) (Real.pi * Real.exp (167 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell668_product_lower
  have hD : Real.exp (Real.pi * Real.exp (669 / 800 : ℝ) - (167 / 800 : ℝ)) ≤
      (5713186693333 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell668_denomUpper
    linarith [hpThetaJensenCell668_product_upper]
  have hi : (1 / (5713186693333 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (669 / 800 : ℝ) - (167 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5713186693333 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5713186693333 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((167 / 800 : ℝ) - Real.pi * Real.exp (669 / 800 : ℝ)) := by
    rw [show (167 / 800 : ℝ) - Real.pi * Real.exp (669 / 800 : ℝ) =
      -(Real.pi * Real.exp (669 / 800 : ℝ) - (167 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (167 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (167 / 200 : ℝ)) := by
    have h := hpThetaJensenCell668_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5713186693333 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell668_endpointUpper :
    hpThetaJensenKernelEndpointUpper (167 / 400 : ℝ) (669 / 1600 : ℝ) ≤ (369222831 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (669 / 800 : ℝ)) (72498443244316089 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (669 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell668_product_upper
  have hD : (2829947975273 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (167 / 200 : ℝ) - (669 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell668_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell668_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (167 / 200 : ℝ) - (669 / 3200 : ℝ)) ≤
      (1 / (2829947975273 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2829947975273 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((669 / 3200 : ℝ) - Real.pi * Real.exp (167 / 200 : ℝ)) ≤
      (2 / (2829947975273 / 2500000000 : ℝ) : ℝ) := by
    rw [show (669 / 3200 : ℝ) - Real.pi * Real.exp (167 / 200 : ℝ) =
      -(Real.pi * Real.exp (167 / 200 : ℝ) - (669 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72498443244316089 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (72498443244316089 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell668_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (167 / 400 : ℝ) (669 / 1600 : ℝ)) :
    (291030537 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (369222831 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell668_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell668_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell669_leftExp :
    (23076968671 / 10000000000 : ℝ) ≤ Real.exp (669 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (669 / 800 : ℝ) (64154829277 / 62500000000 : ℝ)
    (23076968671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell669_rightExp :
    Real.exp (67 / 80 : ℝ) ≤ (23105832921 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 80 : ℝ) (205303473197 / 200000000000 : ℝ)
    (23105832921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell669_denomUpper :
    Real.exp (70498497963783153 / 10000000000000000 : ℝ) ≤ (2881713980603 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (70498497963783153 / 10000000000000000 : ℝ) (155807542461
    / 125000000000 : ℝ) (2881713980603 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell669_denomLower :
    (11419207774987 / 10000000000 : ℝ) ≤ Real.exp (8800583770133029 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8800583770133029 / 1250000000000000 : ℝ) (1246094916279
    / 1000000000000 : ℝ) (11419207774987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell669_product_lower :
    (9062302520133029 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (669 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell669_leftExp
    (by norm_num : (0 : ℝ) ≤ (23076968671 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell669_product_upper :
    Real.pi * Real.exp (67 / 80 : ℝ) ≤ (72589122963783153 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell669_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell669_endpointLower :
    (2893100877 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (669 / 1600 : ℝ) (67 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9062302520133029 / 1250000000000000 : ℝ) (Real.pi * Real.exp (669 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell669_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 80 : ℝ) - (669 / 3200 : ℝ)) ≤
      (2881713980603 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell669_denomUpper
    linarith [hpThetaJensenCell669_product_upper]
  have hi : (1 / (2881713980603 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 80 : ℝ) - (669 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2881713980603 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2881713980603 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((669 / 3200 : ℝ) - Real.pi * Real.exp (67 / 80 : ℝ)) := by
    rw [show (669 / 3200 : ℝ) - Real.pi * Real.exp (67 / 80 : ℝ) =
      -(Real.pi * Real.exp (67 / 80 : ℝ) - (669 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (669 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (669 / 800 : ℝ)) := by
    have h := hpThetaJensenCell669_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2881713980603 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell669_endpointUpper :
    hpThetaJensenKernelEndpointUpper (669 / 1600 : ℝ) (67 / 160 : ℝ) ≤ (2936352899 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 80 : ℝ)) (72589122963783153 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell669_product_upper
  have hD : (11419207774987 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (669 / 800 : ℝ) - (67 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell669_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell669_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (669 / 800 : ℝ) - (67 / 320 : ℝ)) ≤
      (1 / (11419207774987 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11419207774987 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 320 : ℝ) - Real.pi * Real.exp (669 / 800 : ℝ)) ≤
      (2 / (11419207774987 / 10000000000 : ℝ) : ℝ) := by
    rw [show (67 / 320 : ℝ) - Real.pi * Real.exp (669 / 800 : ℝ) =
      -(Real.pi * Real.exp (669 / 800 : ℝ) - (67 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72589122963783153 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (72589122963783153 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell669_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (669 / 1600 : ℝ) (67 / 160 : ℝ)) :
    (2893100877 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2936352899 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell669_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell669_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell670_leftExp :
    (23105832919 / 10000000000 : ℝ) ≤ Real.exp (67 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 80 : ℝ) (32078667687 / 31250000000 : ℝ)
    (23105832919 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell670_rightExp :
    Real.exp (671 / 800 : ℝ) ≤ (23134733271 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (671 / 800 : ℝ) (1026557465103 / 1000000000000 : ℝ)
    (23134733271 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell670_denomUpper :
    Real.exp (70586166101040703 / 10000000000000000 : ℝ) ≤ (1453544247303 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (70586166101040703 / 10000000000000000 : ℝ) (249360374079
    / 200000000000 : ℝ) (1453544247303 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell670_denomLower :
    (11519627263723 / 10000000000 : ℝ) ≤ Real.exp (8811528106458381 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8811528106458381 / 1250000000000000 : ℝ) (311608976243 /
    250000000000 : ℝ) (11519627263723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell670_product_lower :
    (9073637481458381 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell670_leftExp
    (by norm_num : (0 : ℝ) ≤ (23105832919 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell670_product_upper :
    Real.pi * Real.exp (671 / 800 : ℝ) ≤ (72679916101040703 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell670_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell670_endpointLower :
    (1437981997 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 160 : ℝ) (671 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9073637481458381 / 1250000000000000 : ℝ) (Real.pi * Real.exp (67 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell670_product_lower
  have hD : Real.exp (Real.pi * Real.exp (671 / 800 : ℝ) - (67 / 320 : ℝ)) ≤
      (1453544247303 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell670_denomUpper
    linarith [hpThetaJensenCell670_product_upper]
  have hi : (1 / (1453544247303 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (671 / 800 : ℝ) - (67 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1453544247303 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1453544247303 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 320 : ℝ) - Real.pi * Real.exp (671 / 800 : ℝ)) := by
    rw [show (67 / 320 : ℝ) - Real.pi * Real.exp (671 / 800 : ℝ) =
      -(Real.pi * Real.exp (671 / 800 : ℝ) - (67 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 80 : ℝ)) := by
    have h := hpThetaJensenCell670_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1453544247303 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell670_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 160 : ℝ) (671 / 1600 : ℝ) ≤ (583798287 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (671 / 800 : ℝ)) (72679916101040703 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (671 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell670_product_upper
  have hD : (11519627263723 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 80 : ℝ) - (671 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell670_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell670_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 80 : ℝ) - (671 / 3200 : ℝ)) ≤
      (1 / (11519627263723 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11519627263723 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((671 / 3200 : ℝ) - Real.pi * Real.exp (67 / 80 : ℝ)) ≤
      (2 / (11519627263723 / 10000000000 : ℝ) : ℝ) := by
    rw [show (671 / 3200 : ℝ) - Real.pi * Real.exp (67 / 80 : ℝ) =
      -(Real.pi * Real.exp (67 / 80 : ℝ) - (671 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72679916101040703 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (72679916101040703 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell670_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 160 : ℝ) (671 / 1600 : ℝ)) :
    (1437981997 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (583798287 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell670_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell670_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell671_leftExp :
    (23134733269 / 10000000000 : ℝ) ≤ Real.exp (671 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (671 / 800 : ℝ) (513278732551 / 500000000000 : ℝ)
    (23134733269 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell671_rightExp :
    Real.exp (21 / 25 : ℝ) ≤ (23163669769 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 25 : ℝ) (1026597565787 / 1000000000000 : ℝ)
    (23163669769 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell671_denomUpper :
    Real.exp (70673947800602017 / 10000000000000000 : ℝ) ≤ (5865439489217 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (70673947800602017 / 10000000000000000 : ℝ) (124714393727
    / 100000000000 : ℝ) (5865439489217 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell671_denomLower :
    (11621061635163 / 10000000000 : ℝ) ≤ Real.exp (8822486620003031 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8822486620003031 / 1250000000000000 : ℝ) (1246777428871
    / 1000000000000 : ℝ) (11621061635163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell671_product_lower :
    (9084986620003031 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (671 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell671_leftExp
    (by norm_num : (0 : ℝ) ≤ (23134733269 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell671_product_upper :
    Real.pi * Real.exp (21 / 25 : ℝ) ≤ (72770822800602017 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell671_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell671_endpointLower :
    (571778937 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (671 / 1600 : ℝ) (21 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9084986620003031 / 1250000000000000 : ℝ) (Real.pi * Real.exp (671 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell671_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 25 : ℝ) - (671 / 3200 : ℝ)) ≤
      (5865439489217 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell671_denomUpper
    linarith [hpThetaJensenCell671_product_upper]
  have hi : (1 / (5865439489217 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 25 : ℝ) - (671 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5865439489217 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5865439489217 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((671 / 3200 : ℝ) - Real.pi * Real.exp (21 / 25 : ℝ)) := by
    rw [show (671 / 3200 : ℝ) - Real.pi * Real.exp (21 / 25 : ℝ) =
      -(Real.pi * Real.exp (21 / 25 : ℝ) - (671 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (671 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (671 / 800 : ℝ)) := by
    have h := hpThetaJensenCell671_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5865439489217 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell671_endpointUpper :
    hpThetaJensenKernelEndpointUpper (671 / 1600 : ℝ) (21 / 50 : ℝ) ≤ (1450849113 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 25 : ℝ)) (72770822800602017 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell671_product_upper
  have hD : (11621061635163 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (671 / 800 : ℝ) - (21 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell671_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell671_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (671 / 800 : ℝ) - (21 / 100 : ℝ)) ≤
      (1 / (11621061635163 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11621061635163 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 100 : ℝ) - Real.pi * Real.exp (671 / 800 : ℝ)) ≤
      (2 / (11621061635163 / 10000000000 : ℝ) : ℝ) := by
    rw [show (21 / 100 : ℝ) - Real.pi * Real.exp (671 / 800 : ℝ) =
      -(Real.pi * Real.exp (671 / 800 : ℝ) - (21 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (72770822800602017 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (72770822800602017 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell671_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (671 / 1600 : ℝ) (21 / 50 : ℝ)) :
    (571778937 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1450849113 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell671_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell671_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell672_leftExp :
    (23163669767 / 10000000000 : ℝ) ≤ Real.exp (21 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 25 : ℝ) (513298782893 / 500000000000 : ℝ)
    (23163669767 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell672_rightExp :
    Real.exp (673 / 800 : ℝ) ≤ (1159632123 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (673 / 800 : ℝ) (513318834019 / 500000000000 : ℝ)
    (1159632123 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell672_denomUpper :
    Real.exp (3538092160191939 / 500000000000000 : ℝ) ≤ (11834442483279 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3538092160191939 / 500000000000000 : ℝ) (249497308251 /
    200000000000 : ℝ) (11834442483279 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell672_denomLower :
    (11723522306169 / 10000000000 : ℝ) ≤ Real.exp (8833459328831133 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8833459328831133 / 1250000000000000 : ℝ) (38972484029 /
    31250000000 : ℝ) (11723522306169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell672_product_lower :
    (9096349953831133 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell672_leftExp
    (by norm_num : (0 : ℝ) ≤ (23163669767 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell672_product_upper :
    Real.pi * Real.exp (673 / 800 : ℝ) ≤ (3643092160191939 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell672_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell672_endpointLower :
    (2841892917 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 50 : ℝ) (673 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9096349953831133 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell672_product_lower
  have hD : Real.exp (Real.pi * Real.exp (673 / 800 : ℝ) - (21 / 100 : ℝ)) ≤
      (11834442483279 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell672_denomUpper
    linarith [hpThetaJensenCell672_product_upper]
  have hi : (1 / (11834442483279 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (673 / 800 : ℝ) - (21 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11834442483279 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11834442483279 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 100 : ℝ) - Real.pi * Real.exp (673 / 800 : ℝ)) := by
    rw [show (21 / 100 : ℝ) - Real.pi * Real.exp (673 / 800 : ℝ) =
      -(Real.pi * Real.exp (673 / 800 : ℝ) - (21 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 25 : ℝ)) := by
    have h := hpThetaJensenCell672_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11834442483279 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell672_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 50 : ℝ) (673 / 1600 : ℝ) ≤ (1442236619 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (673 / 800 : ℝ)) (3643092160191939 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (673 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell672_product_upper
  have hD : (11723522306169 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 25 : ℝ) - (673 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell672_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell672_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 25 : ℝ) - (673 / 3200 : ℝ)) ≤
      (1 / (11723522306169 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11723522306169 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((673 / 3200 : ℝ) - Real.pi * Real.exp (21 / 25 : ℝ)) ≤
      (2 / (11723522306169 / 10000000000 : ℝ) : ℝ) := by
    rw [show (673 / 3200 : ℝ) - Real.pi * Real.exp (21 / 25 : ℝ) =
      -(Real.pi * Real.exp (21 / 25 : ℝ) - (673 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3643092160191939 / 500000000000000 : ℝ) ^ 2 - 6 *
      (3643092160191939 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell672_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 50 : ℝ) (673 / 1600 : ℝ)) :
    (2841892917 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1442236619 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell672_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell672_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell673_leftExp :
    (23192642459 / 10000000000 : ℝ) ≤ Real.exp (673 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (673 / 800 : ℝ) (1026637668037 / 1000000000000 : ℝ)
    (23192642459 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell673_rightExp :
    Real.exp (337 / 400 : ℝ) ≤ (2322165139 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (337 / 400 : ℝ) (205335554371 / 200000000000 : ℝ)
    (2322165139 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell673_denomUpper :
    Real.exp (7084985245526427 / 1000000000000000 : ℝ) ≤ (5969528099679 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7084985245526427 / 1000000000000000 : ℝ) (249565936661 /
    200000000000 : ℝ) (5969528099679 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell673_denomLower :
    (2365404166733 / 2000000000 : ℝ) ≤ Real.exp (8844446251006841 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8844446251006841 / 1250000000000000 : ℝ) (77966380381 /
    62500000000 : ℝ) (2365404166733 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell673_product_lower :
    (9107727501006841 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (673 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell673_leftExp
    (by norm_num : (0 : ℝ) ≤ (23192642459 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell673_product_upper :
    Real.pi * Real.exp (337 / 400 : ℝ) ≤ (7295297745526427 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell673_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell673_endpointLower :
    (706239663 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (673 / 1600 : ℝ) (337 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9107727501006841 / 1250000000000000 : ℝ) (Real.pi * Real.exp (673 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell673_product_lower
  have hD : Real.exp (Real.pi * Real.exp (337 / 400 : ℝ) - (673 / 3200 : ℝ)) ≤
      (5969528099679 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell673_denomUpper
    linarith [hpThetaJensenCell673_product_upper]
  have hi : (1 / (5969528099679 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (337 / 400 : ℝ) - (673 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5969528099679 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5969528099679 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((673 / 3200 : ℝ) - Real.pi * Real.exp (337 / 400 : ℝ)) := by
    rw [show (673 / 3200 : ℝ) - Real.pi * Real.exp (337 / 400 : ℝ) =
      -(Real.pi * Real.exp (337 / 400 : ℝ) - (673 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (673 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (673 / 800 : ℝ)) := by
    have h := hpThetaJensenCell673_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5969528099679 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell673_endpointUpper :
    hpThetaJensenKernelEndpointUpper (673 / 1600 : ℝ) (337 / 800 : ℝ) ≤ (1433658217 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (337 / 400 : ℝ)) (7295297745526427 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (337 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell673_product_upper
  have hD : (2365404166733 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (673 / 800 : ℝ) - (337 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell673_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell673_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (673 / 800 : ℝ) - (337 / 1600 : ℝ)) ≤
      (1 / (2365404166733 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2365404166733 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((337 / 1600 : ℝ) - Real.pi * Real.exp (673 / 800 : ℝ)) ≤
      (2 / (2365404166733 / 2000000000 : ℝ) : ℝ) := by
    rw [show (337 / 1600 : ℝ) - Real.pi * Real.exp (673 / 800 : ℝ) =
      -(Real.pi * Real.exp (673 / 800 : ℝ) - (337 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7295297745526427 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (7295297745526427 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell673_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (673 / 1600 : ℝ) (337 / 800 : ℝ)) :
    (706239663 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1433658217 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell673_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell673_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell674_leftExp :
    (5805412847 / 2500000000 : ℝ) ≤ Real.exp (337 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (337 / 400 : ℝ) (513338885927 / 500000000000 : ℝ)
    (5805412847 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell674_rightExp :
    Real.exp (27 / 32 : ℝ) ≤ (23250696603 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 32 : ℝ) (513358938619 / 500000000000 : ℝ)
    (23250696603 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell674_denomUpper :
    Real.exp (70937975693108579 / 10000000000000000 : ℝ) ≤ (6022365984463 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (70937975693108579 / 10000000000000000 : ℝ) (24963467287
    / 20000000000 : ℝ) (6022365984463 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell674_denomLower :
    (5965784452737 / 5000000000 : ℝ) ≤ Real.exp (2213861850854053 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2213861850854053 / 312500000000000 : ℝ) (1247805221293 /
    1000000000000 : ℝ) (5965784452737 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell674_product_lower :
    (2279779819604053 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (337 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell674_leftExp
    (by norm_num : (0 : ℝ) ≤ (5805412847 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell674_product_upper :
    Real.pi * Real.exp (27 / 32 : ℝ) ≤ (73044225693108579 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell674_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell674_endpointLower :
    (1404045927 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (337 / 800 : ℝ) (27 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2279779819604053 / 312500000000000 : ℝ) (Real.pi * Real.exp (337 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell674_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 32 : ℝ) - (337 / 1600 : ℝ)) ≤
      (6022365984463 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell674_denomUpper
    linarith [hpThetaJensenCell674_product_upper]
  have hi : (1 / (6022365984463 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 32 : ℝ) - (337 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6022365984463 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6022365984463 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((337 / 1600 : ℝ) - Real.pi * Real.exp (27 / 32 : ℝ)) := by
    rw [show (337 / 1600 : ℝ) - Real.pi * Real.exp (27 / 32 : ℝ) =
      -(Real.pi * Real.exp (27 / 32 : ℝ) - (337 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (337 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (337 / 400 : ℝ)) := by
    have h := hpThetaJensenCell674_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6022365984463 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell674_endpointUpper :
    hpThetaJensenKernelEndpointUpper (337 / 800 : ℝ) (27 / 64 : ℝ) ≤ (2850227779 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 32 : ℝ)) (73044225693108579 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell674_product_upper
  have hD : (5965784452737 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (337 / 400 : ℝ) - (27 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell674_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell674_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (337 / 400 : ℝ) - (27 / 128 : ℝ)) ≤
      (1 / (5965784452737 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5965784452737 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 128 : ℝ) - Real.pi * Real.exp (337 / 400 : ℝ)) ≤
      (2 / (5965784452737 / 5000000000 : ℝ) : ℝ) := by
    rw [show (27 / 128 : ℝ) - Real.pi * Real.exp (337 / 400 : ℝ) =
      -(Real.pi * Real.exp (337 / 400 : ℝ) - (27 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (73044225693108579 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (73044225693108579 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell674_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (337 / 800 : ℝ) (27 / 64 : ℝ)) :
    (1404045927 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2850227779 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell674_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell674_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell675_leftExp :
    (11625348301 / 5000000000 : ℝ) ≤ Real.exp (27 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 32 : ℝ) (1026717877237 / 1000000000000 : ℝ)
    (11625348301 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell675_rightExp :
    Real.exp (169 / 200 : ℝ) ≤ (23279778147 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (169 / 200 : ℝ) (1026757984189 / 1000000000000 : ℝ)
    (23279778147 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell675_denomUpper :
    Real.exp (71026213068168171 / 10000000000000000 : ℝ) ≤ (2430296359127 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71026213068168171 / 10000000000000000 : ℝ) (312129396343
    / 250000000000 : ℝ) (2430296359127 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell675_denomLower :
    (6018589185981 / 5000000000 : ℝ) ≤ Real.exp (4433231402454399 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4433231402454399 / 625000000000000 : ℝ) (2496297791 /
    2000000000 : ℝ) (6018589185981 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell675_product_lower :
    (4565262652454399 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell675_leftExp
    (by norm_num : (0 : ℝ) ≤ (11625348301 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell675_product_upper :
    Real.pi * Real.exp (169 / 200 : ℝ) ≤ (73135588068168171 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell675_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell675_endpointLower :
    (1395646241 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 64 : ℝ) (169 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4565262652454399 / 625000000000000 : ℝ) (Real.pi * Real.exp (27 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell675_product_lower
  have hD : Real.exp (Real.pi * Real.exp (169 / 200 : ℝ) - (27 / 128 : ℝ)) ≤
      (2430296359127 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell675_denomUpper
    linarith [hpThetaJensenCell675_product_upper]
  have hi : (1 / (2430296359127 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (169 / 200 : ℝ) - (27 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2430296359127 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2430296359127 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 128 : ℝ) - Real.pi * Real.exp (169 / 200 : ℝ)) := by
    rw [show (27 / 128 : ℝ) - Real.pi * Real.exp (169 / 200 : ℝ) =
      -(Real.pi * Real.exp (169 / 200 : ℝ) - (27 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 32 : ℝ)) := by
    have h := hpThetaJensenCell675_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2430296359127 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell675_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 64 : ℝ) (169 / 400 : ℝ) ≤ (1416603617 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (169 / 200 : ℝ)) (73135588068168171 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (169 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell675_product_upper
  have hD : (6018589185981 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 32 : ℝ) - (169 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell675_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell675_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 32 : ℝ) - (169 / 800 : ℝ)) ≤
      (1 / (6018589185981 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6018589185981 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((169 / 800 : ℝ) - Real.pi * Real.exp (27 / 32 : ℝ)) ≤
      (2 / (6018589185981 / 5000000000 : ℝ) : ℝ) := by
    rw [show (169 / 800 : ℝ) - Real.pi * Real.exp (27 / 32 : ℝ) =
      -(Real.pi * Real.exp (27 / 32 : ℝ) - (169 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (73135588068168171 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (73135588068168171 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell675_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 64 : ℝ) (169 / 400 : ℝ)) :
    (1395646241 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1416603617 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell675_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell675_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell676_leftExp :
    (4655955629 / 2000000000 : ℝ) ≤ Real.exp (169 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (169 / 200 : ℝ) (256689496047 / 250000000000 : ℝ)
    (4655955629 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell676_rightExp :
    Real.exp (677 / 800 : ℝ) ≤ (364201501 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (677 / 800 : ℝ) (513399046353 / 500000000000 : ℝ)
    (364201501 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell676_denomUpper :
    Real.exp (1111165073631093 / 156250000000000 : ℝ) ≤ (1532414726023 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1111165073631093 / 156250000000000 : ℝ) (1248862347281 /
    1000000000000 : ℝ) (1532414726023 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell676_denomLower :
    (12143861213889 / 10000000000 : ℝ) ≤ Real.exp (1775498494552671 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1775498494552671 / 250000000000000 : ℝ) (1248493109649 /
    1000000000000 : ℝ) (12143861213889 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell676_product_lower :
    (1828389119552671 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (169 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell676_leftExp
    (by norm_num : (0 : ℝ) ≤ (4655955629 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell676_product_upper :
    Real.pi * Real.exp (677 / 800 : ℝ) ≤ (1144172886131093 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell676_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell676_endpointLower :
    (2774560497 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (169 / 400 : ℝ) (677 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1828389119552671 / 250000000000000 : ℝ) (Real.pi * Real.exp (169 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell676_product_lower
  have hD : Real.exp (Real.pi * Real.exp (677 / 800 : ℝ) - (169 / 800 : ℝ)) ≤
      (1532414726023 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell676_denomUpper
    linarith [hpThetaJensenCell676_product_upper]
  have hi : (1 / (1532414726023 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (677 / 800 : ℝ) - (169 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1532414726023 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1532414726023 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((169 / 800 : ℝ) - Real.pi * Real.exp (677 / 800 : ℝ)) := by
    rw [show (169 / 800 : ℝ) - Real.pi * Real.exp (677 / 800 : ℝ) =
      -(Real.pi * Real.exp (677 / 800 : ℝ) - (169 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (169 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (169 / 200 : ℝ)) := by
    have h := hpThetaJensenCell676_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1532414726023 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell676_endpointUpper :
    hpThetaJensenKernelEndpointUpper (169 / 400 : ℝ) (677 / 1600 : ℝ) ≤ (1408127379 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (677 / 800 : ℝ)) (1144172886131093 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (677 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell676_product_upper
  have hD : (12143861213889 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (169 / 200 : ℝ) - (677 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell676_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell676_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (169 / 200 : ℝ) - (677 / 3200 : ℝ)) ≤
      (1 / (12143861213889 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12143861213889 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((677 / 3200 : ℝ) - Real.pi * Real.exp (169 / 200 : ℝ)) ≤
      (2 / (12143861213889 / 10000000000 : ℝ) : ℝ) := by
    rw [show (677 / 3200 : ℝ) - Real.pi * Real.exp (169 / 200 : ℝ) =
      -(Real.pi * Real.exp (169 / 200 : ℝ) - (677 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1144172886131093 / 156250000000000 : ℝ) ^ 2 - 6 *
      (1144172886131093 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell676_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (169 / 400 : ℝ) (677 / 1600 : ℝ)) :
    (2774560497 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1408127379 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell676_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell676_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell677_leftExp :
    (11654448031 / 5000000000 : ℝ) ≤ Real.exp (677 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (677 / 800 : ℝ) (205359618541 / 200000000000 : ℝ)
    (11654448031 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell677_rightExp :
    Real.exp (339 / 400 : ℝ) ≤ (11669025201 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (339 / 400 : ℝ) (102683820279 / 100000000000 : ℝ)
    (11669025201 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell677_denomUpper :
    Real.exp (35601515388285193 / 5000000000000000 : ℝ) ≤ (12368252307873 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35601515388285193 / 5000000000000000 : ℝ) (624603825531
    / 500000000000 : ℝ) (12368252307873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell677_denomLower :
    (3062907390863 / 2500000000 : ℝ) ≤ Real.exp (4444268212325669 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4444268212325669 / 625000000000000 : ℝ) (624418932343 /
    500000000000 : ℝ) (3062907390863 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell677_product_lower :
    (4576690087325669 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (677 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell677_leftExp
    (by norm_num : (0 : ℝ) ≤ (11654448031 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell677_product_upper :
    Real.pi * Real.exp (339 / 400 : ℝ) ≤ (36659327888285193 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell677_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell677_endpointLower :
    (1378947927 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (677 / 1600 : ℝ) (339 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4576690087325669 / 625000000000000 : ℝ) (Real.pi * Real.exp (677 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell677_product_lower
  have hD : Real.exp (Real.pi * Real.exp (339 / 400 : ℝ) - (677 / 3200 : ℝ)) ≤
      (12368252307873 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell677_denomUpper
    linarith [hpThetaJensenCell677_product_upper]
  have hi : (1 / (12368252307873 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (339 / 400 : ℝ) - (677 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12368252307873 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12368252307873 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((677 / 3200 : ℝ) - Real.pi * Real.exp (339 / 400 : ℝ)) := by
    rw [show (677 / 3200 : ℝ) - Real.pi * Real.exp (339 / 400 : ℝ) =
      -(Real.pi * Real.exp (339 / 400 : ℝ) - (677 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (677 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (677 / 800 : ℝ)) := by
    have h := hpThetaJensenCell677_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12368252307873 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell677_endpointUpper :
    hpThetaJensenKernelEndpointUpper (677 / 1600 : ℝ) (339 / 800 : ℝ) ≤ (2799370311 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (339 / 400 : ℝ)) (36659327888285193 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (339 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell677_product_upper
  have hD : (3062907390863 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (677 / 800 : ℝ) - (339 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell677_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell677_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (677 / 800 : ℝ) - (339 / 1600 : ℝ)) ≤
      (1 / (3062907390863 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3062907390863 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((339 / 1600 : ℝ) - Real.pi * Real.exp (677 / 800 : ℝ)) ≤
      (2 / (3062907390863 / 2500000000 : ℝ) : ℝ) := by
    rw [show (339 / 1600 : ℝ) - Real.pi * Real.exp (677 / 800 : ℝ) =
      -(Real.pi * Real.exp (677 / 800 : ℝ) - (339 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36659327888285193 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (36659327888285193 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell677_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (677 / 1600 : ℝ) (339 / 800 : ℝ)) :
    (1378947927 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2799370311 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell677_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell677_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell678_leftExp :
    (29172563 / 12500000 : ℝ) ≤ Real.exp (339 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (339 / 400 : ℝ) (1026838202789 / 1000000000000 : ℝ)
    (29172563 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell678_rightExp :
    Real.exp (679 / 800 : ℝ) ≤ (11683620603 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (679 / 800 : ℝ) (1026878314441 / 1000000000000 : ℝ)
    (11683620603 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell678_denomUpper :
    Real.exp (35645805701040579 / 5000000000000000 : ℝ) ≤ (779893608467 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35645805701040579 / 5000000000000000 : ℝ) (624776748831
    / 500000000000 : ℝ) (779893608467 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell678_denomLower :
    (12360495710211 / 10000000000 : ℝ) ≤ Real.exp (11124493348787 / 1562500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11124493348787 / 1562500000000 : ℝ) (1249183161583 /
    1000000000000 : ℝ) (12360495710211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell678_product_lower :
    (11456036317537 / 1562500000000 : ℝ) ≤ Real.pi * Real.exp (339 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell678_leftExp
    (by norm_num : (0 : ℝ) ≤ (29172563 / 12500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell678_product_upper :
    Real.pi * Real.exp (679 / 800 : ℝ) ≤ (36705180701040579 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell678_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell678_endpointLower :
    (274129851 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (339 / 800 : ℝ) (679 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11456036317537 / 1562500000000 : ℝ) (Real.pi * Real.exp (339 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell678_product_lower
  have hD : Real.exp (Real.pi * Real.exp (679 / 800 : ℝ) - (339 / 1600 : ℝ)) ≤
      (779893608467 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell678_denomUpper
    linarith [hpThetaJensenCell678_product_upper]
  have hi : (1 / (779893608467 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (679 / 800 : ℝ) - (339 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (779893608467 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (779893608467 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((339 / 1600 : ℝ) - Real.pi * Real.exp (679 / 800 : ℝ)) := by
    rw [show (339 / 1600 : ℝ) - Real.pi * Real.exp (679 / 800 : ℝ) =
      -(Real.pi * Real.exp (679 / 800 : ℝ) - (339 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (339 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (339 / 400 : ℝ)) := by
    have h := hpThetaJensenCell678_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (779893608467 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell678_endpointUpper :
    hpThetaJensenKernelEndpointUpper (339 / 800 : ℝ) (679 / 1600 : ℝ) ≤ (2782553849 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (679 / 800 : ℝ)) (36705180701040579 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (679 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell678_product_upper
  have hD : (12360495710211 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (339 / 400 : ℝ) - (679 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell678_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell678_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (339 / 400 : ℝ) - (679 / 3200 : ℝ)) ≤
      (1 / (12360495710211 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12360495710211 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((679 / 3200 : ℝ) - Real.pi * Real.exp (339 / 400 : ℝ)) ≤
      (2 / (12360495710211 / 10000000000 : ℝ) : ℝ) := by
    rw [show (679 / 3200 : ℝ) - Real.pi * Real.exp (339 / 400 : ℝ) =
      -(Real.pi * Real.exp (339 / 400 : ℝ) - (679 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36705180701040579 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (36705180701040579 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell678_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (339 / 800 : ℝ) (679 / 1600 : ℝ)) :
    (274129851 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2782553849 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell678_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell678_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell679_leftExp :
    (5841810301 / 2500000000 : ℝ) ≤ Real.exp (679 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (679 / 800 : ℝ) (25671957861 / 25000000000 : ℝ)
    (5841810301 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell679_rightExp :
    Real.exp (17 / 20 : ℝ) ≤ (584911713 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 20 : ℝ) (513459213829 / 500000000000 : ℝ)
    (584911713 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell679_denomUpper :
    Real.exp (1784507668178809 / 250000000000000 : ℝ) ≤ (12589466682371 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1784507668178809 / 250000000000000 : ℝ) (62494994401 /
    50000000000 : ℝ) (12589466682371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell679_denomLower :
    (3117618021939 / 2500000000 : ℝ) ≤ Real.exp (2227666813392399 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2227666813392399 / 312500000000000 : ℝ) (1249529001289 /
    1000000000000 : ℝ) (3117618021939 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell679_product_lower :
    (2294073063392399 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (679 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell679_leftExp
    (by norm_num : (0 : ℝ) ≤ (5841810301 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell679_product_upper :
    Real.pi * Real.exp (17 / 20 : ℝ) ≤ (1837554543178809 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell679_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell679_endpointLower :
    (1362384211 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (679 / 1600 : ℝ) (17 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2294073063392399 / 312500000000000 : ℝ) (Real.pi * Real.exp (679 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell679_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 20 : ℝ) - (679 / 3200 : ℝ)) ≤
      (12589466682371 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell679_denomUpper
    linarith [hpThetaJensenCell679_product_upper]
  have hi : (1 / (12589466682371 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 20 : ℝ) - (679 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12589466682371 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12589466682371 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((679 / 3200 : ℝ) - Real.pi * Real.exp (17 / 20 : ℝ)) := by
    rw [show (679 / 3200 : ℝ) - Real.pi * Real.exp (17 / 20 : ℝ) =
      -(Real.pi * Real.exp (17 / 20 : ℝ) - (679 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (679 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (679 / 800 : ℝ)) := by
    have h := hpThetaJensenCell679_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12589466682371 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell679_endpointUpper :
    hpThetaJensenKernelEndpointUpper (679 / 1600 : ℝ) (17 / 40 : ℝ) ≤ (1382902663 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 20 : ℝ)) (1837554543178809 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell679_product_upper
  have hD : (3117618021939 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (679 / 800 : ℝ) - (17 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell679_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell679_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (679 / 800 : ℝ) - (17 / 80 : ℝ)) ≤
      (1 / (3117618021939 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3117618021939 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 80 : ℝ) - Real.pi * Real.exp (679 / 800 : ℝ)) ≤
      (2 / (3117618021939 / 2500000000 : ℝ) : ℝ) := by
    rw [show (17 / 80 : ℝ) - Real.pi * Real.exp (679 / 800 : ℝ) =
      -(Real.pi * Real.exp (679 / 800 : ℝ) - (17 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1837554543178809 / 250000000000000 : ℝ) ^ 2 - 6 *
      (1837554543178809 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell679_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (679 / 1600 : ℝ) (17 / 40 : ℝ)) :
    (1362384211 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1382902663 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell679_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell679_endpointUpper

def hpThetaJensenCellsBatch033Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1525189317 / 5000000000 : ℝ)
  | 1 => (3032632279 / 10000000000 : ℝ)
  | 2 => (3014953739 / 10000000000 : ℝ)
  | 3 => (599468599 / 2000000000 : ℝ)
  | 4 => (1489900011 / 5000000000 : ℝ)
  | 5 => (1851453 / 6250000 : ℝ)
  | 6 => (1472458651 / 5000000000 : ℝ)
  | 7 => (2927577501 / 10000000000 : ℝ)
  | 8 => (291030537 / 1000000000 : ℝ)
  | 9 => (2893100877 / 10000000000 : ℝ)
  | 10 => (1437981997 / 5000000000 : ℝ)
  | 11 => (571778937 / 2000000000 : ℝ)
  | 12 => (2841892917 / 10000000000 : ℝ)
  | 13 => (706239663 / 2500000000 : ℝ)
  | 14 => (1404045927 / 5000000000 : ℝ)
  | 15 => (1395646241 / 5000000000 : ℝ)
  | 16 => (2774560497 / 10000000000 : ℝ)
  | 17 => (1378947927 / 5000000000 : ℝ)
  | 18 => (274129851 / 1000000000 : ℝ)
  | 19 => (1362384211 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch033Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (773920567 / 2500000000 : ℝ)
  | 1 => (769426317 / 2500000000 : ℝ)
  | 2 => (191237297 / 625000000 : ℝ)
  | 3 => (30419567 / 100000000 : ℝ)
  | 4 => (604837019 / 2000000000 : ℝ)
  | 5 => (3006481911 / 10000000000 : ℝ)
  | 6 => (1494423563 / 5000000000 : ℝ)
  | 7 => (594256143 / 2000000000 : ℝ)
  | 8 => (369222831 / 1250000000 : ℝ)
  | 9 => (2936352899 / 10000000000 : ℝ)
  | 10 => (583798287 / 2000000000 : ℝ)
  | 11 => (1450849113 / 5000000000 : ℝ)
  | 12 => (1442236619 / 5000000000 : ℝ)
  | 13 => (1433658217 / 5000000000 : ℝ)
  | 14 => (2850227779 / 10000000000 : ℝ)
  | 15 => (1416603617 / 5000000000 : ℝ)
  | 16 => (1408127379 / 5000000000 : ℝ)
  | 17 => (2799370311 / 10000000000 : ℝ)
  | 18 => (2782553849 / 10000000000 : ℝ)
  | 19 => (1382902663 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch033_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch033Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch033Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell660_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell661_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell662_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell663_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell664_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell665_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell666_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell667_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell668_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell669_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell670_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell671_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell672_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell673_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell674_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell675_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell676_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell677_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell678_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell679_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper] at h ⊢
    exact h

end HodgeProofHP
