import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1340_leftExp :
    (53387951489 / 10000000000 : ℝ) ≤ Real.exp (67 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 40 : ℝ) (1053737902667 / 1000000000000 : ℝ)
    (53387951489 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1340_rightExp :
    Real.exp (1341 / 800 : ℝ) ≤ (26727364079 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1341 / 800 : ℝ) (1053779065109 / 1000000000000 : ℝ)
    (26727364079 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1340_denomUpper :
    Real.exp (81872749899037847 / 5000000000000000 : ℝ) ≤ (32308493545829863 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (81872749899037847 / 5000000000000000 : ℝ) (417033103997
    / 250000000000 : ℝ) (32308493545829863 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1340_denomLower :
    (126510861284049093 / 10000000000 : ℝ) ≤ Real.exp (20441567036778811 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (20441567036778811 / 1250000000000000 : ℝ) (52094457029 /
    31250000000 : ℝ) (126510861284049093 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1340_product_lower :
    (20965395161778811 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1340_leftExp
    (by norm_num : (0 : ℝ) ≤ (53387951489 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1340_product_upper :
    Real.pi * Real.exp (1341 / 800 : ℝ) ≤ (83966499899037847 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1340_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1340_endpointLower :
    (3097 / 19531250 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 80 : ℝ) (1341 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (20965395161778811 / 1250000000000000 : ℝ) (Real.pi * Real.exp (67 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1340_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1341 / 800 : ℝ) - (67 / 160 : ℝ)) ≤
      (32308493545829863 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1340_denomUpper
    linarith [hpThetaJensenCell1340_product_upper]
  have hi : (1 / (32308493545829863 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1341 / 800 : ℝ) - (67 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32308493545829863 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32308493545829863 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 160 : ℝ) - Real.pi * Real.exp (1341 / 800 : ℝ)) := by
    rw [show (67 / 160 : ℝ) - Real.pi * Real.exp (1341 / 800 : ℝ) =
      -(Real.pi * Real.exp (1341 / 800 : ℝ) - (67 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1340_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32308493545829863 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1340_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 80 : ℝ) (1341 / 1600 : ℝ) ≤ (203541 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1341 / 800 : ℝ)) (83966499899037847 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1341 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1340_product_upper
  have hD : (126510861284049093 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 40 : ℝ) - (1341 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1340_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1340_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 40 : ℝ) - (1341 / 3200 : ℝ)) ≤
      (1 / (126510861284049093 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (126510861284049093 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1341 / 3200 : ℝ) - Real.pi * Real.exp (67 / 40 : ℝ)) ≤
      (2 / (126510861284049093 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1341 / 3200 : ℝ) - Real.pi * Real.exp (67 / 40 : ℝ) =
      -(Real.pi * Real.exp (67 / 40 : ℝ) - (1341 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (83966499899037847 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (83966499899037847 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1340_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 80 : ℝ) (1341 / 1600 : ℝ)) :
    (3097 / 19531250 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (203541 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1340_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1340_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1341_leftExp :
    (13363682039 / 2500000000 : ℝ) ≤ Real.exp (1341 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1341 / 800 : ℝ) (263444766277 / 250000000000 : ℝ)
    (13363682039 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1341_rightExp :
    Real.exp (671 / 400 : ℝ) ≤ (13380397087 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (671 / 400 : ℝ) (526910114579 / 500000000000 : ℝ)
    (13380397087 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1341_denomUpper :
    Real.exp (40988105575739591 / 2500000000000000 : ℝ) ≤ (5277438990972529 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40988105575739591 / 2500000000000000 : ℝ) (333842286799
    / 200000000000 : ℝ) (5277438990972529 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1341_denomLower :
    (32288134429129597 / 2500000000 : ℝ) ≤ Real.exp (5116849885533261 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5116849885533261 / 312500000000000 : ℝ) (1668099556911 /
    1000000000000 : ℝ) (32288134429129597 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1341_product_lower :
    (5247904573033261 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1341 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1341_leftExp
    (by norm_num : (0 : ℝ) ≤ (13363682039 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1341_product_upper :
    Real.pi * Real.exp (671 / 400 : ℝ) ≤ (42035761825739591 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1341_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1341_endpointLower :
    (1557269 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1341 / 1600 : ℝ) (671 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5247904573033261 / 312500000000000 : ℝ) (Real.pi * Real.exp (1341 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1341_product_lower
  have hD : Real.exp (Real.pi * Real.exp (671 / 400 : ℝ) - (1341 / 3200 : ℝ)) ≤
      (5277438990972529 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1341_denomUpper
    linarith [hpThetaJensenCell1341_product_upper]
  have hi : (1 / (5277438990972529 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (671 / 400 : ℝ) - (1341 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5277438990972529 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5277438990972529 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1341 / 3200 : ℝ) - Real.pi * Real.exp (671 / 400 : ℝ)) := by
    rw [show (1341 / 3200 : ℝ) - Real.pi * Real.exp (671 / 400 : ℝ) =
      -(Real.pi * Real.exp (671 / 400 : ℝ) - (1341 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1341 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1341 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1341_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5277438990972529 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1341_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1341 / 1600 : ℝ) (671 / 800 : ℝ) ≤ (159921 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (671 / 400 : ℝ)) (42035761825739591 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (671 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1341_product_upper
  have hD : (32288134429129597 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1341 / 800 : ℝ) - (671 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1341_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1341_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1341 / 800 : ℝ) - (671 / 1600 : ℝ)) ≤
      (1 / (32288134429129597 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (32288134429129597 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((671 / 1600 : ℝ) - Real.pi * Real.exp (1341 / 800 : ℝ)) ≤
      (2 / (32288134429129597 / 2500000000 : ℝ) : ℝ) := by
    rw [show (671 / 1600 : ℝ) - Real.pi * Real.exp (1341 / 800 : ℝ) =
      -(Real.pi * Real.exp (1341 / 800 : ℝ) - (671 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42035761825739591 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (42035761825739591 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1341_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1341 / 1600 : ℝ) (671 / 800 : ℝ)) :
    (1557269 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (159921 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1341_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1341_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1342_leftExp :
    (10704317669 / 2000000000 : ℝ) ≤ Real.exp (671 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (671 / 400 : ℝ) (1053820229157 / 1000000000000 : ℝ)
    (10704317669 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1342_rightExp :
    Real.exp (1343 / 800 : ℝ) ≤ (53588532163 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1343 / 800 : ℝ) (526930697407 / 500000000000 : ℝ)
    (53588532163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1342_denomUpper :
    Real.exp (164159607523555659 / 10000000000000000 : ℝ) ≤ (134698006991794203 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (164159607523555659 / 10000000000000000 : ℝ)
    (334058504249 / 200000000000 : ℝ) (134698006991794203 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1342_denomLower :
    (3296320868188219 / 250000000 : ℝ) ≤ Real.exp (4098652969298631 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4098652969298631 / 250000000000000 : ℝ) (1669178553299 /
    1000000000000 : ℝ) (3296320868188219 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1342_product_lower :
    (4203574844298631 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (671 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1342_leftExp
    (by norm_num : (0 : ℝ) ≤ (10704317669 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1342_product_upper :
    Real.pi * Real.exp (1343 / 800 : ℝ) ≤ (168353357523555659 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1342_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1342_endpointLower :
    (764671 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (671 / 800 : ℝ) (1343 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4203574844298631 / 250000000000000 : ℝ) (Real.pi * Real.exp (671 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1342_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1343 / 800 : ℝ) - (671 / 1600 : ℝ)) ≤
      (134698006991794203 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1342_denomUpper
    linarith [hpThetaJensenCell1342_product_upper]
  have hi : (1 / (134698006991794203 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1343 / 800 : ℝ) - (671 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (134698006991794203 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (134698006991794203 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((671 / 1600 : ℝ) - Real.pi * Real.exp (1343 / 800 : ℝ)) := by
    rw [show (671 / 1600 : ℝ) - Real.pi * Real.exp (1343 / 800 : ℝ) =
      -(Real.pi * Real.exp (1343 / 800 : ℝ) - (671 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (671 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (671 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1342_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (134698006991794203 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1342_endpointUpper :
    hpThetaJensenKernelEndpointUpper (671 / 800 : ℝ) (1343 / 1600 : ℝ) ≤ (392643 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1343 / 800 : ℝ)) (168353357523555659 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1343 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1342_product_upper
  have hD : (3296320868188219 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (671 / 400 : ℝ) - (1343 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1342_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1342_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (671 / 400 : ℝ) - (1343 / 3200 : ℝ)) ≤
      (1 / (3296320868188219 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3296320868188219 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1343 / 3200 : ℝ) - Real.pi * Real.exp (671 / 400 : ℝ)) ≤
      (2 / (3296320868188219 / 250000000 : ℝ) : ℝ) := by
    rw [show (1343 / 3200 : ℝ) - Real.pi * Real.exp (671 / 400 : ℝ) =
      -(Real.pi * Real.exp (671 / 400 : ℝ) - (1343 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (168353357523555659 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (168353357523555659 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1342_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (671 / 800 : ℝ) (1343 / 1600 : ℝ)) :
    (764671 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (392643 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1342_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1342_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1343_leftExp :
    (53588532161 / 10000000000 : ℝ) ≤ Real.exp (1343 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1343 / 800 : ℝ) (1053861394813 / 1000000000000 : ℝ)
    (53588532161 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1343_rightExp :
    Real.exp (42 / 25 : ℝ) ≤ (1676736241 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42 / 25 : ℝ) (1053902562079 / 1000000000000 : ℝ)
    (1676736241 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1343_denomUpper :
    Real.exp (5136470493821913 / 312500000000000 : ℝ) ≤ (137521478926166307 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (5136470493821913 / 312500000000000 : ℝ) (20892196033 /
    12500000000 : ℝ) (137521478926166307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1343_denomLower :
    (6730656278782611 / 500000000 : ℝ) ≤ Real.exp (20519162991092539 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (20519162991092539 / 1250000000000000 : ℝ) (1670259618919
    / 1000000000000 : ℝ) (6730656278782611 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1343_product_lower :
    (21044162991092539 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1343 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1343_leftExp
    (by norm_num : (0 : ℝ) ≤ (53588532161 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1343_product_upper :
    Real.pi * Real.exp (42 / 25 : ℝ) ≤ (5267622837571913 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1343_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1343_endpointLower :
    (375469 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1343 / 1600 : ℝ) (21 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21044162991092539 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1343 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1343_product_lower
  have hD : Real.exp (Real.pi * Real.exp (42 / 25 : ℝ) - (1343 / 3200 : ℝ)) ≤
      (137521478926166307 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1343_denomUpper
    linarith [hpThetaJensenCell1343_product_upper]
  have hi : (1 / (137521478926166307 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (42 / 25 : ℝ) - (1343 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (137521478926166307 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (137521478926166307 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1343 / 3200 : ℝ) - Real.pi * Real.exp (42 / 25 : ℝ)) := by
    rw [show (1343 / 3200 : ℝ) - Real.pi * Real.exp (42 / 25 : ℝ) =
      -(Real.pi * Real.exp (42 / 25 : ℝ) - (1343 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1343 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1343 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1343_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (137521478926166307 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1343_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1343 / 1600 : ℝ) (21 / 25 : ℝ) ≤ (771203 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (42 / 25 : ℝ)) (5267622837571913 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1343_product_upper
  have hD : (6730656278782611 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1343 / 800 : ℝ) - (21 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell1343_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1343_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1343 / 800 : ℝ) - (21 / 50 : ℝ)) ≤
      (1 / (6730656278782611 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6730656278782611 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 50 : ℝ) - Real.pi * Real.exp (1343 / 800 : ℝ)) ≤
      (2 / (6730656278782611 / 500000000 : ℝ) : ℝ) := by
    rw [show (21 / 50 : ℝ) - Real.pi * Real.exp (1343 / 800 : ℝ) =
      -(Real.pi * Real.exp (1343 / 800 : ℝ) - (21 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5267622837571913 / 312500000000000 : ℝ) ^ 2 - 6 *
      (5267622837571913 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1343_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1343 / 1600 : ℝ) (21 / 25 : ℝ)) :
    (375469 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (771203 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1343_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1343_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1344_leftExp :
    (5365555971 / 1000000000 : ℝ) ≤ Real.exp (42 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (42 / 25 : ℝ) (526951281039 / 500000000000 : ℝ)
    (5365555971 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1344_rightExp :
    Real.exp (269 / 160 : ℝ) ≤ (26861335549 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (269 / 160 : ℝ) (131742966369 / 125000000000 : ℝ)
    (26861335549 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1344_denomUpper :
    Real.exp (82287383731389557 / 5000000000000000 : ℝ) ≤ (140407833096417477 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (82287383731389557 / 5000000000000000 : ℝ) (836230461499
    / 500000000000 : ℝ) (140407833096417477 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1344_denomLower :
    (137434817346664421 / 10000000000 : ℝ) ≤ Real.exp (2054509401755729 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2054509401755729 / 125000000000000 : ℝ) (1671342758627 /
    1000000000000 : ℝ) (137434817346664421 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1344_product_lower :
    (2107048464255729 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (42 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1344_leftExp
    (by norm_num : (0 : ℝ) ≤ (5365555971 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1344_product_upper :
    Real.pi * Real.exp (269 / 160 : ℝ) ≤ (84387383731389557 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1344_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1344_endpointLower :
    (92179 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 25 : ℝ) (269 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2107048464255729 / 125000000000000 : ℝ) (Real.pi * Real.exp (42 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1344_product_lower
  have hD : Real.exp (Real.pi * Real.exp (269 / 160 : ℝ) - (21 / 50 : ℝ)) ≤
      (140407833096417477 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1344_denomUpper
    linarith [hpThetaJensenCell1344_product_upper]
  have hi : (1 / (140407833096417477 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (269 / 160 : ℝ) - (21 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (140407833096417477 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (140407833096417477 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 50 : ℝ) - Real.pi * Real.exp (269 / 160 : ℝ)) := by
    rw [show (21 / 50 : ℝ) - Real.pi * Real.exp (269 / 160 : ℝ) =
      -(Real.pi * Real.exp (269 / 160 : ℝ) - (21 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (42 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (42 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1344_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (140407833096417477 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1344_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 25 : ℝ) (269 / 320 : ℝ) ≤ (302941 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (269 / 160 : ℝ)) (84387383731389557 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (269 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1344_product_upper
  have hD : (137434817346664421 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (42 / 25 : ℝ) - (269 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1344_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1344_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (42 / 25 : ℝ) - (269 / 640 : ℝ)) ≤
      (1 / (137434817346664421 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (137434817346664421 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((269 / 640 : ℝ) - Real.pi * Real.exp (42 / 25 : ℝ)) ≤
      (2 / (137434817346664421 / 10000000000 : ℝ) : ℝ) := by
    rw [show (269 / 640 : ℝ) - Real.pi * Real.exp (42 / 25 : ℝ) =
      -(Real.pi * Real.exp (42 / 25 : ℝ) - (269 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (84387383731389557 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (84387383731389557 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1344_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 25 : ℝ) (269 / 320 : ℝ)) :
    (92179 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (302941 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1344_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1344_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1345_leftExp :
    (6715333887 / 1250000000 : ℝ) ≤ Real.exp (269 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (269 / 160 : ℝ) (1053943730951 / 1000000000000 : ℝ)
    (6715333887 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1345_rightExp :
    Real.exp (673 / 400 : ℝ) ≤ (2151594657 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (673 / 400 : ℝ) (1053984901433 / 1000000000000 : ℝ)
    (2151594657 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1345_denomUpper :
    Real.exp (6591309713268601 / 400000000000000 : ℝ) ≤ (143358547624313839 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (6591309713268601 / 400000000000000 : ℝ) (334709649433 /
    200000000000 : ℝ) (143358547624313839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1345_denomLower :
    (35079837922507729 / 2500000000 : ℝ) ≤ Real.exp (2571382245841013 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2571382245841013 / 156250000000000 : ℝ) (1672427977257 /
    1000000000000 : ℝ) (35079837922507729 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1345_product_lower :
    (2637104902091013 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (269 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1345_leftExp
    (by norm_num : (0 : ℝ) ≤ (6715333887 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1345_product_upper :
    Real.pi * Real.exp (673 / 400 : ℝ) ≤ (6759434713268601 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1345_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1345_endpointLower :
    (14483 / 100000000 : ℝ) ≤ hpThetaTraceEndpointLower (269 / 320 : ℝ) (673 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2637104902091013 / 156250000000000 : ℝ) (Real.pi * Real.exp (269 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1345_product_lower
  have hD : Real.exp (Real.pi * Real.exp (673 / 400 : ℝ) - (269 / 640 : ℝ)) ≤
      (143358547624313839 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1345_denomUpper
    linarith [hpThetaJensenCell1345_product_upper]
  have hi : (1 / (143358547624313839 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (673 / 400 : ℝ) - (269 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (143358547624313839 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (143358547624313839 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((269 / 640 : ℝ) - Real.pi * Real.exp (673 / 400 : ℝ)) := by
    rw [show (269 / 640 : ℝ) - Real.pi * Real.exp (673 / 400 : ℝ) =
      -(Real.pi * Real.exp (673 / 400 : ℝ) - (269 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (269 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (269 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1345_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (143358547624313839 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1345_endpointUpper :
    hpThetaJensenKernelEndpointUpper (269 / 320 : ℝ) (673 / 800 : ℝ) ≤ (1487463 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (673 / 400 : ℝ)) (6759434713268601 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (673 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1345_product_upper
  have hD : (35079837922507729 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (269 / 160 : ℝ) - (673 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1345_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1345_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (269 / 160 : ℝ) - (673 / 1600 : ℝ)) ≤
      (1 / (35079837922507729 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35079837922507729 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((673 / 1600 : ℝ) - Real.pi * Real.exp (269 / 160 : ℝ)) ≤
      (2 / (35079837922507729 / 2500000000 : ℝ) : ℝ) := by
    rw [show (673 / 1600 : ℝ) - Real.pi * Real.exp (269 / 160 : ℝ) =
      -(Real.pi * Real.exp (269 / 160 : ℝ) - (673 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6759434713268601 / 400000000000000 : ℝ) ^ 2 - 6 *
      (6759434713268601 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1345_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (269 / 320 : ℝ) (673 / 800 : ℝ)) :
    (14483 / 100000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1487463 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1345_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1345_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1346_leftExp :
    (53789866423 / 10000000000 : ℝ) ≤ Real.exp (673 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (673 / 400 : ℝ) (131748112679 / 125000000000 : ℝ)
    (53789866423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1346_rightExp :
    Real.exp (1347 / 800 : ℝ) ≤ (26928572899 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1347 / 800 : ℝ) (527013036761 / 500000000000 : ℝ)
    (26928572899 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1346_denomUpper :
    Real.exp (82495491119488107 / 5000000000000000 : ℝ) ≤ (1463751371551309 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (82495491119488107 / 5000000000000000 : ℝ) (334927532003
    / 200000000000 : ℝ) (1463751371551309 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1346_denomLower :
    (14326820579236153 / 1000000000 : ℝ) ≤ Real.exp (20597054879445677 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20597054879445677 / 1250000000000000 : ℝ) (836757639827
    / 500000000000 : ℝ) (14326820579236153 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1346_product_lower :
    (21123226754445677 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (673 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1346_leftExp
    (by norm_num : (0 : ℝ) ≤ (53789866423 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1346_product_upper :
    Real.pi * Real.exp (1347 / 800 : ℝ) ≤ (84598616119488107 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1346_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1346_endpointLower :
    (44443 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (673 / 800 : ℝ) (1347 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21123226754445677 / 1250000000000000 : ℝ) (Real.pi * Real.exp (673 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1346_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1347 / 800 : ℝ) - (673 / 1600 : ℝ)) ≤
      (1463751371551309 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1346_denomUpper
    linarith [hpThetaJensenCell1346_product_upper]
  have hi : (1 / (1463751371551309 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1347 / 800 : ℝ) - (673 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1463751371551309 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1463751371551309 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((673 / 1600 : ℝ) - Real.pi * Real.exp (1347 / 800 : ℝ)) := by
    rw [show (673 / 1600 : ℝ) - Real.pi * Real.exp (1347 / 800 : ℝ) =
      -(Real.pi * Real.exp (1347 / 800 : ℝ) - (673 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (673 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (673 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1346_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1463751371551309 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1346_endpointUpper :
    hpThetaJensenKernelEndpointUpper (673 / 800 : ℝ) (1347 / 1600 : ℝ) ≤ (1460671 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1347 / 800 : ℝ)) (84598616119488107 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1347 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1346_product_upper
  have hD : (14326820579236153 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (673 / 400 : ℝ) - (1347 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1346_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1346_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (673 / 400 : ℝ) - (1347 / 3200 : ℝ)) ≤
      (1 / (14326820579236153 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14326820579236153 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1347 / 3200 : ℝ) - Real.pi * Real.exp (673 / 400 : ℝ)) ≤
      (2 / (14326820579236153 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1347 / 3200 : ℝ) - Real.pi * Real.exp (673 / 400 : ℝ) =
      -(Real.pi * Real.exp (673 / 400 : ℝ) - (1347 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (84598616119488107 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (84598616119488107 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1346_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (673 / 800 : ℝ) (1347 / 1600 : ℝ)) :
    (44443 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1460671 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1346_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1346_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1347_leftExp :
    (13464286449 / 2500000000 : ℝ) ≤ Real.exp (1347 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1347 / 800 : ℝ) (1054026073521 / 1000000000000 : ℝ)
    (13464286449 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1347_rightExp :
    Real.exp (337 / 200 : ℝ) ≤ (2156980373 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (337 / 200 : ℝ) (52703362361 / 50000000000 : ℝ)
    (2156980373 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1347_denomUpper :
    Real.exp (6607979440954189 / 400000000000000 : ℝ) ≤ (14945915389744807 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6607979440954189 / 400000000000000 : ℝ) (1675729166483 /
    1000000000000 : ℝ) (14945915389744807 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1347_denomLower :
    (73141446670260963 / 5000000000 : ℝ) ≤ Real.exp (5155771199235851 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5155771199235851 / 312500000000000 : ℝ) (1674604670691 /
    1000000000000 : ℝ) (73141446670260963 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1347_product_lower :
    (5287411824235851 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1347 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1347_leftExp
    (by norm_num : (0 : ℝ) ≤ (13464286449 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1347_product_upper :
    Real.pi * Real.exp (337 / 200 : ℝ) ≤ (6776354440954189 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1347_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1347_endpointLower :
    (1396487 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1347 / 1600 : ℝ) (337 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5287411824235851 / 312500000000000 : ℝ) (Real.pi * Real.exp (1347 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1347_product_lower
  have hD : Real.exp (Real.pi * Real.exp (337 / 200 : ℝ) - (1347 / 3200 : ℝ)) ≤
      (14945915389744807 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1347_denomUpper
    linarith [hpThetaJensenCell1347_product_upper]
  have hi : (1 / (14945915389744807 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (337 / 200 : ℝ) - (1347 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14945915389744807 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14945915389744807 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1347 / 3200 : ℝ) - Real.pi * Real.exp (337 / 200 : ℝ)) := by
    rw [show (1347 / 3200 : ℝ) - Real.pi * Real.exp (337 / 200 : ℝ) =
      -(Real.pi * Real.exp (337 / 200 : ℝ) - (1347 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1347 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1347 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1347_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14945915389744807 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1347_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1347 / 1600 : ℝ) (337 / 400 : ℝ) ≤ (358581 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (337 / 200 : ℝ)) (6776354440954189 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (337 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1347_product_upper
  have hD : (73141446670260963 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1347 / 800 : ℝ) - (337 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1347_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1347_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1347 / 800 : ℝ) - (337 / 800 : ℝ)) ≤
      (1 / (73141446670260963 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (73141446670260963 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((337 / 800 : ℝ) - Real.pi * Real.exp (1347 / 800 : ℝ)) ≤
      (2 / (73141446670260963 / 5000000000 : ℝ) : ℝ) := by
    rw [show (337 / 800 : ℝ) - Real.pi * Real.exp (1347 / 800 : ℝ) =
      -(Real.pi * Real.exp (1347 / 800 : ℝ) - (337 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6776354440954189 / 400000000000000 : ℝ) ^ 2 - 6 *
      (6776354440954189 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1347_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1347 / 1600 : ℝ) (337 / 400 : ℝ)) :
    (1396487 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (358581 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1347_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1347_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1348_leftExp :
    (26962254661 / 5000000000 : ℝ) ≤ Real.exp (337 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (337 / 200 : ℝ) (1054067247219 / 1000000000000 : ℝ)
    (26962254661 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1348_rightExp :
    Real.exp (1349 / 800 : ℝ) ≤ (53991957107 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1349 / 800 : ℝ) (527054211263 / 500000000000 : ℝ)
    (53991957107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1348_denomUpper :
    Real.exp (165408254503651451 / 10000000000000000 : ℝ) ≤ (38153047030852657 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (165408254503651451 / 10000000000000000 : ℝ) (8384113857
    / 5000000000 : ℝ) (38153047030852657 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1348_denomLower :
    (74682482760414929 / 5000000000 : ℝ) ≤ Real.exp (10324573880620039 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10324573880620039 / 625000000000000 : ℝ) (209462019411 /
    125000000000 : ℝ) (74682482760414929 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1348_product_lower :
    (10588050443120039 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (337 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1348_leftExp
    (by norm_num : (0 : ℝ) ≤ (26962254661 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1348_product_upper :
    Real.pi * Real.exp (1349 / 800 : ℝ) ≤ (169620754503651451 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1348_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1348_endpointLower :
    (54849 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (337 / 400 : ℝ) (1349 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10588050443120039 / 625000000000000 : ℝ) (Real.pi * Real.exp (337 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1348_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1349 / 800 : ℝ) - (337 / 800 : ℝ)) ≤
      (38153047030852657 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1348_denomUpper
    linarith [hpThetaJensenCell1348_product_upper]
  have hi : (1 / (38153047030852657 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1349 / 800 : ℝ) - (337 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38153047030852657 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38153047030852657 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((337 / 800 : ℝ) - Real.pi * Real.exp (1349 / 800 : ℝ)) := by
    rw [show (337 / 800 : ℝ) - Real.pi * Real.exp (1349 / 800 : ℝ) =
      -(Real.pi * Real.exp (1349 / 800 : ℝ) - (337 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (337 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (337 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1348_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38153047030852657 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1348_endpointUpper :
    hpThetaJensenKernelEndpointUpper (337 / 400 : ℝ) (1349 / 1600 : ℝ) ≤ (704207 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1349 / 800 : ℝ)) (169620754503651451 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1349 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1348_product_upper
  have hD : (74682482760414929 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (337 / 200 : ℝ) - (1349 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1348_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1348_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (337 / 200 : ℝ) - (1349 / 3200 : ℝ)) ≤
      (1 / (74682482760414929 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (74682482760414929 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1349 / 3200 : ℝ) - Real.pi * Real.exp (337 / 200 : ℝ)) ≤
      (2 / (74682482760414929 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1349 / 3200 : ℝ) - Real.pi * Real.exp (337 / 200 : ℝ) =
      -(Real.pi * Real.exp (337 / 200 : ℝ) - (1349 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (169620754503651451 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (169620754503651451 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1348_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (337 / 400 : ℝ) (1349 / 1600 : ℝ)) :
    (54849 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (704207 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1348_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1348_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1349_leftExp :
    (10798391421 / 2000000000 : ℝ) ≤ Real.exp (1349 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1349 / 800 : ℝ) (42164336901 / 40000000000 : ℝ)
    (10798391421 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1349_rightExp :
    Real.exp (27 / 16 : ℝ) ≤ (54059489253 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 16 : ℝ) (1054149599441 / 1000000000000 : ℝ)
    (54059489253 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1349_denomUpper :
    Real.exp (165617288020800029 / 10000000000000000 : ℝ) ≤ (155835869861394331 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (165617288020800029 / 10000000000000000 : ℝ) (83895923987
    / 50000000000 : ℝ) (155835869861394331 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1349_denomLower :
    (30503202347803877 / 2000000000 : ℝ) ≤ Real.exp (4135048762635279 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4135048762635279 / 250000000000000 : ℝ) (419197434581 /
    250000000000 : ℝ) (30503202347803877 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1349_product_lower :
    (4240517512635279 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1349 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1349_leftExp
    (by norm_num : (0 : ℝ) ≤ (10798391421 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1349_product_upper :
    Real.pi * Real.exp (27 / 16 : ℝ) ≤ (169832913020800029 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1349_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1349_endpointLower :
    (84149 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1349 / 1600 : ℝ) (27 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4240517512635279 / 250000000000000 : ℝ) (Real.pi * Real.exp (1349 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1349_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 16 : ℝ) - (1349 / 3200 : ℝ)) ≤
      (155835869861394331 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1349_denomUpper
    linarith [hpThetaJensenCell1349_product_upper]
  have hi : (1 / (155835869861394331 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 16 : ℝ) - (1349 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (155835869861394331 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (155835869861394331 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1349 / 3200 : ℝ) - Real.pi * Real.exp (27 / 16 : ℝ)) := by
    rw [show (1349 / 3200 : ℝ) - Real.pi * Real.exp (27 / 16 : ℝ) =
      -(Real.pi * Real.exp (27 / 16 : ℝ) - (1349 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1349 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1349 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1349_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (155835869861394331 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1349_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1349 / 1600 : ℝ) (27 / 32 : ℝ) ≤ (172867 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 16 : ℝ)) (169832913020800029 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1349_product_upper
  have hD : (30503202347803877 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1349 / 800 : ℝ) - (27 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell1349_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1349_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1349 / 800 : ℝ) - (27 / 64 : ℝ)) ≤
      (1 / (30503202347803877 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (30503202347803877 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 64 : ℝ) - Real.pi * Real.exp (1349 / 800 : ℝ)) ≤
      (2 / (30503202347803877 / 2000000000 : ℝ) : ℝ) := by
    rw [show (27 / 64 : ℝ) - Real.pi * Real.exp (1349 / 800 : ℝ) =
      -(Real.pi * Real.exp (1349 / 800 : ℝ) - (27 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (169832913020800029 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (169832913020800029 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1349_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1349 / 1600 : ℝ) (27 / 32 : ℝ)) :
    (84149 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (172867 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1349_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1349_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1350_leftExp :
    (54059489251 / 10000000000 : ℝ) ≤ Real.exp (27 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 16 : ℝ) (13176869993 / 12500000000 : ℝ)
    (54059489251 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1350_rightExp :
    Real.exp (1351 / 800 : ℝ) ≤ (54127105867 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1351 / 800 : ℝ) (263547694491 / 250000000000 : ℝ)
    (54127105867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1350_denomUpper :
    Real.exp (165826586902026131 / 10000000000000000 : ℝ) ≤ (159131869314329887 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (165826586902026131 / 10000000000000000 : ℝ)
    (1679016296409 / 1000000000000 : ℝ) (159131869314329887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1350_denomLower :
    (155737660858160631 / 10000000000 : ℝ) ≤ Real.exp (20701372994378449 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (20701372994378449 / 1250000000000000 : ℝ) (67115416989 /
    40000000000 : ℝ) (155737660858160631 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1350_product_lower :
    (21229107369378449 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1350_leftExp
    (by norm_num : (0 : ℝ) ≤ (54059489251 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1350_product_upper :
    Real.pi * Real.exp (1351 / 800 : ℝ) ≤ (170045336902026131 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1350_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1350_endpointLower :
    (660979 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 32 : ℝ) (1351 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21229107369378449 / 1250000000000000 : ℝ) (Real.pi * Real.exp (27 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell1350_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1351 / 800 : ℝ) - (27 / 64 : ℝ)) ≤
      (159131869314329887 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1350_denomUpper
    linarith [hpThetaJensenCell1350_product_upper]
  have hi : (1 / (159131869314329887 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1351 / 800 : ℝ) - (27 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (159131869314329887 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (159131869314329887 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 64 : ℝ) - Real.pi * Real.exp (1351 / 800 : ℝ)) := by
    rw [show (27 / 64 : ℝ) - Real.pi * Real.exp (1351 / 800 : ℝ) =
      -(Real.pi * Real.exp (1351 / 800 : ℝ) - (27 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 16 : ℝ)) := by
    have h := hpThetaJensenCell1350_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (159131869314329887 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1350_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 32 : ℝ) (1351 / 1600 : ℝ) ≤ (678941 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1351 / 800 : ℝ)) (170045336902026131 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1351 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1350_product_upper
  have hD : (155737660858160631 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 16 : ℝ) - (1351 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1350_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1350_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 16 : ℝ) - (1351 / 3200 : ℝ)) ≤
      (1 / (155737660858160631 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (155737660858160631 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1351 / 3200 : ℝ) - Real.pi * Real.exp (27 / 16 : ℝ)) ≤
      (2 / (155737660858160631 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1351 / 3200 : ℝ) - Real.pi * Real.exp (27 / 16 : ℝ) =
      -(Real.pi * Real.exp (27 / 16 : ℝ) - (1351 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (170045336902026131 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (170045336902026131 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1350_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 32 : ℝ) (1351 / 1600 : ℝ)) :
    (660979 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (678941 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1350_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1350_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1351_leftExp :
    (6765888233 / 1250000000 : ℝ) ≤ Real.exp (1351 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1351 / 800 : ℝ) (1054190777963 / 1000000000000 : ℝ)
    (6765888233 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1351_rightExp :
    Real.exp (169 / 100 : ℝ) ≤ (13548701763 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (169 / 100 : ℝ) (210846391619 / 200000000000 : ℝ)
    (13548701763 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1351_denomUpper :
    Real.exp (41509037867728459 / 2500000000000000 : ℝ) ≤ (32500379614234457 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (41509037867728459 / 2500000000000000 : ℝ) (840058113153
    / 500000000000 : ℝ) (32500379614234457 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1351_denomLower :
    (159031582021558249 / 10000000000 : ℝ) ≤ Real.exp (2590941918210867 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2590941918210867 / 156250000000000 : ℝ) (419745804849 /
    250000000000 : ℝ) (159031582021558249 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1351_product_lower :
    (2656957543210867 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1351 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1351_leftExp
    (by norm_num : (0 : ℝ) ≤ (6765888233 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1351_product_upper :
    Real.pi * Real.exp (169 / 100 : ℝ) ≤ (42564506617728459 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1351_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1351_endpointLower :
    (64897 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1351 / 1600 : ℝ) (169 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2656957543210867 / 156250000000000 : ℝ) (Real.pi * Real.exp (1351 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1351_product_lower
  have hD : Real.exp (Real.pi * Real.exp (169 / 100 : ℝ) - (1351 / 3200 : ℝ)) ≤
      (32500379614234457 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1351_denomUpper
    linarith [hpThetaJensenCell1351_product_upper]
  have hi : (1 / (32500379614234457 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (169 / 100 : ℝ) - (1351 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32500379614234457 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32500379614234457 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1351 / 3200 : ℝ) - Real.pi * Real.exp (169 / 100 : ℝ)) := by
    rw [show (1351 / 3200 : ℝ) - Real.pi * Real.exp (169 / 100 : ℝ) =
      -(Real.pi * Real.exp (169 / 100 : ℝ) - (1351 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1351 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1351 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1351_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32500379614234457 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1351_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1351 / 1600 : ℝ) (169 / 200 : ℝ) ≤ (1333247 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (169 / 100 : ℝ)) (42564506617728459 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (169 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1351_product_upper
  have hD : (159031582021558249 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1351 / 800 : ℝ) - (169 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1351_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1351_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1351 / 800 : ℝ) - (169 / 400 : ℝ)) ≤
      (1 / (159031582021558249 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (159031582021558249 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((169 / 400 : ℝ) - Real.pi * Real.exp (1351 / 800 : ℝ)) ≤
      (2 / (159031582021558249 / 10000000000 : ℝ) : ℝ) := by
    rw [show (169 / 400 : ℝ) - Real.pi * Real.exp (1351 / 800 : ℝ) =
      -(Real.pi * Real.exp (1351 / 800 : ℝ) - (169 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42564506617728459 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (42564506617728459 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1351_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1351 / 1600 : ℝ) (169 / 200 : ℝ)) :
    (64897 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1333247 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1351_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1351_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1352_leftExp :
    (1083896141 / 200000000 : ℝ) ≤ Real.exp (169 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (169 / 100 : ℝ) (527115979047 / 500000000000 : ℝ)
    (1083896141 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1352_rightExp :
    Real.exp (1353 / 800 : ℝ) ≤ (27131296459 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1353 / 800 : ℝ) (210854627967 / 200000000000 : ℝ)
    (27131296459 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1352_denomUpper :
    Real.exp (83122991036519187 / 5000000000000000 : ℝ) ≤ (1037173191242863 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83122991036519187 / 5000000000000000 : ℝ) (1681218274457
    / 1000000000000 : ℝ) (1037173191242863 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1352_denomLower :
    (162399485883628247 / 10000000000 : ℝ) ≤ Real.exp (415074618174559 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (415074618174559 / 25000000000000 : ℝ) (420020781821 /
    250000000000 : ℝ) (162399485883628247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1352_product_lower :
    (425644930674559 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (169 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1352_leftExp
    (by norm_num : (0 : ℝ) ≤ (1083896141 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1352_product_upper :
    Real.pi * Real.exp (1353 / 800 : ℝ) ≤ (85235491036519187 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1352_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1352_endpointLower :
    (318581 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (169 / 200 : ℝ) (1353 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (425644930674559 / 25000000000000 : ℝ) (Real.pi * Real.exp (169 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1352_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1353 / 800 : ℝ) - (169 / 400 : ℝ)) ≤
      (1037173191242863 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1352_denomUpper
    linarith [hpThetaJensenCell1352_product_upper]
  have hi : (1 / (1037173191242863 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1353 / 800 : ℝ) - (169 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1037173191242863 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1037173191242863 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((169 / 400 : ℝ) - Real.pi * Real.exp (1353 / 800 : ℝ)) := by
    rw [show (169 / 400 : ℝ) - Real.pi * Real.exp (1353 / 800 : ℝ) =
      -(Real.pi * Real.exp (1353 / 800 : ℝ) - (169 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (169 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (169 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1352_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1037173191242863 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1352_endpointUpper :
    hpThetaJensenKernelEndpointUpper (169 / 200 : ℝ) (1353 / 1600 : ℝ) ≤ (40907 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1353 / 800 : ℝ)) (85235491036519187 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1353 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1352_product_upper
  have hD : (162399485883628247 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (169 / 100 : ℝ) - (1353 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1352_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1352_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (169 / 100 : ℝ) - (1353 / 3200 : ℝ)) ≤
      (1 / (162399485883628247 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (162399485883628247 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1353 / 3200 : ℝ) - Real.pi * Real.exp (169 / 100 : ℝ)) ≤
      (2 / (162399485883628247 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1353 / 3200 : ℝ) - Real.pi * Real.exp (169 / 100 : ℝ) =
      -(Real.pi * Real.exp (169 / 100 : ℝ) - (1353 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (85235491036519187 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (85235491036519187 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1352_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (169 / 200 : ℝ) (1353 / 1600 : ℝ)) :
    (318581 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40907 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1352_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1352_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1353_leftExp :
    (13565648229 / 2500000000 : ℝ) ≤ Real.exp (1353 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1353 / 800 : ℝ) (527136569917 / 500000000000 : ℝ)
    (13565648229 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1353_rightExp :
    Real.exp (677 / 400 : ℝ) ≤ (5433046357 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (677 / 400 : ℝ) (65894645199 / 62500000000 : ℝ)
    (5433046357 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1353_denomUpper :
    Real.exp (16645607903826701 / 1000000000000000 : ℝ) ≤ (33894220950909683 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (16645607903826701 / 1000000000000000 : ℝ) (84116122291 /
    50000000000 : ℝ) (33894220950909683 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1353_denomLower :
    (82921562832530201 / 5000000000 : ℝ) ≤ Real.exp (5194989931380071 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5194989931380071 / 312500000000000 : ℝ) (1681185153369 /
    1000000000000 : ℝ) (82921562832530201 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1353_product_lower :
    (5327216493880071 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1353 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1353_leftExp
    (by norm_num : (0 : ℝ) ≤ (13565648229 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1353_product_upper :
    Real.pi * Real.exp (677 / 400 : ℝ) ≤ (17068420403826701 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1353_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1353_endpointLower :
    (250221 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1353 / 1600 : ℝ) (677 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5327216493880071 / 312500000000000 : ℝ) (Real.pi * Real.exp (1353 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1353_product_lower
  have hD : Real.exp (Real.pi * Real.exp (677 / 400 : ℝ) - (1353 / 3200 : ℝ)) ≤
      (33894220950909683 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1353_denomUpper
    linarith [hpThetaJensenCell1353_product_upper]
  have hi : (1 / (33894220950909683 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (677 / 400 : ℝ) - (1353 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (33894220950909683 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (33894220950909683 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1353 / 3200 : ℝ) - Real.pi * Real.exp (677 / 400 : ℝ)) := by
    rw [show (1353 / 3200 : ℝ) - Real.pi * Real.exp (677 / 400 : ℝ) =
      -(Real.pi * Real.exp (677 / 400 : ℝ) - (1353 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1353 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1353 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1353_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (33894220950909683 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1353_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1353 / 1600 : ℝ) (677 / 800 : ℝ) ≤ (642603 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (677 / 400 : ℝ)) (17068420403826701 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (677 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1353_product_upper
  have hD : (82921562832530201 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1353 / 800 : ℝ) - (677 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1353_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1353_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1353 / 800 : ℝ) - (677 / 1600 : ℝ)) ≤
      (1 / (82921562832530201 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (82921562832530201 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((677 / 1600 : ℝ) - Real.pi * Real.exp (1353 / 800 : ℝ)) ≤
      (2 / (82921562832530201 / 5000000000 : ℝ) : ℝ) := by
    rw [show (677 / 1600 : ℝ) - Real.pi * Real.exp (1353 / 800 : ℝ) =
      -(Real.pi * Real.exp (1353 / 800 : ℝ) - (677 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17068420403826701 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (17068420403826701 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1353_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1353 / 1600 : ℝ) (677 / 800 : ℝ)) :
    (250221 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (642603 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1353_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1353_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1354_leftExp :
    (54330463567 / 10000000000 : ℝ) ≤ Real.exp (677 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (677 / 400 : ℝ) (1054314323183 / 1000000000000 : ℝ)
    (54330463567 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1354_rightExp :
    Real.exp (271 / 160 : ℝ) ≤ (54398419113 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (271 / 160 : ℝ) (527177754071 / 500000000000 : ℝ)
    (54398419113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1354_denomUpper :
    Real.exp (166666442696467009 / 10000000000000000 : ℝ) ≤ (86536961575321231 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (166666442696467009 / 10000000000000000 : ℝ)
    (1683428745363 / 1000000000000 : ℝ) (86536961575321231 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1354_denomLower :
    (16936429807624001 / 1000000000 : ℝ) ≤ Real.exp (20806221837297333 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (20806221837297333 / 1250000000000000 : ℝ) (841144651303
    / 500000000000 : ℝ) (16936429807624001 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1354_product_lower :
    (21335518712297333 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (677 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1354_leftExp
    (by norm_num : (0 : ℝ) ≤ (54330463567 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1354_product_upper :
    Real.pi * Real.exp (271 / 160 : ℝ) ≤ (170897692696467009 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1354_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1354_endpointLower :
    (49131 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (677 / 800 : ℝ) (271 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21335518712297333 / 1250000000000000 : ℝ) (Real.pi * Real.exp (677 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1354_product_lower
  have hD : Real.exp (Real.pi * Real.exp (271 / 160 : ℝ) - (677 / 1600 : ℝ)) ≤
      (86536961575321231 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1354_denomUpper
    linarith [hpThetaJensenCell1354_product_upper]
  have hi : (1 / (86536961575321231 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (271 / 160 : ℝ) - (677 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (86536961575321231 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (86536961575321231 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((677 / 1600 : ℝ) - Real.pi * Real.exp (271 / 160 : ℝ)) := by
    rw [show (677 / 1600 : ℝ) - Real.pi * Real.exp (271 / 160 : ℝ) =
      -(Real.pi * Real.exp (271 / 160 : ℝ) - (677 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (677 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (677 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1354_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (86536961575321231 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1354_endpointUpper :
    hpThetaJensenKernelEndpointUpper (677 / 800 : ℝ) (271 / 320 : ℝ) ≤ (315447 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (271 / 160 : ℝ)) (170897692696467009 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (271 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1354_product_upper
  have hD : (16936429807624001 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (677 / 400 : ℝ) - (271 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1354_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1354_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (677 / 400 : ℝ) - (271 / 640 : ℝ)) ≤
      (1 / (16936429807624001 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16936429807624001 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((271 / 640 : ℝ) - Real.pi * Real.exp (677 / 400 : ℝ)) ≤
      (2 / (16936429807624001 / 1000000000 : ℝ) : ℝ) := by
    rw [show (271 / 640 : ℝ) - Real.pi * Real.exp (677 / 400 : ℝ) =
      -(Real.pi * Real.exp (677 / 400 : ℝ) - (271 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (170897692696467009 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (170897692696467009 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1354_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (677 / 800 : ℝ) (271 / 320 : ℝ)) :
    (49131 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (315447 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1354_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1354_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1355_leftExp :
    (54398419111 / 10000000000 : ℝ) ≤ Real.exp (271 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (271 / 160 : ℝ) (1054355508141 / 1000000000000 : ℝ)
    (54398419111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1355_rightExp :
    Real.exp (339 / 200 : ℝ) ≤ (54466459653 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (339 / 200 : ℝ) (263599173677 / 250000000000 : ℝ)
    (54466459653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1355_denomUpper :
    Real.exp (166877073380647229 / 10000000000000000 : ℝ) ≤ (176758054385766989 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (166877073380647229 / 10000000000000000 : ℝ)
    (421134294521 / 250000000000 : ℝ) (176758054385766989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1355_denomLower :
    (172964844727901919 / 10000000000 : ℝ) ≤ Real.exp (20832517286470589 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (20832517286470589 / 1250000000000000 : ℝ) (1683395580013
    / 1000000000000 : ℝ) (172964844727901919 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1355_product_lower :
    (21362204786470589 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (271 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1355_leftExp
    (by norm_num : (0 : ℝ) ≤ (54398419111 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1355_product_upper :
    Real.pi * Real.exp (339 / 200 : ℝ) ≤ (171111448380647229 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1355_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1355_endpointLower :
    (120583 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (271 / 320 : ℝ) (339 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21362204786470589 / 1250000000000000 : ℝ) (Real.pi * Real.exp (271 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1355_product_lower
  have hD : Real.exp (Real.pi * Real.exp (339 / 200 : ℝ) - (271 / 640 : ℝ)) ≤
      (176758054385766989 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1355_denomUpper
    linarith [hpThetaJensenCell1355_product_upper]
  have hi : (1 / (176758054385766989 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (339 / 200 : ℝ) - (271 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (176758054385766989 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (176758054385766989 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((271 / 640 : ℝ) - Real.pi * Real.exp (339 / 200 : ℝ)) := by
    rw [show (271 / 640 : ℝ) - Real.pi * Real.exp (339 / 200 : ℝ) =
      -(Real.pi * Real.exp (339 / 200 : ℝ) - (271 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (271 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (271 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1355_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (176758054385766989 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1355_endpointUpper :
    hpThetaJensenKernelEndpointUpper (271 / 320 : ℝ) (339 / 400 : ℝ) ≤ (1238763 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (339 / 200 : ℝ)) (171111448380647229 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (339 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1355_product_upper
  have hD : (172964844727901919 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (271 / 160 : ℝ) - (339 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1355_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1355_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (271 / 160 : ℝ) - (339 / 800 : ℝ)) ≤
      (1 / (172964844727901919 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (172964844727901919 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((339 / 800 : ℝ) - Real.pi * Real.exp (271 / 160 : ℝ)) ≤
      (2 / (172964844727901919 / 10000000000 : ℝ) : ℝ) := by
    rw [show (339 / 800 : ℝ) - Real.pi * Real.exp (271 / 160 : ℝ) =
      -(Real.pi * Real.exp (271 / 160 : ℝ) - (339 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (171111448380647229 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (171111448380647229 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1355_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (271 / 320 : ℝ) (339 / 400 : ℝ)) :
    (120583 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1238763 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1355_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1355_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1356_leftExp :
    (1089329193 / 200000000 : ℝ) ≤ Real.exp (339 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (339 / 200 : ℝ) (1054396694707 / 1000000000000 : ℝ)
    (1089329193 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1356_rightExp :
    Real.exp (1357 / 800 : ℝ) ≤ (27267292649 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1357 / 800 : ℝ) (263609470721 / 250000000000 : ℝ)
    (27267292649 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1356_denomUpper :
    Real.exp (83543985715049857 / 5000000000000000 : ℝ) ≤ (1444203474332707 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83543985715049857 / 5000000000000000 : ℝ) (52676492157 /
    31250000000 : ℝ) (1444203474332707 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1356_denomLower :
    (88323326404394641 / 5000000000 : ℝ) ≤ Real.exp (417176922261907 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (417176922261907 / 25000000000000 : ℝ) (1684503990521 /
    1000000000000 : ℝ) (88323326404394641 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1356_product_lower :
    (427778484761907 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (339 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1356_leftExp
    (by norm_num : (0 : ℝ) ≤ (1089329193 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1356_product_upper :
    Real.pi * Real.exp (1357 / 800 : ℝ) ≤ (85662735715049857 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1356_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1356_endpointLower :
    (1183763 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (339 / 400 : ℝ) (1357 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (427778484761907 / 25000000000000 : ℝ) (Real.pi * Real.exp (339 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1356_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1357 / 800 : ℝ) - (339 / 800 : ℝ)) ≤
      (1444203474332707 / 80000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1356_denomUpper
    linarith [hpThetaJensenCell1356_product_upper]
  have hi : (1 / (1444203474332707 / 80000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1357 / 800 : ℝ) - (339 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1444203474332707 / 80000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1444203474332707 / 80000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((339 / 800 : ℝ) - Real.pi * Real.exp (1357 / 800 : ℝ)) := by
    rw [show (339 / 800 : ℝ) - Real.pi * Real.exp (1357 / 800 : ℝ) =
      -(Real.pi * Real.exp (1357 / 800 : ℝ) - (339 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (339 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (339 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1356_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1444203474332707 / 80000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1356_endpointUpper :
    hpThetaJensenKernelEndpointUpper (339 / 400 : ℝ) (1357 / 1600 : ℝ) ≤ (608063 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1357 / 800 : ℝ)) (85662735715049857 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1357 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1356_product_upper
  have hD : (88323326404394641 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (339 / 200 : ℝ) - (1357 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1356_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1356_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (339 / 200 : ℝ) - (1357 / 3200 : ℝ)) ≤
      (1 / (88323326404394641 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (88323326404394641 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1357 / 3200 : ℝ) - Real.pi * Real.exp (339 / 200 : ℝ)) ≤
      (2 / (88323326404394641 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1357 / 3200 : ℝ) - Real.pi * Real.exp (339 / 200 : ℝ) =
      -(Real.pi * Real.exp (339 / 200 : ℝ) - (1357 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (85662735715049857 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (85662735715049857 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1356_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (339 / 400 : ℝ) (1357 / 1600 : ℝ)) :
    (1183763 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (608063 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1356_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1356_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1357_leftExp :
    (3408411581 / 625000000 : ℝ) ≤ Real.exp (1357 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1357 / 800 : ℝ) (1054437882883 / 1000000000000 : ℝ)
    (3408411581 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1357_rightExp :
    Real.exp (679 / 400 : ℝ) ≤ (6825349519 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (679 / 400 : ℝ) (263619768167 / 250000000000 : ℝ)
    (6825349519 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1357_denomUpper :
    Real.exp (20912392146443767 / 1250000000000000 : ℝ) ≤ (46094511710053223 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (20912392146443767 / 1250000000000000 : ℝ) (421690115793
    / 250000000000 : ℝ) (46094511710053223 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1357_denomLower :
    (180411657158414457 / 10000000000 : ℝ) ≤ Real.exp (1305325522572119 / 78125000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1305325522572119 / 78125000000000 : ℝ) (42140363481 /
    25000000000 : ℝ) (180411657158414457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1357_product_lower :
    (1338479819447119 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (1357 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1357_leftExp
    (by norm_num : (0 : ℝ) ≤ (3408411581 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1357_product_upper :
    Real.pi * Real.exp (679 / 400 : ℝ) ≤ (21442470271443767 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1357_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1357_endpointLower :
    (1162069 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1357 / 1600 : ℝ) (679 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1338479819447119 / 78125000000000 : ℝ) (Real.pi * Real.exp (1357 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1357_product_lower
  have hD : Real.exp (Real.pi * Real.exp (679 / 400 : ℝ) - (1357 / 3200 : ℝ)) ≤
      (46094511710053223 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1357_denomUpper
    linarith [hpThetaJensenCell1357_product_upper]
  have hi : (1 / (46094511710053223 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (679 / 400 : ℝ) - (1357 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (46094511710053223 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (46094511710053223 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1357 / 3200 : ℝ) - Real.pi * Real.exp (679 / 400 : ℝ)) := by
    rw [show (1357 / 3200 : ℝ) - Real.pi * Real.exp (679 / 400 : ℝ) =
      -(Real.pi * Real.exp (679 / 400 : ℝ) - (1357 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1357 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1357 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1357_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (46094511710053223 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1357_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1357 / 1600 : ℝ) (679 / 800 : ℝ) ≤ (1193871 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (679 / 400 : ℝ)) (21442470271443767 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (679 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1357_product_upper
  have hD : (180411657158414457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1357 / 800 : ℝ) - (679 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1357_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1357_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1357 / 800 : ℝ) - (679 / 1600 : ℝ)) ≤
      (1 / (180411657158414457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (180411657158414457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((679 / 1600 : ℝ) - Real.pi * Real.exp (1357 / 800 : ℝ)) ≤
      (2 / (180411657158414457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (679 / 1600 : ℝ) - Real.pi * Real.exp (1357 / 800 : ℝ) =
      -(Real.pi * Real.exp (1357 / 800 : ℝ) - (679 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21442470271443767 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (21442470271443767 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1357_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1357 / 1600 : ℝ) (679 / 800 : ℝ)) :
    (1162069 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1193871 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1357_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1357_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1358_leftExp :
    (1092055923 / 200000000 : ℝ) ≤ Real.exp (679 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (679 / 400 : ℝ) (1054479072667 / 1000000000000 : ℝ)
    (1092055923 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1358_rightExp :
    Real.exp (1359 / 800 : ℝ) ≤ (54671092323 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1359 / 800 : ℝ) (1054520264061 / 1000000000000 : ℝ)
    (54671092323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1358_denomUpper :
    Real.exp (167510570944290539 / 10000000000000000 : ℝ) ≤ (188317925847712179 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (167510570944290539 / 10000000000000000 : ℝ)
    (337575065119 / 200000000000 : ℝ) (188317925847712179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1358_denomLower :
    (184261840319103453 / 10000000000 : ℝ) ≤ Real.exp (418232081406177 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (418232081406177 / 25000000000000 : ℝ) (843363615553 /
    500000000000 : ℝ) (184261840319103453 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1358_product_lower :
    (428849268906177 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (679 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1358_leftExp
    (by norm_num : (0 : ℝ) ≤ (1092055923 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1358_product_upper :
    Real.pi * Real.exp (1359 / 800 : ℝ) ≤ (171754320944290539 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1358_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1358_endpointLower :
    (570371 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (679 / 800 : ℝ) (1359 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (428849268906177 / 25000000000000 : ℝ) (Real.pi * Real.exp (679 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1358_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1359 / 800 : ℝ) - (679 / 1600 : ℝ)) ≤
      (188317925847712179 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1358_denomUpper
    linarith [hpThetaJensenCell1358_product_upper]
  have hi : (1 / (188317925847712179 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1359 / 800 : ℝ) - (679 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (188317925847712179 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (188317925847712179 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((679 / 1600 : ℝ) - Real.pi * Real.exp (1359 / 800 : ℝ)) := by
    rw [show (679 / 1600 : ℝ) - Real.pi * Real.exp (1359 / 800 : ℝ) =
      -(Real.pi * Real.exp (1359 / 800 : ℝ) - (679 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (679 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (679 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1358_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (188317925847712179 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1358_endpointUpper :
    hpThetaJensenKernelEndpointUpper (679 / 800 : ℝ) (1359 / 1600 : ℝ) ≤ (1171991 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1359 / 800 : ℝ)) (171754320944290539 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1359 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1358_product_upper
  have hD : (184261840319103453 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (679 / 400 : ℝ) - (1359 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1358_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1358_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (679 / 400 : ℝ) - (1359 / 3200 : ℝ)) ≤
      (1 / (184261840319103453 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (184261840319103453 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1359 / 3200 : ℝ) - Real.pi * Real.exp (679 / 400 : ℝ)) ≤
      (2 / (184261840319103453 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1359 / 3200 : ℝ) - Real.pi * Real.exp (679 / 400 : ℝ) =
      -(Real.pi * Real.exp (679 / 400 : ℝ) - (1359 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (171754320944290539 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (171754320944290539 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1358_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (679 / 800 : ℝ) (1359 / 1600 : ℝ)) :
    (570371 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1171991 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1358_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1358_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1359_leftExp :
    (54671092321 / 10000000000 : ℝ) ≤ Real.exp (1359 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1359 / 800 : ℝ) (52726013203 / 50000000000 : ℝ)
    (54671092321 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1359_rightExp :
    Real.exp (17 / 10 : ℝ) ≤ (54739473919 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 10 : ℝ) (131820182133 / 125000000000 : ℝ)
    (54739473919 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1359_denomUpper :
    Real.exp (167722273087612967 / 10000000000000000 : ℝ) ≤ (24043394506277043 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (167722273087612967 / 10000000000000000 : ℝ)
    (1688992341371 / 1000000000000 : ℝ) (24043394506277043 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1359_denomLower :
    (188199234884031687 / 10000000000 : ℝ) ≤ Real.exp (20938033283364379 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (20938033283364379 / 1250000000000000 : ℝ) (421960517801
    / 250000000000 : ℝ) (188199234884031687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1359_product_lower :
    (21469283283364379 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1359 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1359_leftExp
    (by norm_num : (0 : ℝ) ≤ (54671092321 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1359_product_upper :
    Real.pi * Real.exp (17 / 10 : ℝ) ≤ (171969148087612967 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1359_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1359_endpointLower :
    (44791 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (1359 / 1600 : ℝ) (17 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (21469283283364379 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1359 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1359_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 10 : ℝ) - (1359 / 3200 : ℝ)) ≤
      (24043394506277043 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1359_denomUpper
    linarith [hpThetaJensenCell1359_product_upper]
  have hi : (1 / (24043394506277043 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 10 : ℝ) - (1359 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24043394506277043 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24043394506277043 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1359 / 3200 : ℝ) - Real.pi * Real.exp (17 / 10 : ℝ)) := by
    rw [show (1359 / 3200 : ℝ) - Real.pi * Real.exp (17 / 10 : ℝ) =
      -(Real.pi * Real.exp (17 / 10 : ℝ) - (1359 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1359 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1359 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1359_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24043394506277043 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1359_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1359 / 1600 : ℝ) (17 / 20 : ℝ) ≤ (1150481 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 10 : ℝ)) (171969148087612967 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 20 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1359_product_upper
  have hD : (188199234884031687 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1359 / 800 : ℝ) - (17 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell1359_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1359_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1359 / 800 : ℝ) - (17 / 40 : ℝ)) ≤
      (1 / (188199234884031687 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (188199234884031687 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 40 : ℝ) - Real.pi * Real.exp (1359 / 800 : ℝ)) ≤
      (2 / (188199234884031687 / 10000000000 : ℝ) : ℝ) := by
    rw [show (17 / 40 : ℝ) - Real.pi * Real.exp (1359 / 800 : ℝ) =
      -(Real.pi * Real.exp (1359 / 800 : ℝ) - (17 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (171969148087612967 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (171969148087612967 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1359_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1359 / 1600 : ℝ) (17 / 20 : ℝ)) :
    (44791 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1150481 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1359_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1359_endpointUpper

def hpThetaJensenCellsBatch067Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3097 / 19531250 : ℝ)
  | 1 => (1557269 / 10000000000 : ℝ)
  | 2 => (764671 / 5000000000 : ℝ)
  | 3 => (375469 / 2500000000 : ℝ)
  | 4 => (92179 / 625000000 : ℝ)
  | 5 => (14483 / 100000000 : ℝ)
  | 6 => (44443 / 312500000 : ℝ)
  | 7 => (1396487 / 10000000000 : ℝ)
  | 8 => (54849 / 400000000 : ℝ)
  | 9 => (84149 / 625000000 : ℝ)
  | 10 => (660979 / 5000000000 : ℝ)
  | 11 => (64897 / 500000000 : ℝ)
  | 12 => (318581 / 2500000000 : ℝ)
  | 13 => (250221 / 2000000000 : ℝ)
  | 14 => (49131 / 400000000 : ℝ)
  | 15 => (120583 / 1000000000 : ℝ)
  | 16 => (1183763 / 10000000000 : ℝ)
  | 17 => (1162069 / 10000000000 : ℝ)
  | 18 => (570371 / 5000000000 : ℝ)
  | 19 => (44791 / 400000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch067Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (203541 / 1250000000 : ℝ)
  | 1 => (159921 / 1000000000 : ℝ)
  | 2 => (392643 / 2500000000 : ℝ)
  | 3 => (771203 / 5000000000 : ℝ)
  | 4 => (302941 / 2000000000 : ℝ)
  | 5 => (1487463 / 10000000000 : ℝ)
  | 6 => (1460671 / 10000000000 : ℝ)
  | 7 => (358581 / 2500000000 : ℝ)
  | 8 => (704207 / 5000000000 : ℝ)
  | 9 => (172867 / 1250000000 : ℝ)
  | 10 => (678941 / 5000000000 : ℝ)
  | 11 => (1333247 / 10000000000 : ℝ)
  | 12 => (40907 / 312500000 : ℝ)
  | 13 => (642603 / 5000000000 : ℝ)
  | 14 => (315447 / 2500000000 : ℝ)
  | 15 => (1238763 / 10000000000 : ℝ)
  | 16 => (608063 / 5000000000 : ℝ)
  | 17 => (1193871 / 10000000000 : ℝ)
  | 18 => (1171991 / 10000000000 : ℝ)
  | 19 => (1150481 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch067_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch067Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch067Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1340_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1341_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1342_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1343_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1344_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1345_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1346_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1347_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1348_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1349_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1350_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1351_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1352_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1353_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1354_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1355_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1356_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1357_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1358_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1359_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper] at h ⊢
    exact h

end HodgeProofHP
