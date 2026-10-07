import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1080_leftExp :
    (19287127653 / 5000000000 : ℝ) ≤ Real.exp (27 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 20 : ℝ) (521545019899 / 500000000000 : ℝ)
    (19287127653 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1080_rightExp :
    Real.exp (1081 / 800 : ℝ) ≤ (9655625819 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1081 / 800 : ℝ) (10431307863 / 10000000000 : ℝ)
    (9655625819 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1080_denomUpper :
    Real.exp (29490296483589667 / 2500000000000000 : ℝ) ≤ (66368074417883 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29490296483589667 / 2500000000000000 : ℝ) (144575070551
    / 100000000000 : ℝ) (66368074417883 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1080_denomLower :
    (326745029482597 / 2500000000 : ℝ) ≤ Real.exp (7362902929705447 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7362902929705447 / 625000000000000 : ℝ) (1445051767937 /
    1000000000000 : ℝ) (326745029482597 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1080_product_lower :
    (7574035742205447 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1080_leftExp
    (by norm_num : (0 : ℝ) ≤ (19287127653 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1080_product_upper :
    Real.pi * Real.exp (1081 / 800 : ℝ) ≤ (30334046483589667 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1080_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1080_endpointLower :
    (1551099 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 40 : ℝ) (1081 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7574035742205447 / 625000000000000 : ℝ) (Real.pi * Real.exp (27 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell1080_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1081 / 800 : ℝ) - (27 / 80 : ℝ)) ≤
      (66368074417883 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1080_denomUpper
    linarith [hpThetaJensenCell1080_product_upper]
  have hi : (1 / (66368074417883 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1081 / 800 : ℝ) - (27 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (66368074417883 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (66368074417883 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 80 : ℝ) - Real.pi * Real.exp (1081 / 800 : ℝ)) := by
    rw [show (27 / 80 : ℝ) - Real.pi * Real.exp (1081 / 800 : ℝ) =
      -(Real.pi * Real.exp (1081 / 800 : ℝ) - (27 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 20 : ℝ)) := by
    have h := hpThetaJensenCell1080_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (66368074417883 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1080_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 40 : ℝ) (1081 / 1600 : ℝ) ≤ (19795873 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1081 / 800 : ℝ)) (30334046483589667 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1081 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1080_product_upper
  have hD : (326745029482597 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 20 : ℝ) - (1081 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1080_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1080_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 20 : ℝ) - (1081 / 3200 : ℝ)) ≤
      (1 / (326745029482597 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (326745029482597 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1081 / 3200 : ℝ) - Real.pi * Real.exp (27 / 20 : ℝ)) ≤
      (2 / (326745029482597 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1081 / 3200 : ℝ) - Real.pi * Real.exp (27 / 20 : ℝ) =
      -(Real.pi * Real.exp (27 / 20 : ℝ) - (1081 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30334046483589667 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (30334046483589667 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1080_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 40 : ℝ) (1081 / 1600 : ℝ)) :
    (1551099 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (19795873 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1080_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1080_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1081_leftExp :
    (19311251637 / 5000000000 : ℝ) ≤ Real.exp (1081 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1081 / 800 : ℝ) (1043130786299 / 1000000000000 : ℝ)
    (19311251637 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1081_rightExp :
    Real.exp (541 / 400 : ℝ) ≤ (38670811591 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (541 / 400 : ℝ) (130396441799 / 125000000000 : ℝ)
    (38670811591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1081_denomUpper :
    Real.exp (118109825998604463 / 10000000000000000 : ℝ) ≤ (1347238760024353 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (118109825998604463 / 10000000000000000 : ℝ)
    (289284482599 / 200000000000 : ℝ) (1347238760024353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1081_denomLower :
    (82907938898277 / 625000000 : ℝ) ≤ Real.exp (7372181081598263 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7372181081598263 / 625000000000000 : ℝ) (722861146973 /
    500000000000 : ℝ) (82907938898277 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1081_product_lower :
    (7583509206598263 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1081 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1081_leftExp
    (by norm_num : (0 : ℝ) ≤ (19311251637 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1081_product_upper :
    Real.pi * Real.exp (541 / 400 : ℝ) ≤ (121487950998604463 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1081_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1081_endpointLower :
    (38307741 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1081 / 1600 : ℝ) (541 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7583509206598263 / 625000000000000 : ℝ) (Real.pi * Real.exp (1081 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1081_product_lower
  have hD : Real.exp (Real.pi * Real.exp (541 / 400 : ℝ) - (1081 / 3200 : ℝ)) ≤
      (1347238760024353 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1081_denomUpper
    linarith [hpThetaJensenCell1081_product_upper]
  have hi : (1 / (1347238760024353 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (541 / 400 : ℝ) - (1081 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1347238760024353 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1347238760024353 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1081 / 3200 : ℝ) - Real.pi * Real.exp (541 / 400 : ℝ)) := by
    rw [show (1081 / 3200 : ℝ) - Real.pi * Real.exp (541 / 400 : ℝ) =
      -(Real.pi * Real.exp (541 / 400 : ℝ) - (1081 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1081 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1081 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1081_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1347238760024353 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1081_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1081 / 1600 : ℝ) (541 / 800 : ℝ) ≤ (488911 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (541 / 400 : ℝ)) (121487950998604463 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (541 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1081_product_upper
  have hD : (82907938898277 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1081 / 800 : ℝ) - (541 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1081_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1081_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1081 / 800 : ℝ) - (541 / 1600 : ℝ)) ≤
      (1 / (82907938898277 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (82907938898277 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((541 / 1600 : ℝ) - Real.pi * Real.exp (1081 / 800 : ℝ)) ≤
      (2 / (82907938898277 / 625000000 : ℝ) : ℝ) := by
    rw [show (541 / 1600 : ℝ) - Real.pi * Real.exp (1081 / 800 : ℝ) =
      -(Real.pi * Real.exp (1081 / 800 : ℝ) - (541 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (121487950998604463 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (121487950998604463 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1081_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1081 / 1600 : ℝ) (541 / 800 : ℝ)) :
    (38307741 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (488911 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1081_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1081_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1082_leftExp :
    (38670811589 / 10000000000 : ℝ) ≤ Real.exp (541 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (541 / 400 : ℝ) (1043171534391 / 1000000000000 : ℝ)
    (38670811589 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1082_rightExp :
    Real.exp (1083 / 800 : ℝ) ≤ (3871918033 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1083 / 800 : ℝ) (260803071019 / 250000000000 : ℝ)
    (3871918033 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1082_denomUpper :
    Real.exp (11825865589046569 / 1000000000000000 : ℝ) ≤ (683719825937933 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11825865589046569 / 1000000000000000 : ℝ) (723547645497
    / 500000000000 : ℝ) (683719825937933 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1082_denomLower :
    (269278358280711 / 2000000000 : ℝ) ≤ Real.exp (14762942165188711 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14762942165188711 / 1250000000000000 : ℝ) (1446393988013
    / 1000000000000 : ℝ) (269278358280711 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1082_product_lower :
    (15185989040188711 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (541 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1082_leftExp
    (by norm_num : (0 : ℝ) ≤ (38670811589 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1082_product_upper :
    Real.pi * Real.exp (1083 / 800 : ℝ) ≤ (12163990589046569 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1082_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1082_endpointLower :
    (37842969 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (541 / 800 : ℝ) (1083 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15185989040188711 / 1250000000000000 : ℝ) (Real.pi * Real.exp (541 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1082_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1083 / 800 : ℝ) - (541 / 1600 : ℝ)) ≤
      (683719825937933 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1082_denomUpper
    linarith [hpThetaJensenCell1082_product_upper]
  have hi : (1 / (683719825937933 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1083 / 800 : ℝ) - (541 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (683719825937933 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (683719825937933 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((541 / 1600 : ℝ) - Real.pi * Real.exp (1083 / 800 : ℝ)) := by
    rw [show (541 / 1600 : ℝ) - Real.pi * Real.exp (1083 / 800 : ℝ) =
      -(Real.pi * Real.exp (1083 / 800 : ℝ) - (541 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (541 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (541 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1082_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (683719825937933 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1082_endpointUpper :
    hpThetaJensenKernelEndpointUpper (541 / 800 : ℝ) (1083 / 1600 : ℝ) ≤ (77278127 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1083 / 800 : ℝ)) (12163990589046569 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1083 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1082_product_upper
  have hD : (269278358280711 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (541 / 400 : ℝ) - (1083 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1082_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1082_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (541 / 400 : ℝ) - (1083 / 3200 : ℝ)) ≤
      (1 / (269278358280711 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (269278358280711 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1083 / 3200 : ℝ) - Real.pi * Real.exp (541 / 400 : ℝ)) ≤
      (2 / (269278358280711 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1083 / 3200 : ℝ) - Real.pi * Real.exp (541 / 400 : ℝ) =
      -(Real.pi * Real.exp (541 / 400 : ℝ) - (1083 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12163990589046569 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (12163990589046569 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1082_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (541 / 800 : ℝ) (1083 / 1600 : ℝ)) :
    (37842969 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (77278127 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1082_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1082_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1083_leftExp :
    (4839897541 / 1250000000 : ℝ) ≤ Real.exp (1083 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1083 / 800 : ℝ) (41728491363 / 40000000000 : ℝ)
    (4839897541 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1083_rightExp :
    Real.exp (271 / 200 : ℝ) ≤ (1211487799 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (271 / 200 : ℝ) (130406629419 / 125000000000 : ℝ)
    (1211487799 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1083_denomUpper :
    Real.exp (3700239870173807 / 312500000000000 : ℝ) ≤ (69398491088241 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3700239870173807 / 312500000000000 : ℝ) (361942335479 /
    250000000000 : ℝ) (69398491088241 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1083_denomLower :
    (1366579976921991 / 10000000000 : ℝ) ≤ Real.exp (1847693236953159 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1847693236953159 / 156250000000000 : ℝ) (1447066852569 /
    1000000000000 : ℝ) (1366579976921991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1083_product_lower :
    (1900622924453159 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1083 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1083_leftExp
    (by norm_num : (0 : ℝ) ≤ (4839897541 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1083_product_upper :
    Real.pi * Real.exp (271 / 200 : ℝ) ≤ (3806001588923807 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1083_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1083_endpointLower :
    (9345779 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1083 / 1600 : ℝ) (271 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1900622924453159 / 156250000000000 : ℝ) (Real.pi * Real.exp (1083 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1083_product_lower
  have hD : Real.exp (Real.pi * Real.exp (271 / 200 : ℝ) - (1083 / 3200 : ℝ)) ≤
      (69398491088241 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1083_denomUpper
    linarith [hpThetaJensenCell1083_product_upper]
  have hi : (1 / (69398491088241 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (271 / 200 : ℝ) - (1083 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (69398491088241 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (69398491088241 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1083 / 3200 : ℝ) - Real.pi * Real.exp (271 / 200 : ℝ)) := by
    rw [show (1083 / 3200 : ℝ) - Real.pi * Real.exp (271 / 200 : ℝ) =
      -(Real.pi * Real.exp (271 / 200 : ℝ) - (1083 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1083 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1083 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1083_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (69398491088241 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1083_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1083 / 1600 : ℝ) (271 / 400 : ℝ) ≤ (15268101 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (271 / 200 : ℝ)) (3806001588923807 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (271 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1083_product_upper
  have hD : (1366579976921991 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1083 / 800 : ℝ) - (271 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1083_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1083_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1083 / 800 : ℝ) - (271 / 800 : ℝ)) ≤
      (1 / (1366579976921991 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1366579976921991 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((271 / 800 : ℝ) - Real.pi * Real.exp (1083 / 800 : ℝ)) ≤
      (2 / (1366579976921991 / 10000000000 : ℝ) : ℝ) := by
    rw [show (271 / 800 : ℝ) - Real.pi * Real.exp (1083 / 800 : ℝ) =
      -(Real.pi * Real.exp (1083 / 800 : ℝ) - (271 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3806001588923807 / 312500000000000 : ℝ) ^ 2 - 6 *
      (3806001588923807 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1083_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1083 / 1600 : ℝ) (271 / 400 : ℝ)) :
    (9345779 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15268101 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1083_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1083_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1084_leftExp :
    (19383804783 / 5000000000 : ℝ) ≤ Real.exp (271 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (271 / 200 : ℝ) (1043253035351 / 1000000000000 : ℝ)
    (19383804783 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1084_rightExp :
    Real.exp (217 / 160 : ℝ) ≤ (38816099379 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (217 / 160 : ℝ) (1043293788219 / 1000000000000 : ℝ)
    (38816099379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1084_denomUpper :
    Real.exp (118556886096370747 / 10000000000000000 : ℝ) ≤ (1408835032342963 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (118556886096370747 / 10000000000000000 : ℝ) (9052778551
    / 6250000000 : ℝ) (1408835032342963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1084_denomLower :
    (346774308319783 / 2500000000 : ℝ) ≤ Real.exp (7400086691979317 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7400086691979317 / 625000000000000 : ℝ) (57909635601 /
    40000000000 : ℝ) (346774308319783 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1084_product_lower :
    (7612000754479317 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (271 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1084_leftExp
    (by norm_num : (0 : ℝ) ≤ (19383804783 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1084_product_upper :
    Real.pi * Real.exp (217 / 160 : ℝ) ≤ (121944386096370747 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1084_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1084_endpointLower :
    (36928139 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (271 / 400 : ℝ) (217 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7612000754479317 / 625000000000000 : ℝ) (Real.pi * Real.exp (271 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1084_product_lower
  have hD : Real.exp (Real.pi * Real.exp (217 / 160 : ℝ) - (271 / 800 : ℝ)) ≤
      (1408835032342963 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1084_denomUpper
    linarith [hpThetaJensenCell1084_product_upper]
  have hi : (1 / (1408835032342963 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (217 / 160 : ℝ) - (271 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1408835032342963 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1408835032342963 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((271 / 800 : ℝ) - Real.pi * Real.exp (217 / 160 : ℝ)) := by
    rw [show (271 / 800 : ℝ) - Real.pi * Real.exp (217 / 160 : ℝ) =
      -(Real.pi * Real.exp (217 / 160 : ℝ) - (271 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (271 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (271 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1084_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1408835032342963 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1084_endpointUpper :
    hpThetaJensenKernelEndpointUpper (271 / 400 : ℝ) (217 / 320 : ℝ) ≤ (9426601 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (217 / 160 : ℝ)) (121944386096370747 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (217 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1084_product_upper
  have hD : (346774308319783 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (271 / 200 : ℝ) - (217 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1084_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1084_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (271 / 200 : ℝ) - (217 / 640 : ℝ)) ≤
      (1 / (346774308319783 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (346774308319783 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((217 / 640 : ℝ) - Real.pi * Real.exp (271 / 200 : ℝ)) ≤
      (2 / (346774308319783 / 2500000000 : ℝ) : ℝ) := by
    rw [show (217 / 640 : ℝ) - Real.pi * Real.exp (271 / 200 : ℝ) =
      -(Real.pi * Real.exp (271 / 200 : ℝ) - (217 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (121944386096370747 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (121944386096370747 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1084_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (271 / 400 : ℝ) (217 / 320 : ℝ)) :
    (36928139 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9426601 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1084_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1084_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1085_leftExp :
    (38816099377 / 10000000000 : ℝ) ≤ Real.exp (217 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (217 / 160 : ℝ) (521646894109 / 500000000000 : ℝ)
    (38816099377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1085_rightExp :
    Real.exp (543 / 400 : ℝ) ≤ (38864649841 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (543 / 400 : ℝ) (1043334542679 / 1000000000000 : ℝ)
    (38864649841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1085_denomUpper :
    Real.exp (118706286887936713 / 10000000000000000 : ℝ) ≤ (715020577685187 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (118706286887936713 / 10000000000000000 : ℝ)
    (1449120972187 / 1000000000000 : ℝ) (715020577685187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1085_denomLower :
    (703974659750431 / 5000000000 : ℝ) ≤ Real.exp (14818824659248523 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14818824659248523 / 1250000000000000 : ℝ) (72420805139 /
    50000000000 : ℝ) (703974659750431 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1085_product_lower :
    (15243043409248523 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (217 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1085_leftExp
    (by norm_num : (0 : ℝ) ≤ (38816099377 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1085_product_upper :
    Real.pi * Real.exp (543 / 400 : ℝ) ≤ (122096911887936713 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1085_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1085_endpointLower :
    (7295599 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (217 / 320 : ℝ) (543 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15243043409248523 / 1250000000000000 : ℝ) (Real.pi * Real.exp (217 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1085_product_lower
  have hD : Real.exp (Real.pi * Real.exp (543 / 400 : ℝ) - (217 / 640 : ℝ)) ≤
      (715020577685187 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1085_denomUpper
    linarith [hpThetaJensenCell1085_product_upper]
  have hi : (1 / (715020577685187 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (543 / 400 : ℝ) - (217 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (715020577685187 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (715020577685187 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((217 / 640 : ℝ) - Real.pi * Real.exp (543 / 400 : ℝ)) := by
    rw [show (217 / 640 : ℝ) - Real.pi * Real.exp (543 / 400 : ℝ) =
      -(Real.pi * Real.exp (543 / 400 : ℝ) - (217 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (217 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (217 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1085_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (715020577685187 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1085_endpointUpper :
    hpThetaJensenKernelEndpointUpper (217 / 320 : ℝ) (543 / 800 : ℝ) ≤ (18623737 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (543 / 400 : ℝ)) (122096911887936713 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (543 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1085_product_upper
  have hD : (703974659750431 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (217 / 160 : ℝ) - (543 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1085_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1085_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (217 / 160 : ℝ) - (543 / 1600 : ℝ)) ≤
      (1 / (703974659750431 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (703974659750431 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((543 / 1600 : ℝ) - Real.pi * Real.exp (217 / 160 : ℝ)) ≤
      (2 / (703974659750431 / 5000000000 : ℝ) : ℝ) := by
    rw [show (543 / 1600 : ℝ) - Real.pi * Real.exp (217 / 160 : ℝ) =
      -(Real.pi * Real.exp (217 / 160 : ℝ) - (543 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (122096911887936713 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (122096911887936713 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1085_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (217 / 320 : ℝ) (543 / 800 : ℝ)) :
    (7295599 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (18623737 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1085_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1085_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1086_leftExp :
    (38864649839 / 10000000000 : ℝ) ≤ Real.exp (543 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (543 / 400 : ℝ) (521667271339 / 500000000000 : ℝ)
    (38864649839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1086_rightExp :
    Real.exp (1087 / 800 : ℝ) ≤ (3891326103 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1087 / 800 : ℝ) (1043375298731 / 1000000000000 : ℝ)
    (3891326103 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1086_denomUpper :
    Real.exp (11885587845902079 / 1000000000000000 : ℝ) ≤ (1451594171234713 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (11885587845902079 / 1000000000000000 : ℝ) (289959711287
    / 200000000000 : ℝ) (1451594171234713 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1086_denomLower :
    (142914210365283 / 1000000000 : ℝ) ≤ Real.exp (14837499752125461 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14837499752125461 / 1250000000000000 : ℝ) (289818498659
    / 200000000000 : ℝ) (142914210365283 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1086_product_lower :
    (15262109127125461 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (543 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1086_leftExp
    (by norm_num : (0 : ℝ) ≤ (38864649839 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1086_product_upper :
    Real.pi * Real.exp (1087 / 800 : ℝ) ≤ (12224962845902079 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1086_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1086_endpointLower :
    (18016321 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (543 / 800 : ℝ) (1087 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15262109127125461 / 1250000000000000 : ℝ) (Real.pi * Real.exp (543 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1086_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1087 / 800 : ℝ) - (543 / 1600 : ℝ)) ≤
      (1451594171234713 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1086_denomUpper
    linarith [hpThetaJensenCell1086_product_upper]
  have hi : (1 / (1451594171234713 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1087 / 800 : ℝ) - (543 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1451594171234713 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1451594171234713 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((543 / 1600 : ℝ) - Real.pi * Real.exp (1087 / 800 : ℝ)) := by
    rw [show (543 / 1600 : ℝ) - Real.pi * Real.exp (1087 / 800 : ℝ) =
      -(Real.pi * Real.exp (1087 / 800 : ℝ) - (543 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (543 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (543 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1086_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1451594171234713 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1086_endpointUpper :
    hpThetaJensenKernelEndpointUpper (543 / 800 : ℝ) (1087 / 1600 : ℝ) ≤ (36793419 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1087 / 800 : ℝ)) (12224962845902079 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1087 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1086_product_upper
  have hD : (142914210365283 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (543 / 400 : ℝ) - (1087 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1086_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1086_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (543 / 400 : ℝ) - (1087 / 3200 : ℝ)) ≤
      (1 / (142914210365283 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (142914210365283 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1087 / 3200 : ℝ) - Real.pi * Real.exp (543 / 400 : ℝ)) ≤
      (2 / (142914210365283 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1087 / 3200 : ℝ) - Real.pi * Real.exp (543 / 400 : ℝ) =
      -(Real.pi * Real.exp (543 / 400 : ℝ) - (1087 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12224962845902079 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (12224962845902079 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1086_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (543 / 800 : ℝ) (1087 / 1600 : ℝ)) :
    (18016321 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (36793419 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1086_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1086_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1087_leftExp :
    (38913261027 / 10000000000 : ℝ) ≤ Real.exp (1087 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1087 / 800 : ℝ) (104337529873 / 100000000000 : ℝ)
    (38913261027 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1087_rightExp :
    Real.exp (34 / 25 : ℝ) ≤ (38961933019 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34 / 25 : ℝ) (521708028187 / 500000000000 : ℝ)
    (38961933019 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1087_denomUpper :
    Real.exp (119005661038959267 / 10000000000000000 : ℝ) ≤ (1473500170557101 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (119005661038959267 / 10000000000000000 : ℝ)
    (181309665413 / 125000000000 : ℝ) (1473500170557101 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1087_denomLower :
    (725340780923811 / 5000000000 : ℝ) ≤ Real.exp (14856198692041873 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14856198692041873 / 1250000000000000 : ℝ) (181221257999
    / 125000000000 : ℝ) (725340780923811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1087_product_lower :
    (15281198692041873 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1087 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1087_leftExp
    (by norm_num : (0 : ℝ) ≤ (38913261027 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1087_product_upper :
    Real.pi * Real.exp (34 / 25 : ℝ) ≤ (122402536038959267 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1087_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1087_endpointLower :
    (35592037 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1087 / 1600 : ℝ) (17 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15281198692041873 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1087 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1087_product_lower
  have hD : Real.exp (Real.pi * Real.exp (34 / 25 : ℝ) - (1087 / 3200 : ℝ)) ≤
      (1473500170557101 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1087_denomUpper
    linarith [hpThetaJensenCell1087_product_upper]
  have hi : (1 / (1473500170557101 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (34 / 25 : ℝ) - (1087 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1473500170557101 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1473500170557101 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1087 / 3200 : ℝ) - Real.pi * Real.exp (34 / 25 : ℝ)) := by
    rw [show (1087 / 3200 : ℝ) - Real.pi * Real.exp (34 / 25 : ℝ) =
      -(Real.pi * Real.exp (34 / 25 : ℝ) - (1087 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1087 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1087 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1087_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1473500170557101 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1087_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1087 / 1600 : ℝ) (17 / 25 : ℝ) ≤ (36344197 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (34 / 25 : ℝ)) (122402536038959267 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1087_product_upper
  have hD : (725340780923811 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1087 / 800 : ℝ) - (17 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell1087_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1087_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1087 / 800 : ℝ) - (17 / 50 : ℝ)) ≤
      (1 / (725340780923811 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (725340780923811 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 50 : ℝ) - Real.pi * Real.exp (1087 / 800 : ℝ)) ≤
      (2 / (725340780923811 / 5000000000 : ℝ) : ℝ) := by
    rw [show (17 / 50 : ℝ) - Real.pi * Real.exp (1087 / 800 : ℝ) =
      -(Real.pi * Real.exp (1087 / 800 : ℝ) - (17 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (122402536038959267 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (122402536038959267 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1087_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1087 / 1600 : ℝ) (17 / 25 : ℝ)) :
    (35592037 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (36344197 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1087_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1087_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1088_leftExp :
    (38961933017 / 10000000000 : ℝ) ≤ Real.exp (34 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (34 / 25 : ℝ) (1043416056373 / 1000000000000 : ℝ)
    (38961933017 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1088_rightExp :
    Real.exp (1089 / 800 : ℝ) ≤ (39010665887 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1089 / 800 : ℝ) (104345681561 / 100000000000 : ℝ)
    (39010665887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1088_denomUpper :
    Real.exp (119155634875937991 / 10000000000000000 : ℝ) ≤ (1495765360447471 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (119155634875937991 / 10000000000000000 : ℝ)
    (725578637641 / 500000000000 : ℝ) (1495765360447471 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1088_denomLower :
    (736286891140641 / 5000000000 : ℝ) ≤ Real.exp (14874921508842883 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14874921508842883 / 1250000000000000 : ℝ) (290089763463
    / 200000000000 : ℝ) (736286891140641 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1088_product_lower :
    (15300312133842883 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (34 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1088_leftExp
    (by norm_num : (0 : ℝ) ≤ (38961933017 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1088_product_upper :
    Real.pi * Real.exp (1089 / 800 : ℝ) ≤ (122555634875937991 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1088_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1088_endpointLower :
    (35156139 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 25 : ℝ) (1089 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15300312133842883 / 1250000000000000 : ℝ) (Real.pi * Real.exp (34 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1088_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1089 / 800 : ℝ) - (17 / 50 : ℝ)) ≤
      (1495765360447471 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1088_denomUpper
    linarith [hpThetaJensenCell1088_product_upper]
  have hi : (1 / (1495765360447471 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1089 / 800 : ℝ) - (17 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1495765360447471 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1495765360447471 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 50 : ℝ) - Real.pi * Real.exp (1089 / 800 : ℝ)) := by
    rw [show (17 / 50 : ℝ) - Real.pi * Real.exp (1089 / 800 : ℝ) =
      -(Real.pi * Real.exp (1089 / 800 : ℝ) - (17 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (34 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (34 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1088_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1495765360447471 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1088_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 25 : ℝ) (1089 / 1600 : ℝ) ≤ (7179953 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1089 / 800 : ℝ)) (122555634875937991 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1089 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1088_product_upper
  have hD : (736286891140641 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (34 / 25 : ℝ) - (1089 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1088_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1088_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (34 / 25 : ℝ) - (1089 / 3200 : ℝ)) ≤
      (1 / (736286891140641 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (736286891140641 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1089 / 3200 : ℝ) - Real.pi * Real.exp (34 / 25 : ℝ)) ≤
      (2 / (736286891140641 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1089 / 3200 : ℝ) - Real.pi * Real.exp (34 / 25 : ℝ) =
      -(Real.pi * Real.exp (34 / 25 : ℝ) - (1089 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (122555634875937991 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (122555634875937991 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1088_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 25 : ℝ) (1089 / 1600 : ℝ)) :
    (35156139 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7179953 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1088_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1088_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1089_leftExp :
    (7802133177 / 2000000000 : ℝ) ≤ Real.exp (1089 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1089 / 800 : ℝ) (1043456815609 / 1000000000000 : ℝ)
    (7802133177 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1089_rightExp :
    Real.exp (109 / 80 : ℝ) ≤ (39059459709 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109 / 80 : ℝ) (521748788219 / 500000000000 : ℝ)
    (39059459709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1089_denomUpper :
    Real.exp (119305800205576437 / 10000000000000000 : ℝ) ≤ (303679212472847 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (119305800205576437 / 10000000000000000 : ℝ)
    (181479801851 / 125000000000 : ℝ) (303679212472847 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1089_denomLower :
    (747412483390307 / 5000000000 : ℝ) ≤ Real.exp (2978733646474723 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2978733646474723 / 250000000000000 : ℝ) (1451128755709 /
    1000000000000 : ℝ) (747412483390307 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1089_product_lower :
    (3063889896474723 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1089 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1089_leftExp
    (by norm_num : (0 : ℝ) ≤ (7802133177 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1089_product_upper :
    Real.pi * Real.exp (109 / 80 : ℝ) ≤ (122708925205576437 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1089_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1089_endpointLower :
    (17362453 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1089 / 1600 : ℝ) (109 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3063889896474723 / 250000000000000 : ℝ) (Real.pi * Real.exp (1089 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1089_product_lower
  have hD : Real.exp (Real.pi * Real.exp (109 / 80 : ℝ) - (1089 / 3200 : ℝ)) ≤
      (303679212472847 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1089_denomUpper
    linarith [hpThetaJensenCell1089_product_upper]
  have hi : (1 / (303679212472847 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (109 / 80 : ℝ) - (1089 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (303679212472847 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (303679212472847 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1089 / 3200 : ℝ) - Real.pi * Real.exp (109 / 80 : ℝ)) := by
    rw [show (1089 / 3200 : ℝ) - Real.pi * Real.exp (109 / 80 : ℝ) =
      -(Real.pi * Real.exp (109 / 80 : ℝ) - (1089 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1089 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1089 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1089_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (303679212472847 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1089_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1089 / 1600 : ℝ) (109 / 160 : ℝ) ≤ (70920161 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (109 / 80 : ℝ)) (122708925205576437 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (109 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1089_product_upper
  have hD : (747412483390307 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1089 / 800 : ℝ) - (109 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1089_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1089_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1089 / 800 : ℝ) - (109 / 320 : ℝ)) ≤
      (1 / (747412483390307 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (747412483390307 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((109 / 320 : ℝ) - Real.pi * Real.exp (1089 / 800 : ℝ)) ≤
      (2 / (747412483390307 / 5000000000 : ℝ) : ℝ) := by
    rw [show (109 / 320 : ℝ) - Real.pi * Real.exp (1089 / 800 : ℝ) =
      -(Real.pi * Real.exp (1089 / 800 : ℝ) - (109 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (122708925205576437 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (122708925205576437 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1089_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1089 / 1600 : ℝ) (109 / 160 : ℝ)) :
    (17362453 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (70920161 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1089_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1089_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1090_leftExp :
    (39059459707 / 10000000000 : ℝ) ≤ Real.exp (109 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (109 / 80 : ℝ) (1043497576437 / 1000000000000 : ℝ)
    (39059459707 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1090_rightExp :
    Real.exp (1091 / 800 : ℝ) ≤ (19554157281 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1091 / 800 : ℝ) (521769169429 / 500000000000 : ℝ)
    (19554157281 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1090_denomUpper :
    Real.exp (59728078634888633 / 5000000000000000 : ℝ) ≤ (1541398717029263 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (59728078634888633 / 5000000000000000 : ℝ) (1452520744353
    / 1000000000000 : ℝ) (1541398717029263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1090_denomLower :
    (758720716653529 / 5000000000 : ℝ) ≤ Real.exp (14912438892479193 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14912438892479193 / 1250000000000000 : ℝ) (362952470407
    / 250000000000 : ℝ) (758720716653529 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1090_product_lower :
    (15338610767479193 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (109 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1090_leftExp
    (by norm_num : (0 : ℝ) ≤ (39059459707 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1090_product_upper :
    Real.pi * Real.exp (1091 / 800 : ℝ) ≤ (61431203634888633 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1090_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1090_endpointLower :
    (4287287 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (109 / 160 : ℝ) (1091 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15338610767479193 / 1250000000000000 : ℝ) (Real.pi * Real.exp (109 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1090_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1091 / 800 : ℝ) - (109 / 320 : ℝ)) ≤
      (1541398717029263 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1090_denomUpper
    linarith [hpThetaJensenCell1090_product_upper]
  have hi : (1 / (1541398717029263 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1091 / 800 : ℝ) - (109 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1541398717029263 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1541398717029263 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((109 / 320 : ℝ) - Real.pi * Real.exp (1091 / 800 : ℝ)) := by
    rw [show (109 / 320 : ℝ) - Real.pi * Real.exp (1091 / 800 : ℝ) =
      -(Real.pi * Real.exp (1091 / 800 : ℝ) - (109 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (109 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (109 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1090_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1541398717029263 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1090_endpointUpper :
    hpThetaJensenKernelEndpointUpper (109 / 160 : ℝ) (1091 / 1600 : ℝ) ≤ (17512551 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1091 / 800 : ℝ)) (61431203634888633 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1091 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1090_product_upper
  have hD : (758720716653529 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (109 / 80 : ℝ) - (1091 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1090_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1090_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (109 / 80 : ℝ) - (1091 / 3200 : ℝ)) ≤
      (1 / (758720716653529 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (758720716653529 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1091 / 3200 : ℝ) - Real.pi * Real.exp (109 / 80 : ℝ)) ≤
      (2 / (758720716653529 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1091 / 3200 : ℝ) - Real.pi * Real.exp (109 / 80 : ℝ) =
      -(Real.pi * Real.exp (109 / 80 : ℝ) - (1091 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61431203634888633 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (61431203634888633 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1090_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (109 / 160 : ℝ) (1091 / 1600 : ℝ)) :
    (4287287 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17512551 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1090_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1090_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1091_leftExp :
    (39108314559 / 10000000000 : ℝ) ≤ Real.exp (1091 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1091 / 800 : ℝ) (1043538338857 / 1000000000000 : ℝ)
    (39108314559 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1091_rightExp :
    Real.exp (273 / 200 : ℝ) ≤ (39157230521 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (273 / 200 : ℝ) (1043579102871 / 1000000000000 : ℝ)
    (39157230521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1091_denomUpper :
    Real.exp (119606706304159953 / 10000000000000000 : ℝ) ≤ (782389942435821 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (119606706304159953 / 10000000000000000 : ℝ)
    (1453204266363 / 1000000000000 : ℝ) (782389942435821 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1091_denomLower :
    (770214808976653 / 5000000000 : ℝ) ≤ Real.exp (14931233519004741 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14931233519004741 / 1250000000000000 : ℝ) (726246098763
    / 500000000000 : ℝ) (770214808976653 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1091_product_lower :
    (15357796019004741 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1091 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1091_leftExp
    (by norm_num : (0 : ℝ) ≤ (39108314559 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1091_product_upper :
    Real.pi * Real.exp (273 / 200 : ℝ) ≤ (123016081304159953 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1091_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1091_endpointLower :
    (67752537 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1091 / 1600 : ℝ) (273 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15357796019004741 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1091 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1091_product_lower
  have hD : Real.exp (Real.pi * Real.exp (273 / 200 : ℝ) - (1091 / 3200 : ℝ)) ≤
      (782389942435821 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1091_denomUpper
    linarith [hpThetaJensenCell1091_product_upper]
  have hi : (1 / (782389942435821 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (273 / 200 : ℝ) - (1091 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (782389942435821 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (782389942435821 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1091 / 3200 : ℝ) - Real.pi * Real.exp (273 / 200 : ℝ)) := by
    rw [show (1091 / 3200 : ℝ) - Real.pi * Real.exp (273 / 200 : ℝ) =
      -(Real.pi * Real.exp (273 / 200 : ℝ) - (1091 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1091 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1091 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1091_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (782389942435821 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1091_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1091 / 1600 : ℝ) (273 / 400 : ℝ) ≤ (34594787 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (273 / 200 : ℝ)) (123016081304159953 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (273 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1091_product_upper
  have hD : (770214808976653 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1091 / 800 : ℝ) - (273 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1091_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1091_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1091 / 800 : ℝ) - (273 / 800 : ℝ)) ≤
      (1 / (770214808976653 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (770214808976653 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((273 / 800 : ℝ) - Real.pi * Real.exp (1091 / 800 : ℝ)) ≤
      (2 / (770214808976653 / 5000000000 : ℝ) : ℝ) := by
    rw [show (273 / 800 : ℝ) - Real.pi * Real.exp (1091 / 800 : ℝ) =
      -(Real.pi * Real.exp (1091 / 800 : ℝ) - (273 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (123016081304159953 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (123016081304159953 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1091_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1091 / 1600 : ℝ) (273 / 400 : ℝ)) :
    (67752537 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (34594787 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1091_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1091_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1092_leftExp :
    (39157230519 / 10000000000 : ℝ) ≤ Real.exp (273 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (273 / 200 : ℝ) (104357910287 / 100000000000 : ℝ)
    (39157230519 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1092_rightExp :
    Real.exp (1093 / 800 : ℝ) ≤ (2450387979 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1093 / 800 : ℝ) (260904967119 / 250000000000 : ℝ)
    (2450387979 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1092_denomUpper :
    Real.exp (7484840472110547 / 625000000000000 : ℝ) ≤ (1588546250930187 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7484840472110547 / 625000000000000 : ℝ) (1453888983333 /
    1000000000000 : ℝ) (1588546250930187 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1092_denomLower :
    (31275921571591 / 200000000 : ℝ) ≤ Real.exp (14950052142580781 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14950052142580781 / 1250000000000000 : ℝ) (290635141179
    / 200000000000 : ℝ) (31275921571591 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1092_product_lower :
    (15377005267580781 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (273 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1092_leftExp
    (by norm_num : (0 : ℝ) ≤ (39157230519 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1092_product_upper :
    Real.pi * Real.exp (1093 / 800 : ℝ) ≤ (7698121722110547 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1092_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1092_endpointLower :
    (13383513 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (273 / 400 : ℝ) (1093 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15377005267580781 / 1250000000000000 : ℝ) (Real.pi * Real.exp (273 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1092_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1093 / 800 : ℝ) - (273 / 800 : ℝ)) ≤
      (1588546250930187 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1092_denomUpper
    linarith [hpThetaJensenCell1092_product_upper]
  have hi : (1 / (1588546250930187 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1093 / 800 : ℝ) - (273 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1588546250930187 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1588546250930187 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((273 / 800 : ℝ) - Real.pi * Real.exp (1093 / 800 : ℝ)) := by
    rw [show (273 / 800 : ℝ) - Real.pi * Real.exp (1093 / 800 : ℝ) =
      -(Real.pi * Real.exp (1093 / 800 : ℝ) - (273 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (273 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (273 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1092_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1588546250930187 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1092_endpointUpper :
    hpThetaJensenKernelEndpointUpper (273 / 400 : ℝ) (1093 / 1600 : ℝ) ≤ (6833819 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1093 / 800 : ℝ)) (7698121722110547 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1093 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1092_product_upper
  have hD : (31275921571591 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (273 / 200 : ℝ) - (1093 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1092_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1092_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (273 / 200 : ℝ) - (1093 / 3200 : ℝ)) ≤
      (1 / (31275921571591 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31275921571591 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1093 / 3200 : ℝ) - Real.pi * Real.exp (273 / 200 : ℝ)) ≤
      (2 / (31275921571591 / 200000000 : ℝ) : ℝ) := by
    rw [show (1093 / 3200 : ℝ) - Real.pi * Real.exp (273 / 200 : ℝ) =
      -(Real.pi * Real.exp (273 / 200 : ℝ) - (1093 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7698121722110547 / 625000000000000 : ℝ) ^ 2 - 6 *
      (7698121722110547 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1092_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (273 / 400 : ℝ) (1093 / 1600 : ℝ)) :
    (13383513 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6833819 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1092_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1092_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1093_leftExp :
    (19603103831 / 5000000000 : ℝ) ≤ Real.exp (1093 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1093 / 800 : ℝ) (41744794739 / 40000000000 : ℝ)
    (19603103831 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1093_rightExp :
    Real.exp (547 / 400 : ℝ) ≤ (19627623033 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (547 / 400 : ℝ) (1043660635673 / 1000000000000 : ℝ)
    (19627623033 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1093_denomUpper :
    Real.exp (59954190627111569 / 5000000000000000 : ℝ) ≤ (322540924870821 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59954190627111569 / 5000000000000000 : ℝ) (1454574897721
    / 1000000000000 : ℝ) (322540924870821 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1093_denomLower :
    (317509498904993 / 2000000000 : ℝ) ≤ Real.exp (7484447396329869 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7484447396329869 / 625000000000000 : ℝ) (726930204593 /
    500000000000 : ℝ) (317509498904993 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1093_product_lower :
    (7698119271329869 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1093 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1093_leftExp
    (by norm_num : (0 : ℝ) ≤ (19603103831 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1093_product_upper :
    Real.pi * Real.exp (547 / 400 : ℝ) ≤ (61662003127111569 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1093_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1093_endpointLower :
    (13218319 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1093 / 1600 : ℝ) (547 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7698119271329869 / 625000000000000 : ℝ) (Real.pi * Real.exp (1093 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1093_product_lower
  have hD : Real.exp (Real.pi * Real.exp (547 / 400 : ℝ) - (1093 / 3200 : ℝ)) ≤
      (322540924870821 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1093_denomUpper
    linarith [hpThetaJensenCell1093_product_upper]
  have hi : (1 / (322540924870821 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (547 / 400 : ℝ) - (1093 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (322540924870821 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (322540924870821 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1093 / 3200 : ℝ) - Real.pi * Real.exp (547 / 400 : ℝ)) := by
    rw [show (1093 / 3200 : ℝ) - Real.pi * Real.exp (547 / 400 : ℝ) =
      -(Real.pi * Real.exp (547 / 400 : ℝ) - (1093 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1093 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1093 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1093_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (322540924870821 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1093_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1093 / 1600 : ℝ) (547 / 800 : ℝ) ≤ (67495967 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (547 / 400 : ℝ)) (61662003127111569 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (547 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1093_product_upper
  have hD : (317509498904993 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1093 / 800 : ℝ) - (547 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1093_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1093_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1093 / 800 : ℝ) - (547 / 1600 : ℝ)) ≤
      (1 / (317509498904993 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (317509498904993 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((547 / 1600 : ℝ) - Real.pi * Real.exp (1093 / 800 : ℝ)) ≤
      (2 / (317509498904993 / 2000000000 : ℝ) : ℝ) := by
    rw [show (547 / 1600 : ℝ) - Real.pi * Real.exp (1093 / 800 : ℝ) =
      -(Real.pi * Real.exp (1093 / 800 : ℝ) - (547 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61662003127111569 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (61662003127111569 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1093_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1093 / 1600 : ℝ) (547 / 800 : ℝ)) :
    (13218319 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (67495967 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1093_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1093_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1094_leftExp :
    (2453452879 / 625000000 : ℝ) ≤ Real.exp (547 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (547 / 400 : ℝ) (130457579459 / 125000000000 : ℝ)
    (2453452879 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1094_rightExp :
    Real.exp (219 / 160 : ℝ) ≤ (7860869161 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (219 / 160 : ℝ) (1043701404463 / 1000000000000 : ℝ)
    (7860869161 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1094_denomUpper :
    Real.exp (24011901530113473 / 2000000000000000 : ℝ) ≤ (1637261943738193 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (24011901530113473 / 2000000000000000 : ℝ) (145526201203
    / 100000000000 : ℝ) (1637261943738193 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1094_denomLower :
    (1611690671092943 / 10000000000 : ℝ) ≤ Real.exp (936735093692921 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (936735093692921 / 78125000000000 : ℝ) (145454630987 /
    100000000000 : ℝ) (1611690671092943 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1094_product_lower :
    (963468492130421 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (547 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1094_leftExp
    (by norm_num : (0 : ℝ) ≤ (2453452879 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1094_product_upper :
    Real.pi * Real.exp (219 / 160 : ℝ) ≤ (24695651530113473 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1094_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1094_endpointLower :
    (32637273 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (547 / 800 : ℝ) (219 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (963468492130421 / 78125000000000 : ℝ) (Real.pi * Real.exp (547 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1094_product_lower
  have hD : Real.exp (Real.pi * Real.exp (219 / 160 : ℝ) - (547 / 1600 : ℝ)) ≤
      (1637261943738193 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1094_denomUpper
    linarith [hpThetaJensenCell1094_product_upper]
  have hi : (1 / (1637261943738193 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (219 / 160 : ℝ) - (547 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1637261943738193 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1637261943738193 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((547 / 1600 : ℝ) - Real.pi * Real.exp (219 / 160 : ℝ)) := by
    rw [show (547 / 1600 : ℝ) - Real.pi * Real.exp (219 / 160 : ℝ) =
      -(Real.pi * Real.exp (219 / 160 : ℝ) - (547 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (547 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (547 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1094_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1637261943738193 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1094_endpointUpper :
    hpThetaJensenKernelEndpointUpper (547 / 800 : ℝ) (219 / 320 : ℝ) ≤ (2666513 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (219 / 160 : ℝ)) (24695651530113473 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (219 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1094_product_upper
  have hD : (1611690671092943 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (547 / 400 : ℝ) - (219 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1094_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1094_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (547 / 400 : ℝ) - (219 / 640 : ℝ)) ≤
      (1 / (1611690671092943 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1611690671092943 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((219 / 640 : ℝ) - Real.pi * Real.exp (547 / 400 : ℝ)) ≤
      (2 / (1611690671092943 / 10000000000 : ℝ) : ℝ) := by
    rw [show (219 / 640 : ℝ) - Real.pi * Real.exp (547 / 400 : ℝ) =
      -(Real.pi * Real.exp (547 / 400 : ℝ) - (219 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24695651530113473 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (24695651530113473 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1094_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (547 / 800 : ℝ) (219 / 320 : ℝ)) :
    (32637273 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2666513 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1094_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1094_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1095_leftExp :
    (19652172901 / 5000000000 : ℝ) ≤ Real.exp (219 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (219 / 160 : ℝ) (521850702231 / 500000000000 : ℝ)
    (19652172901 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1095_rightExp :
    Real.exp (137 / 100 : ℝ) ≤ (9838376739 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (137 / 100 : ℝ) (208748434969 / 200000000000 : ℝ)
    (9838376739 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1095_denomUpper :
    Real.exp (30052706744605227 / 2500000000000000 : ℝ) ≤ (332445055369569 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (30052706744605227 / 2500000000000000 : ℝ) (181993791091
    / 125000000000 : ℝ) (332445055369569 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1095_denomLower :
    (409058135510523 / 2500000000 : ℝ) ≤ Real.exp (7503326146049799 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7503326146049799 / 625000000000000 : ℝ) (1455233410437 /
    1000000000000 : ℝ) (409058135510523 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1095_product_lower :
    (7717388646049799 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (219 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1095_leftExp
    (by norm_num : (0 : ℝ) ≤ (19652172901 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1095_product_upper :
    Real.pi * Real.exp (137 / 100 : ℝ) ≤ (30908175494605227 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1095_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1095_endpointLower :
    (32233169 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (219 / 320 : ℝ) (137 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7717388646049799 / 625000000000000 : ℝ) (Real.pi * Real.exp (219 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1095_product_lower
  have hD : Real.exp (Real.pi * Real.exp (137 / 100 : ℝ) - (219 / 640 : ℝ)) ≤
      (332445055369569 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1095_denomUpper
    linarith [hpThetaJensenCell1095_product_upper]
  have hi : (1 / (332445055369569 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (137 / 100 : ℝ) - (219 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (332445055369569 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (332445055369569 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((219 / 640 : ℝ) - Real.pi * Real.exp (137 / 100 : ℝ)) := by
    rw [show (219 / 640 : ℝ) - Real.pi * Real.exp (137 / 100 : ℝ) =
      -(Real.pi * Real.exp (137 / 100 : ℝ) - (219 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (219 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (219 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1095_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (332445055369569 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1095_endpointUpper :
    hpThetaJensenKernelEndpointUpper (219 / 320 : ℝ) (137 / 200 : ℝ) ≤ (32919341 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (137 / 100 : ℝ)) (30908175494605227 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (137 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1095_product_upper
  have hD : (409058135510523 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (219 / 160 : ℝ) - (137 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1095_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1095_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (219 / 160 : ℝ) - (137 / 400 : ℝ)) ≤
      (1 / (409058135510523 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (409058135510523 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((137 / 400 : ℝ) - Real.pi * Real.exp (219 / 160 : ℝ)) ≤
      (2 / (409058135510523 / 2500000000 : ℝ) : ℝ) := by
    rw [show (137 / 400 : ℝ) - Real.pi * Real.exp (219 / 160 : ℝ) =
      -(Real.pi * Real.exp (219 / 160 : ℝ) - (137 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30908175494605227 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (30908175494605227 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1095_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (219 / 320 : ℝ) (137 / 200 : ℝ)) :
    (32233169 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32919341 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1095_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1095_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1096_leftExp :
    (39353506953 / 10000000000 : ℝ) ≤ Real.exp (137 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (137 / 100 : ℝ) (260935543711 / 250000000000 : ℝ)
    (39353506953 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1096_rightExp :
    Real.exp (1097 / 800 : ℝ) ≤ (39402729597 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1097 / 800 : ℝ) (52189147341 / 50000000000 : ℝ)
    (39402729597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1096_denomUpper :
    Real.exp (120362339482828021 / 10000000000000000 : ℝ) ≤ (26368778532417 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (120362339482828021 / 10000000000000000 : ℝ)
    (182079981291 / 125000000000 : ℝ) (26368778532417 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1096_denomLower :
    (83059008584481 / 500000000 : ℝ) ≤ Real.exp (15025567201936147 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15025567201936147 / 1250000000000000 : ℝ) (1455921713383
    / 1000000000000 : ℝ) (83059008584481 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1096_product_lower :
    (15454082826936147 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (137 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1096_leftExp
    (by norm_num : (0 : ℝ) ≤ (39353506953 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1096_product_upper :
    Real.pi * Real.exp (1097 / 800 : ℝ) ≤ (123787339482828021 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1096_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1096_endpointLower :
    (63666891 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (137 / 200 : ℝ) (1097 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15454082826936147 / 1250000000000000 : ℝ) (Real.pi * Real.exp (137 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1096_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1097 / 800 : ℝ) - (137 / 400 : ℝ)) ≤
      (26368778532417 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1096_denomUpper
    linarith [hpThetaJensenCell1096_product_upper]
  have hi : (1 / (26368778532417 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1097 / 800 : ℝ) - (137 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26368778532417 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26368778532417 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((137 / 400 : ℝ) - Real.pi * Real.exp (1097 / 800 : ℝ)) := by
    rw [show (137 / 400 : ℝ) - Real.pi * Real.exp (1097 / 800 : ℝ) =
      -(Real.pi * Real.exp (1097 / 800 : ℝ) - (137 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (137 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (137 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1096_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26368778532417 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1096_endpointUpper :
    hpThetaJensenKernelEndpointUpper (137 / 200 : ℝ) (1097 / 1600 : ℝ) ≤ (32511729 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1097 / 800 : ℝ)) (123787339482828021 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1097 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1096_product_upper
  have hD : (83059008584481 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (137 / 100 : ℝ) - (1097 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1096_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1096_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (137 / 100 : ℝ) - (1097 / 3200 : ℝ)) ≤
      (1 / (83059008584481 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (83059008584481 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1097 / 3200 : ℝ) - Real.pi * Real.exp (137 / 100 : ℝ)) ≤
      (2 / (83059008584481 / 500000000 : ℝ) : ℝ) := by
    rw [show (1097 / 3200 : ℝ) - Real.pi * Real.exp (137 / 100 : ℝ) =
      -(Real.pi * Real.exp (137 / 100 : ℝ) - (1097 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (123787339482828021 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (123787339482828021 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1096_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (137 / 200 : ℝ) (1097 / 1600 : ℝ)) :
    (63666891 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32511729 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1096_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1096_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1097_leftExp :
    (7880545919 / 2000000000 : ℝ) ≤ Real.exp (1097 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1097 / 800 : ℝ) (1043782946819 / 1000000000000 : ℝ)
    (7880545919 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1097_rightExp :
    Real.exp (549 / 400 : ℝ) ≤ (19726006903 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (549 / 400 : ℝ) (260955930097 / 250000000000 : ℝ)
    (19726006903 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1097_denomUpper :
    Real.exp (60257022704416479 / 5000000000000000 : ℝ) ≤ (856699464882627 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (60257022704416479 / 5000000000000000 : ℝ) (29146611587 /
    20000000000 : ℝ) (856699464882627 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1097_denomLower :
    (1686540757953679 / 10000000000 : ℝ) ≤ Real.exp (3008901251845381 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3008901251845381 / 250000000000000 : ℝ) (728305610611 /
    500000000000 : ℝ) (1686540757953679 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1097_product_lower :
    (3094682501845381 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1097 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1097_leftExp
    (by norm_num : (0 : ℝ) ≤ (7880545919 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1097_product_upper :
    Real.pi * Real.exp (549 / 400 : ℝ) ≤ (61971085204416479 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1097_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1097_endpointLower :
    (62876127 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1097 / 1600 : ℝ) (549 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3094682501845381 / 250000000000000 : ℝ) (Real.pi * Real.exp (1097 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1097_product_lower
  have hD : Real.exp (Real.pi * Real.exp (549 / 400 : ℝ) - (1097 / 3200 : ℝ)) ≤
      (856699464882627 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1097_denomUpper
    linarith [hpThetaJensenCell1097_product_upper]
  have hi : (1 / (856699464882627 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (549 / 400 : ℝ) - (1097 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (856699464882627 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (856699464882627 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1097 / 3200 : ℝ) - Real.pi * Real.exp (549 / 400 : ℝ)) := by
    rw [show (1097 / 3200 : ℝ) - Real.pi * Real.exp (549 / 400 : ℝ) =
      -(Real.pi * Real.exp (549 / 400 : ℝ) - (1097 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1097 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1097 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1097_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (856699464882627 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1097_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1097 / 1600 : ℝ) (549 / 800 : ℝ) ≤ (64217071 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (549 / 400 : ℝ)) (61971085204416479 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (549 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1097_product_upper
  have hD : (1686540757953679 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1097 / 800 : ℝ) - (549 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1097_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1097_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1097 / 800 : ℝ) - (549 / 1600 : ℝ)) ≤
      (1 / (1686540757953679 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1686540757953679 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((549 / 1600 : ℝ) - Real.pi * Real.exp (1097 / 800 : ℝ)) ≤
      (2 / (1686540757953679 / 10000000000 : ℝ) : ℝ) := by
    rw [show (549 / 1600 : ℝ) - Real.pi * Real.exp (1097 / 800 : ℝ) =
      -(Real.pi * Real.exp (1097 / 800 : ℝ) - (549 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61971085204416479 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (61971085204416479 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1097_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1097 / 1600 : ℝ) (549 / 800 : ℝ)) :
    (62876127 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (64217071 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1097_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1097_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1098_leftExp :
    (39452013803 / 10000000000 : ℝ) ≤ Real.exp (549 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (549 / 400 : ℝ) (1043823720387 / 1000000000000 : ℝ)
    (39452013803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1098_rightExp :
    Real.exp (1099 / 800 : ℝ) ≤ (39501359657 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1099 / 800 : ℝ) (260966123887 / 250000000000 : ℝ)
    (39501359657 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1098_denomUpper :
    Real.exp (120665944988913601 / 10000000000000000 : ℝ) ≤ (1739624062643143 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (120665944988913601 / 10000000000000000 : ℝ)
    (1458022518261 / 1000000000000 : ℝ) (1739624062643143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1098_denomLower :
    (214040204111891 / 1250000000 : ℝ) ≤ Real.exp (15063469493424297 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15063469493424297 / 1250000000000000 : ℝ) (1457301936429
    / 1000000000000 : ℝ) (214040204111891 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1098_product_lower :
    (15492766368424297 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (549 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1098_leftExp
    (by norm_num : (0 : ℝ) ≤ (39452013803 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1098_product_upper :
    Real.pi * Real.exp (1099 / 800 : ℝ) ≤ (124097194988913601 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1098_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1098_endpointLower :
    (31046983 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (549 / 800 : ℝ) (1099 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15492766368424297 / 1250000000000000 : ℝ) (Real.pi * Real.exp (549 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1098_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1099 / 800 : ℝ) - (549 / 1600 : ℝ)) ≤
      (1739624062643143 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1098_denomUpper
    linarith [hpThetaJensenCell1098_product_upper]
  have hi : (1 / (1739624062643143 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1099 / 800 : ℝ) - (549 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1739624062643143 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1739624062643143 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((549 / 1600 : ℝ) - Real.pi * Real.exp (1099 / 800 : ℝ)) := by
    rw [show (549 / 1600 : ℝ) - Real.pi * Real.exp (1099 / 800 : ℝ) =
      -(Real.pi * Real.exp (1099 / 800 : ℝ) - (549 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (549 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (549 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1098_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1739624062643143 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1098_endpointUpper :
    hpThetaJensenKernelEndpointUpper (549 / 800 : ℝ) (1099 / 1600 : ℝ) ≤ (31709721 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1099 / 800 : ℝ)) (124097194988913601 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1099 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1098_product_upper
  have hD : (214040204111891 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (549 / 400 : ℝ) - (1099 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1098_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1098_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (549 / 400 : ℝ) - (1099 / 3200 : ℝ)) ≤
      (1 / (214040204111891 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (214040204111891 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1099 / 3200 : ℝ) - Real.pi * Real.exp (549 / 400 : ℝ)) ≤
      (2 / (214040204111891 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1099 / 3200 : ℝ) - Real.pi * Real.exp (549 / 400 : ℝ) =
      -(Real.pi * Real.exp (549 / 400 : ℝ) - (1099 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (124097194988913601 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (124097194988913601 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1098_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (549 / 800 : ℝ) (1099 / 1600 : ℝ)) :
    (31046983 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (31709721 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1098_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1098_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1099_leftExp :
    (7900271931 / 2000000000 : ℝ) ≤ Real.exp (1099 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1099 / 800 : ℝ) (1043864495547 / 1000000000000 : ℝ)
    (7900271931 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1099_rightExp :
    Real.exp (11 / 8 : ℝ) ≤ (39550767231 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 8 : ℝ) (521952636151 / 500000000000 : ℝ)
    (39550767231 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1099_denomUpper :
    Real.exp (120818038477538983 / 10000000000000000 : ℝ) ≤ (88314242226549 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (120818038477538983 / 10000000000000000 : ℝ)
    (1458715669633 / 1000000000000 : ℝ) (88314242226549 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1099_denomLower :
    (1738530268734887 / 10000000000 : ℝ) ≤ Real.exp (3016491387031769 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3016491387031769 / 250000000000000 : ℝ) (145799386153 /
    100000000000 : ℝ) (1738530268734887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1099_product_lower :
    (3102428887031769 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1099 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1099_leftExp
    (by norm_num : (0 : ℝ) ≤ (7900271931 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1099_product_upper :
    Real.pi * Real.exp (11 / 8 : ℝ) ≤ (124252413477538983 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1099_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1099_endpointLower :
    (15330083 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1099 / 1600 : ℝ) (11 / 16 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3102428887031769 / 250000000000000 : ℝ) (Real.pi * Real.exp (1099 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1099_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 8 : ℝ) - (1099 / 3200 : ℝ)) ≤
      (88314242226549 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1099_denomUpper
    linarith [hpThetaJensenCell1099_product_upper]
  have hi : (1 / (88314242226549 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 8 : ℝ) - (1099 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (88314242226549 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (88314242226549 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1099 / 3200 : ℝ) - Real.pi * Real.exp (11 / 8 : ℝ)) := by
    rw [show (1099 / 3200 : ℝ) - Real.pi * Real.exp (11 / 8 : ℝ) =
      -(Real.pi * Real.exp (11 / 8 : ℝ) - (1099 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1099 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1099 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1099_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (88314242226549 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1099_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1099 / 1600 : ℝ) (11 / 16 : ℝ) ≤ (62630493 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 8 : ℝ)) (124252413477538983 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 16 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1099_product_upper
  have hD : (1738530268734887 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1099 / 800 : ℝ) - (11 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell1099_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1099_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1099 / 800 : ℝ) - (11 / 32 : ℝ)) ≤
      (1 / (1738530268734887 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1738530268734887 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 32 : ℝ) - Real.pi * Real.exp (1099 / 800 : ℝ)) ≤
      (2 / (1738530268734887 / 10000000000 : ℝ) : ℝ) := by
    rw [show (11 / 32 : ℝ) - Real.pi * Real.exp (1099 / 800 : ℝ) =
      -(Real.pi * Real.exp (1099 / 800 : ℝ) - (11 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (124252413477538983 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (124252413477538983 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1099_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1099 / 1600 : ℝ) (11 / 16 : ℝ)) :
    (15330083 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (62630493 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1099_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1099_endpointUpper

def hpThetaJensenCellsBatch054Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1551099 / 200000000 : ℝ)
  | 1 => (38307741 / 5000000000 : ℝ)
  | 2 => (37842969 / 5000000000 : ℝ)
  | 3 => (9345779 / 1250000000 : ℝ)
  | 4 => (36928139 / 5000000000 : ℝ)
  | 5 => (7295599 / 1000000000 : ℝ)
  | 6 => (18016321 / 2500000000 : ℝ)
  | 7 => (35592037 / 5000000000 : ℝ)
  | 8 => (35156139 / 5000000000 : ℝ)
  | 9 => (17362453 / 2500000000 : ℝ)
  | 10 => (4287287 / 625000000 : ℝ)
  | 11 => (67752537 / 10000000000 : ℝ)
  | 12 => (13383513 / 2000000000 : ℝ)
  | 13 => (13218319 / 2000000000 : ℝ)
  | 14 => (32637273 / 5000000000 : ℝ)
  | 15 => (32233169 / 5000000000 : ℝ)
  | 16 => (63666891 / 10000000000 : ℝ)
  | 17 => (62876127 / 10000000000 : ℝ)
  | 18 => (31046983 / 5000000000 : ℝ)
  | 19 => (15330083 / 2500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch054Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (19795873 / 2500000000 : ℝ)
  | 1 => (488911 / 62500000 : ℝ)
  | 2 => (77278127 / 10000000000 : ℝ)
  | 3 => (15268101 / 2000000000 : ℝ)
  | 4 => (9426601 / 1250000000 : ℝ)
  | 5 => (18623737 / 2500000000 : ℝ)
  | 6 => (36793419 / 5000000000 : ℝ)
  | 7 => (36344197 / 5000000000 : ℝ)
  | 8 => (7179953 / 1000000000 : ℝ)
  | 9 => (70920161 / 10000000000 : ℝ)
  | 10 => (17512551 / 2500000000 : ℝ)
  | 11 => (34594787 / 5000000000 : ℝ)
  | 12 => (6833819 / 1000000000 : ℝ)
  | 13 => (67495967 / 10000000000 : ℝ)
  | 14 => (2666513 / 400000000 : ℝ)
  | 15 => (32919341 / 5000000000 : ℝ)
  | 16 => (32511729 / 5000000000 : ℝ)
  | 17 => (64217071 / 10000000000 : ℝ)
  | 18 => (31709721 / 5000000000 : ℝ)
  | 19 => (62630493 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch054_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch054Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch054Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1080_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1081_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1082_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1083_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1084_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1085_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1086_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1087_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1088_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1089_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1090_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1091_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1092_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1093_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1094_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1095_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1096_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1097_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1098_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1099_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper] at h ⊢
    exact h

end HodgeProofHP
