import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell340_leftExp :
    (3823976049 / 2500000000 : ℝ) ≤ Real.exp (17 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 40 : ℝ) (20267396751 / 20000000000 : ℝ) (3823976049
    / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell340_rightExp :
    Real.exp (341 / 800 : ℝ) ≤ (15315036033 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (341 / 800 : ℝ) (253352355771 / 250000000000 : ℝ)
    (15315036033 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell340_denomUpper :
    Real.exp (47051109996020569 / 10000000000000000 : ℝ) ≤ (552552754481 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47051109996020569 / 10000000000000000 : ℝ) (289598545079
    / 250000000000 : ℝ) (552552754481 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell340_denomLower :
    (549069176383 / 5000000000 : ℝ) ≤ Real.exp (1468370789216251 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1468370789216251 / 312500000000000 : ℝ) (1853064413 /
    1600000000 : ℝ) (549069176383 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell340_product_lower :
    (1501671570466251 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell340_leftExp
    (by norm_num : (0 : ℝ) ≤ (3823976049 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell340_product_upper :
    Real.pi * Real.exp (341 / 800 : ℝ) ≤ (48113609996020569 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell340_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell340_endpointLower :
    (718635261 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 80 : ℝ) (341 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1501671570466251 / 312500000000000 : ℝ) (Real.pi * Real.exp (17 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell340_product_lower
  have hD : Real.exp (Real.pi * Real.exp (341 / 800 : ℝ) - (17 / 160 : ℝ)) ≤
      (552552754481 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell340_denomUpper
    linarith [hpThetaJensenCell340_product_upper]
  have hi : (1 / (552552754481 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (341 / 800 : ℝ) - (17 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (552552754481 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (552552754481 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 160 : ℝ) - Real.pi * Real.exp (341 / 800 : ℝ)) := by
    rw [show (17 / 160 : ℝ) - Real.pi * Real.exp (341 / 800 : ℝ) =
      -(Real.pi * Real.exp (341 / 800 : ℝ) - (17 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 40 : ℝ)) := by
    have h := hpThetaJensenCell340_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (552552754481 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell340_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 80 : ℝ) (341 / 1600 : ℝ) ≤ (2909307539 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (341 / 800 : ℝ)) (48113609996020569 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (341 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell340_product_upper
  have hD : (549069176383 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 40 : ℝ) - (341 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell340_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell340_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 40 : ℝ) - (341 / 3200 : ℝ)) ≤
      (1 / (549069176383 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (549069176383 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((341 / 3200 : ℝ) - Real.pi * Real.exp (17 / 40 : ℝ)) ≤
      (2 / (549069176383 / 5000000000 : ℝ) : ℝ) := by
    rw [show (341 / 3200 : ℝ) - Real.pi * Real.exp (17 / 40 : ℝ) =
      -(Real.pi * Real.exp (17 / 40 : ℝ) - (341 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48113609996020569 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (48113609996020569 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell340_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 80 : ℝ) (341 / 1600 : ℝ)) :
    (718635261 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2909307539 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell340_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell340_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell341_leftExp :
    (15315036031 / 10000000000 : ℝ) ≤ Real.exp (341 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (341 / 800 : ℝ) (1013409423083 / 1000000000000 : ℝ)
    (15315036031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell341_rightExp :
    Real.exp (171 / 400 : ℝ) ≤ (7667095899 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (171 / 400 : ℝ) (1013449010163 / 1000000000000 : ℝ)
    (7667095899 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell341_denomUpper :
    Real.exp (23554082306627107 / 5000000000000000 : ℝ) ≤ (222285733451 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23554082306627107 / 5000000000000000 : ℝ) (579300367703
    / 500000000000 : ℝ) (222285733451 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell341_denomLower :
    (552206670841 / 5000000000 : ℝ) ≤ Real.exp (5880605584337669 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5880605584337669 / 1250000000000000 : ℝ) (289592875047 /
    250000000000 : ℝ) (552206670841 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell341_product_lower :
    (6014199334337669 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (341 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell341_leftExp
    (by norm_num : (0 : ℝ) ≤ (15315036031 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell341_product_upper :
    Real.pi * Real.exp (171 / 400 : ℝ) ≤ (24086894806627107 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell341_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell341_endpointLower :
    (11467863799 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (341 / 1600 : ℝ) (171 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6014199334337669 / 1250000000000000 : ℝ) (Real.pi * Real.exp (341 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell341_product_lower
  have hD : Real.exp (Real.pi * Real.exp (171 / 400 : ℝ) - (341 / 3200 : ℝ)) ≤
      (222285733451 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell341_denomUpper
    linarith [hpThetaJensenCell341_product_upper]
  have hi : (1 / (222285733451 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (171 / 400 : ℝ) - (341 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (222285733451 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (222285733451 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((341 / 3200 : ℝ) - Real.pi * Real.exp (171 / 400 : ℝ)) := by
    rw [show (341 / 3200 : ℝ) - Real.pi * Real.exp (171 / 400 : ℝ) =
      -(Real.pi * Real.exp (171 / 400 : ℝ) - (341 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (341 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (341 / 800 : ℝ)) := by
    have h := hpThetaJensenCell341_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (222285733451 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell341_endpointUpper :
    hpThetaJensenKernelEndpointUpper (341 / 1600 : ℝ) (171 / 800 : ℝ) ≤ (11606638647 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (171 / 400 : ℝ)) (24086894806627107 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (171 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell341_product_upper
  have hD : (552206670841 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (341 / 800 : ℝ) - (171 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell341_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell341_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (341 / 800 : ℝ) - (171 / 1600 : ℝ)) ≤
      (1 / (552206670841 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (552206670841 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((171 / 1600 : ℝ) - Real.pi * Real.exp (341 / 800 : ℝ)) ≤
      (2 / (552206670841 / 5000000000 : ℝ) : ℝ) := by
    rw [show (171 / 1600 : ℝ) - Real.pi * Real.exp (341 / 800 : ℝ) =
      -(Real.pi * Real.exp (341 / 800 : ℝ) - (171 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24086894806627107 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (24086894806627107 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell341_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (341 / 1600 : ℝ) (171 / 800 : ℝ)) :
    (11467863799 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11606638647 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell341_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell341_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell342_leftExp :
    (3833547949 / 2500000000 : ℝ) ≤ Real.exp (171 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (171 / 400 : ℝ) (506724505081 / 500000000000 : ℝ)
    (3833547949 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell342_rightExp :
    Real.exp (343 / 800 : ℝ) ≤ (7676685761 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (343 / 800 : ℝ) (253372149697 / 250000000000 : ℝ)
    (7676685761 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell342_denomUpper :
    Real.exp (23582647249957273 / 5000000000000000 : ℝ) ≤ (558898209373 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23582647249957273 / 5000000000000000 : ℝ) (579403799949
    / 500000000000 : ℝ) (558898209373 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell342_denomLower :
    (111073253741 / 1000000000 : ℝ) ≤ Real.exp (1471934352274351 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1471934352274351 / 312500000000000 : ℝ) (289644512791 /
    250000000000 : ℝ) (111073253741 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell342_product_lower :
    (1505430446024351 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (171 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell342_leftExp
    (by norm_num : (0 : ℝ) ≤ (3833547949 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell342_product_upper :
    Real.pi * Real.exp (343 / 800 : ℝ) ≤ (24117022249957273 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell342_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell342_endpointLower :
    (11437545419 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (171 / 800 : ℝ) (343 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1505430446024351 / 312500000000000 : ℝ) (Real.pi * Real.exp (171 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell342_product_lower
  have hD : Real.exp (Real.pi * Real.exp (343 / 800 : ℝ) - (171 / 1600 : ℝ)) ≤
      (558898209373 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell342_denomUpper
    linarith [hpThetaJensenCell342_product_upper]
  have hi : (1 / (558898209373 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (343 / 800 : ℝ) - (171 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (558898209373 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (558898209373 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((171 / 1600 : ℝ) - Real.pi * Real.exp (343 / 800 : ℝ)) := by
    rw [show (171 / 1600 : ℝ) - Real.pi * Real.exp (343 / 800 : ℝ) =
      -(Real.pi * Real.exp (343 / 800 : ℝ) - (171 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (171 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (171 / 400 : ℝ)) := by
    have h := hpThetaJensenCell342_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (558898209373 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell342_endpointUpper :
    hpThetaJensenKernelEndpointUpper (171 / 800 : ℝ) (343 / 1600 : ℝ) ≤ (11576028651 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (343 / 800 : ℝ)) (24117022249957273 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (343 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell342_product_upper
  have hD : (111073253741 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (171 / 400 : ℝ) - (343 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell342_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell342_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (171 / 400 : ℝ) - (343 / 3200 : ℝ)) ≤
      (1 / (111073253741 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (111073253741 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((343 / 3200 : ℝ) - Real.pi * Real.exp (171 / 400 : ℝ)) ≤
      (2 / (111073253741 / 1000000000 : ℝ) : ℝ) := by
    rw [show (343 / 3200 : ℝ) - Real.pi * Real.exp (171 / 400 : ℝ) =
      -(Real.pi * Real.exp (171 / 400 : ℝ) - (343 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24117022249957273 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (24117022249957273 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell342_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (171 / 800 : ℝ) (343 / 1600 : ℝ)) :
    (11437545419 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11576028651 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell342_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell342_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell343_leftExp :
    (15353371521 / 10000000000 : ℝ) ≤ Real.exp (343 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (343 / 800 : ℝ) (1013488598787 / 1000000000000 : ℝ)
    (15353371521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell343_rightExp :
    Real.exp (43 / 100 : ℝ) ≤ (3843143809 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 100 : ℝ) (1013528188959 / 1000000000000 : ℝ)
    (3843143809 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell343_denomUpper :
    Real.exp (11805624938347737 / 2500000000000000 : ℝ) ≤ (56210456303 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11805624938347737 / 2500000000000000 : ℝ) (1159014774299
    / 1000000000000 : ℝ) (56210456303 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell343_denomLower :
    (558548149377 / 5000000000 : ℝ) ≤ Real.exp (5894878642925179 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5894878642925179 / 1250000000000000 : ℝ) (289696227887 /
    250000000000 : ℝ) (558548149377 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell343_product_lower :
    (6029253642925179 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (343 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell343_leftExp
    (by norm_num : (0 : ℝ) ≤ (15353371521 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell343_product_upper :
    Real.pi * Real.exp (43 / 100 : ℝ) ≤ (12073593688347737 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell343_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell343_endpointLower :
    (11407209517 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (343 / 1600 : ℝ) (43 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6029253642925179 / 1250000000000000 : ℝ) (Real.pi * Real.exp (343 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell343_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 100 : ℝ) - (343 / 3200 : ℝ)) ≤
      (56210456303 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell343_denomUpper
    linarith [hpThetaJensenCell343_product_upper]
  have hi : (1 / (56210456303 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 100 : ℝ) - (343 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (56210456303 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (56210456303 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((343 / 3200 : ℝ) - Real.pi * Real.exp (43 / 100 : ℝ)) := by
    rw [show (343 / 3200 : ℝ) - Real.pi * Real.exp (43 / 100 : ℝ) =
      -(Real.pi * Real.exp (43 / 100 : ℝ) - (343 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (343 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (343 / 800 : ℝ)) := by
    have h := hpThetaJensenCell343_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (56210456303 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell343_endpointUpper :
    hpThetaJensenKernelEndpointUpper (343 / 1600 : ℝ) (43 / 200 : ℝ) ≤ (577270033 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 100 : ℝ)) (12073593688347737 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell343_product_upper
  have hD : (558548149377 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (343 / 800 : ℝ) - (43 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell343_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell343_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (343 / 800 : ℝ) - (43 / 400 : ℝ)) ≤
      (1 / (558548149377 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (558548149377 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 400 : ℝ) - Real.pi * Real.exp (343 / 800 : ℝ)) ≤
      (2 / (558548149377 / 5000000000 : ℝ) : ℝ) := by
    rw [show (43 / 400 : ℝ) - Real.pi * Real.exp (343 / 800 : ℝ) =
      -(Real.pi * Real.exp (343 / 800 : ℝ) - (43 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12073593688347737 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (12073593688347737 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell343_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (343 / 1600 : ℝ) (43 / 200 : ℝ)) :
    (11407209517 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (577270033 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell343_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell343_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell344_leftExp :
    (3074515047 / 2000000000 : ℝ) ≤ Real.exp (43 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 100 : ℝ) (506764094479 / 500000000000 : ℝ)
    (3074515047 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell344_rightExp :
    Real.exp (69 / 160 : ℝ) ≤ (1539180297 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 160 : ℝ) (1013567780677 / 1000000000000 : ℝ)
    (1539180297 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell344_denomUpper :
    Real.exp (4727978046793121 / 1000000000000000 : ℝ) ≤ (9045337237 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4727978046793121 / 1000000000000000 : ℝ) (1159222259101
    / 1000000000000 : ℝ) (9045337237 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell344_denomLower :
    (1123504987373 / 10000000000 : ℝ) ≤ Real.exp (1180405859441853 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1180405859441853 / 250000000000000 : ℝ) (1158992081823 /
    1000000000000 : ℝ) (1123504987373 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell344_product_lower :
    (1207358984441853 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell344_leftExp
    (by norm_num : (0 : ℝ) ≤ (3074515047 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell344_product_upper :
    Real.pi * Real.exp (69 / 160 : ℝ) ≤ (4835478046793121 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell344_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell344_endpointLower :
    (5688428289 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 200 : ℝ) (69 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1207358984441853 / 250000000000000 : ℝ) (Real.pi * Real.exp (43 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell344_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 160 : ℝ) - (43 / 400 : ℝ)) ≤
      (9045337237 / 80000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell344_denomUpper
    linarith [hpThetaJensenCell344_product_upper]
  have hi : (1 / (9045337237 / 80000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 160 : ℝ) - (43 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9045337237 / 80000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9045337237 / 80000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 400 : ℝ) - Real.pi * Real.exp (69 / 160 : ℝ)) := by
    rw [show (43 / 400 : ℝ) - Real.pi * Real.exp (69 / 160 : ℝ) =
      -(Real.pi * Real.exp (69 / 160 : ℝ) - (43 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 100 : ℝ)) := by
    have h := hpThetaJensenCell344_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9045337237 / 80000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell344_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 200 : ℝ) (69 / 320 : ℝ) ≤ (359836099 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 160 : ℝ)) (4835478046793121 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell344_product_upper
  have hD : (1123504987373 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 100 : ℝ) - (69 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell344_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell344_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 100 : ℝ) - (69 / 640 : ℝ)) ≤
      (1 / (1123504987373 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1123504987373 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 640 : ℝ) - Real.pi * Real.exp (43 / 100 : ℝ)) ≤
      (2 / (1123504987373 / 10000000000 : ℝ) : ℝ) := by
    rw [show (69 / 640 : ℝ) - Real.pi * Real.exp (43 / 100 : ℝ) =
      -(Real.pi * Real.exp (43 / 100 : ℝ) - (69 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4835478046793121 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4835478046793121 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell344_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 200 : ℝ) (69 / 320 : ℝ)) :
    (5688428289 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (359836099 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell344_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell344_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell345_leftExp :
    (1923975371 / 1250000000 : ℝ) ≤ Real.exp (69 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 160 : ℝ) (253391945169 / 250000000000 : ℝ)
    (1923975371 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell345_rightExp :
    Real.exp (173 / 400 : ℝ) ≤ (7705527377 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (173 / 400 : ℝ) (506803686971 / 500000000000 : ℝ)
    (7705527377 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell345_denomUpper :
    Real.exp (23668568368891561 / 5000000000000000 : ℝ) ≤ (568585436643 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23668568368891561 / 5000000000000000 : ℝ) (2898575137 /
    2500000000 : ℝ) (568585436643 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell345_denomLower :
    (1129958968461 / 10000000000 : ℝ) ≤ Real.exp (738648672966329 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (738648672966329 / 156250000000000 : ℝ) (1159199562481 /
    1000000000000 : ℝ) (1129958968461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell345_product_lower :
    (755543204216329 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell345_leftExp
    (by norm_num : (0 : ℝ) ≤ (1923975371 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell345_product_upper :
    Real.pi * Real.exp (173 / 400 : ℝ) ≤ (24207630868891561 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell345_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell345_endpointLower :
    (709155443 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 320 : ℝ) (173 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (755543204216329 / 156250000000000 : ℝ) (Real.pi * Real.exp (69 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell345_product_lower
  have hD : Real.exp (Real.pi * Real.exp (173 / 400 : ℝ) - (69 / 640 : ℝ)) ≤
      (568585436643 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell345_denomUpper
    linarith [hpThetaJensenCell345_product_upper]
  have hi : (1 / (568585436643 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (173 / 400 : ℝ) - (69 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (568585436643 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (568585436643 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 640 : ℝ) - Real.pi * Real.exp (173 / 400 : ℝ)) := by
    rw [show (69 / 640 : ℝ) - Real.pi * Real.exp (173 / 400 : ℝ) =
      -(Real.pi * Real.exp (173 / 400 : ℝ) - (69 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 160 : ℝ)) := by
    have h := hpThetaJensenCell345_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (568585436643 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell345_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 320 : ℝ) (173 / 800 : ℝ) ≤ (2296818533 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (173 / 400 : ℝ)) (24207630868891561 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (173 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell345_product_upper
  have hD : (1129958968461 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 160 : ℝ) - (173 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell345_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell345_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 160 : ℝ) - (173 / 1600 : ℝ)) ≤
      (1 / (1129958968461 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1129958968461 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((173 / 1600 : ℝ) - Real.pi * Real.exp (69 / 160 : ℝ)) ≤
      (2 / (1129958968461 / 10000000000 : ℝ) : ℝ) := by
    rw [show (173 / 1600 : ℝ) - Real.pi * Real.exp (69 / 160 : ℝ) =
      -(Real.pi * Real.exp (69 / 160 : ℝ) - (173 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24207630868891561 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (24207630868891561 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell345_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 320 : ℝ) (173 / 800 : ℝ)) :
    (709155443 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2296818533 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell345_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell345_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell346_leftExp :
    (481595461 / 312500000 : ℝ) ≤ Real.exp (173 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (173 / 400 : ℝ) (1013607373941 / 1000000000000 : ℝ)
    (481595461 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell346_rightExp :
    Real.exp (347 / 800 : ℝ) ≤ (15430330617 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (347 / 800 : ℝ) (506823484377 / 500000000000 : ℝ)
    (15430330617 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell346_denomUpper :
    Real.exp (47394568654052881 / 10000000000000000 : ℝ) ≤ (1143720653839 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47394568654052881 / 10000000000000000 : ℝ) (28990954047
    / 25000000000 : ℝ) (1143720653839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell346_denomLower :
    (1136458611379 / 10000000000 : ℝ) ≤ Real.exp (184886216095489 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (184886216095489 / 39062500000000 : ℝ) (579703677021 /
    500000000000 : ℝ) (1136458611379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell346_product_lower :
    (189122055939239 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (173 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell346_leftExp
    (by norm_num : (0 : ℝ) ≤ (481595461 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell346_product_upper :
    Real.pi * Real.exp (347 / 800 : ℝ) ≤ (48475818654052881 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell346_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell346_endpointLower :
    (11316101539 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (173 / 800 : ℝ) (347 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (189122055939239 / 39062500000000 : ℝ) (Real.pi * Real.exp (173 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell346_product_lower
  have hD : Real.exp (Real.pi * Real.exp (347 / 800 : ℝ) - (173 / 1600 : ℝ)) ≤
      (1143720653839 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell346_denomUpper
    linarith [hpThetaJensenCell346_product_upper]
  have hi : (1 / (1143720653839 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (347 / 800 : ℝ) - (173 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1143720653839 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1143720653839 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((173 / 1600 : ℝ) - Real.pi * Real.exp (347 / 800 : ℝ)) := by
    rw [show (173 / 1600 : ℝ) - Real.pi * Real.exp (347 / 800 : ℝ) =
      -(Real.pi * Real.exp (347 / 800 : ℝ) - (173 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (173 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (173 / 400 : ℝ)) := by
    have h := hpThetaJensenCell346_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1143720653839 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell346_endpointUpper :
    hpThetaJensenKernelEndpointUpper (173 / 800 : ℝ) (347 / 1600 : ℝ) ≤ (11453413631 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (347 / 800 : ℝ)) (48475818654052881 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (347 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell346_product_upper
  have hD : (1136458611379 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (173 / 400 : ℝ) - (347 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell346_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell346_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (173 / 400 : ℝ) - (347 / 3200 : ℝ)) ≤
      (1 / (1136458611379 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1136458611379 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((347 / 3200 : ℝ) - Real.pi * Real.exp (173 / 400 : ℝ)) ≤
      (2 / (1136458611379 / 10000000000 : ℝ) : ℝ) := by
    rw [show (347 / 3200 : ℝ) - Real.pi * Real.exp (173 / 400 : ℝ) =
      -(Real.pi * Real.exp (173 / 400 : ℝ) - (347 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48475818654052881 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (48475818654052881 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell346_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (173 / 800 : ℝ) (347 / 1600 : ℝ)) :
    (11316101539 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11453413631 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell346_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell346_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell347_leftExp :
    (1928791327 / 1250000000 : ℝ) ≤ Real.exp (347 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (347 / 800 : ℝ) (1013646968753 / 1000000000000 : ℝ)
    (1928791327 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell347_rightExp :
    Real.exp (87 / 200 : ℝ) ≤ (1544963059 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87 / 200 : ℝ) (126710820639 / 125000000000 : ℝ)
    (1544963059 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell347_denomUpper :
    Real.exp (4745207631412987 / 1000000000000000 : ℝ) ≤ (7189480451 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4745207631412987 / 1000000000000000 : ℝ) (72490411303 /
    62500000000 : ℝ) (7189480451 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell347_denomLower :
    (228600857539 / 2000000000 : ℝ) ≤ Real.exp (740442237821573 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (740442237821573 / 156250000000000 : ℝ) (115961545699 /
    100000000000 : ℝ) (228600857539 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell347_product_lower :
    (757434425321573 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (347 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell347_leftExp
    (by norm_num : (0 : ℝ) ≤ (1928791327 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell347_product_upper :
    Real.pi * Real.exp (87 / 200 : ℝ) ≤ (4853645131412987 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell347_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell347_endpointLower :
    (1128570041 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (347 / 1600 : ℝ) (87 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (757434425321573 / 156250000000000 : ℝ) (Real.pi * Real.exp (347 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell347_product_lower
  have hD : Real.exp (Real.pi * Real.exp (87 / 200 : ℝ) - (347 / 3200 : ℝ)) ≤
      (7189480451 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell347_denomUpper
    linarith [hpThetaJensenCell347_product_upper]
  have hi : (1 / (7189480451 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (87 / 200 : ℝ) - (347 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7189480451 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7189480451 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((347 / 3200 : ℝ) - Real.pi * Real.exp (87 / 200 : ℝ)) := by
    rw [show (347 / 3200 : ℝ) - Real.pi * Real.exp (87 / 200 : ℝ) =
      -(Real.pi * Real.exp (87 / 200 : ℝ) - (347 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (347 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (347 / 800 : ℝ)) := by
    have h := hpThetaJensenCell347_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7189480451 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell347_endpointUpper :
    hpThetaJensenKernelEndpointUpper (347 / 1600 : ℝ) (87 / 400 : ℝ) ≤ (71391991 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (87 / 200 : ℝ)) (4853645131412987 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (87 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell347_product_upper
  have hD : (228600857539 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (347 / 800 : ℝ) - (87 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell347_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell347_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (347 / 800 : ℝ) - (87 / 800 : ℝ)) ≤
      (1 / (228600857539 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (228600857539 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((87 / 800 : ℝ) - Real.pi * Real.exp (347 / 800 : ℝ)) ≤
      (2 / (228600857539 / 2000000000 : ℝ) : ℝ) := by
    rw [show (87 / 800 : ℝ) - Real.pi * Real.exp (347 / 800 : ℝ) =
      -(Real.pi * Real.exp (347 / 800 : ℝ) - (87 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4853645131412987 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4853645131412987 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell347_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (347 / 1600 : ℝ) (87 / 400 : ℝ)) :
    (1128570041 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (71391991 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell347_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell347_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell348_leftExp :
    (15449630589 / 10000000000 : ℝ) ≤ Real.exp (87 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87 / 200 : ℝ) (1013686565111 / 1000000000000 : ℝ)
    (15449630589 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell348_rightExp :
    Real.exp (349 / 800 : ℝ) ≤ (15468954703 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (349 / 800 : ℝ) (126715770377 / 125000000000 : ℝ)
    (15468954703 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell348_denomUpper :
    Real.exp (47509659812261879 / 10000000000000000 : ℝ) ≤ (1156959907207 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47509659812261879 / 10000000000000000 : ℝ)
    (1160055312201 / 1000000000000 : ℝ) (1156959907207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell348_denomLower :
    (1149596372263 / 10000000000 : ℝ) ≤ Real.exp (5930726357669711 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5930726357669711 / 1250000000000000 : ℝ) (1159823871807
    / 1000000000000 : ℝ) (1149596372263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell348_product_lower :
    (6067054482669711 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (87 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell348_leftExp
    (by norm_num : (0 : ℝ) ≤ (15449630589 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell348_product_upper :
    Real.pi * Real.exp (349 / 800 : ℝ) ≤ (48597159812261879 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell348_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell348_endpointLower :
    (1406910523 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 400 : ℝ) (349 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6067054482669711 / 1250000000000000 : ℝ) (Real.pi * Real.exp (87 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell348_product_lower
  have hD : Real.exp (Real.pi * Real.exp (349 / 800 : ℝ) - (87 / 800 : ℝ)) ≤
      (1156959907207 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell348_denomUpper
    linarith [hpThetaJensenCell348_product_upper]
  have hi : (1 / (1156959907207 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (349 / 800 : ℝ) - (87 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1156959907207 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1156959907207 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((87 / 800 : ℝ) - Real.pi * Real.exp (349 / 800 : ℝ)) := by
    rw [show (87 / 800 : ℝ) - Real.pi * Real.exp (349 / 800 : ℝ) =
      -(Real.pi * Real.exp (349 / 800 : ℝ) - (87 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (87 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (87 / 200 : ℝ)) := by
    have h := hpThetaJensenCell348_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1156959907207 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell348_endpointUpper :
    hpThetaJensenKernelEndpointUpper (87 / 400 : ℝ) (349 / 1600 : ℝ) ≤ (5696003973 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (349 / 800 : ℝ)) (48597159812261879 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (349 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell348_product_upper
  have hD : (1149596372263 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (87 / 200 : ℝ) - (349 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell348_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell348_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (87 / 200 : ℝ) - (349 / 3200 : ℝ)) ≤
      (1 / (1149596372263 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1149596372263 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((349 / 3200 : ℝ) - Real.pi * Real.exp (87 / 200 : ℝ)) ≤
      (2 / (1149596372263 / 10000000000 : ℝ) : ℝ) := by
    rw [show (349 / 3200 : ℝ) - Real.pi * Real.exp (87 / 200 : ℝ) =
      -(Real.pi * Real.exp (87 / 200 : ℝ) - (349 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48597159812261879 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (48597159812261879 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell348_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (87 / 400 : ℝ) (349 / 1600 : ℝ)) :
    (1406910523 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5696003973 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell348_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell348_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell349_leftExp :
    (7734477351 / 5000000000 : ℝ) ≤ Real.exp (349 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (349 / 800 : ℝ) (202745232603 / 200000000000 : ℝ)
    (7734477351 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell349_rightExp :
    Real.exp (7 / 16 : ℝ) ≤ (15488302987 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 16 : ℝ) (253441440617 / 250000000000 : ℝ)
    (15488302987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell349_denomUpper :
    Real.exp (47567319245838291 / 10000000000000000 : ℝ) ≤ (29091253543 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47567319245838291 / 10000000000000000 : ℝ)
    (1160264356447 / 1000000000000 : ℝ) (29091253543 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell349_denomLower :
    (1156235244213 / 10000000000 : ℝ) ≤ Real.exp (2968962146260349 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2968962146260349 / 625000000000000 : ℝ) (1160032599003 /
    1000000000000 : ℝ) (1156235244213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell349_product_lower :
    (3037321521260349 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (349 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell349_leftExp
    (by norm_num : (0 : ℝ) ≤ (7734477351 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell349_product_upper :
    Real.pi * Real.exp (7 / 16 : ℝ) ≤ (48657944245838291 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell349_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell349_endpointLower :
    (5612426671 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (349 / 1600 : ℝ) (7 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3037321521260349 / 625000000000000 : ℝ) (Real.pi * Real.exp (349 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell349_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 16 : ℝ) - (349 / 3200 : ℝ)) ≤
      (29091253543 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell349_denomUpper
    linarith [hpThetaJensenCell349_product_upper]
  have hi : (1 / (29091253543 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 16 : ℝ) - (349 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29091253543 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29091253543 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((349 / 3200 : ℝ) - Real.pi * Real.exp (7 / 16 : ℝ)) := by
    rw [show (349 / 3200 : ℝ) - Real.pi * Real.exp (7 / 16 : ℝ) =
      -(Real.pi * Real.exp (7 / 16 : ℝ) - (349 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (349 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (349 / 800 : ℝ)) := by
    have h := hpThetaJensenCell349_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29091253543 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell349_endpointUpper :
    hpThetaJensenKernelEndpointUpper (349 / 1600 : ℝ) (7 / 32 : ℝ) ≤ (5680641137 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 16 : ℝ)) (48657944245838291 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell349_product_upper
  have hD : (1156235244213 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (349 / 800 : ℝ) - (7 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell349_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell349_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (349 / 800 : ℝ) - (7 / 64 : ℝ)) ≤
      (1 / (1156235244213 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1156235244213 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 64 : ℝ) - Real.pi * Real.exp (349 / 800 : ℝ)) ≤
      (2 / (1156235244213 / 10000000000 : ℝ) : ℝ) := by
    rw [show (7 / 64 : ℝ) - Real.pi * Real.exp (349 / 800 : ℝ) =
      -(Real.pi * Real.exp (349 / 800 : ℝ) - (7 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48657944245838291 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (48657944245838291 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell349_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (349 / 1600 : ℝ) (7 / 32 : ℝ)) :
    (5612426671 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5680641137 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell349_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell349_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell350_leftExp :
    (7744151493 / 5000000000 : ℝ) ≤ Real.exp (7 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 16 : ℝ) (1013765762467 / 1000000000000 : ℝ)
    (7744151493 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell350_rightExp :
    Real.exp (351 / 800 : ℝ) ≤ (15507675471 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (351 / 800 : ℝ) (1013805363467 / 1000000000000 : ℝ)
    (15507675471 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell350_denomUpper :
    Real.exp (47625054705965303 / 10000000000000000 : ℝ) ≤ (292596990299 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47625054705965303 / 10000000000000000 : ℝ) (145059214259
    / 125000000000 : ℝ) (292596990299 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell350_denomLower :
    (232584257209 / 2000000000 : ℝ) ≤ Real.exp (2972565859649607 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2972565859649607 / 625000000000000 : ℝ) (580120819543 /
    500000000000 : ℝ) (232584257209 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell350_product_lower :
    (3041120547149607 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell350_leftExp
    (by norm_num : (0 : ℝ) ≤ (7744151493 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell350_product_upper :
    Real.pi * Real.exp (351 / 800 : ℝ) ≤ (48718804705965303 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell350_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell350_endpointLower :
    (89555267 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 32 : ℝ) (351 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3041120547149607 / 625000000000000 : ℝ) (Real.pi * Real.exp (7 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell350_product_lower
  have hD : Real.exp (Real.pi * Real.exp (351 / 800 : ℝ) - (7 / 64 : ℝ)) ≤
      (292596990299 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell350_denomUpper
    linarith [hpThetaJensenCell350_product_upper]
  have hi : (1 / (292596990299 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (351 / 800 : ℝ) - (7 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (292596990299 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (292596990299 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 64 : ℝ) - Real.pi * Real.exp (351 / 800 : ℝ)) := by
    rw [show (7 / 64 : ℝ) - Real.pi * Real.exp (351 / 800 : ℝ) =
      -(Real.pi * Real.exp (351 / 800 : ℝ) - (7 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 16 : ℝ)) := by
    have h := hpThetaJensenCell350_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (292596990299 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell350_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 32 : ℝ) (351 / 1600 : ℝ) ≤ (5665271013 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (351 / 800 : ℝ)) (48718804705965303 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (351 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell350_product_upper
  have hD : (232584257209 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 16 : ℝ) - (351 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell350_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell350_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 16 : ℝ) - (351 / 3200 : ℝ)) ≤
      (1 / (232584257209 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (232584257209 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((351 / 3200 : ℝ) - Real.pi * Real.exp (7 / 16 : ℝ)) ≤
      (2 / (232584257209 / 2000000000 : ℝ) : ℝ) := by
    rw [show (351 / 3200 : ℝ) - Real.pi * Real.exp (7 / 16 : ℝ) =
      -(Real.pi * Real.exp (7 / 16 : ℝ) - (351 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48718804705965303 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (48718804705965303 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell350_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 32 : ℝ) (351 / 1600 : ℝ)) :
    (89555267 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5665271013 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell350_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell350_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell351_leftExp :
    (1550767547 / 1000000000 : ℝ) ≤ Real.exp (351 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (351 / 800 : ℝ) (506902681733 / 500000000000 : ℝ)
    (1550767547 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell351_rightExp :
    Real.exp (11 / 25 : ℝ) ≤ (7763536093 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 25 : ℝ) (253461241503 / 250000000000 : ℝ)
    (7763536093 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell351_denomUpper :
    Real.exp (23841433145016149 / 5000000000000000 : ℝ) ≤ (5885868777 / 50000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23841433145016149 / 5000000000000000 : ℝ) (580341692793
    / 500000000000 : ℝ) (5885868777 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell351_denomLower :
    (584827441507 / 5000000000 : ℝ) ≤ Real.exp (595234864939353 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (595234864939353 / 125000000000000 : ℝ) (580225496271 /
    500000000000 : ℝ) (584827441507 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell351_product_lower :
    (608984864939353 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (351 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell351_leftExp
    (by norm_num : (0 : ℝ) ≤ (1550767547 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell351_product_upper :
    Real.pi * Real.exp (11 / 25 : ℝ) ≤ (24389870645016149 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell351_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell351_endpointLower :
    (11163949757 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (351 / 1600 : ℝ) (11 / 50 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (608984864939353 / 125000000000000 : ℝ) (Real.pi * Real.exp (351 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell351_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 25 : ℝ) - (351 / 3200 : ℝ)) ≤
      (5885868777 / 50000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell351_denomUpper
    linarith [hpThetaJensenCell351_product_upper]
  have hi : (1 / (5885868777 / 50000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 25 : ℝ) - (351 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5885868777 / 50000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5885868777 / 50000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((351 / 3200 : ℝ) - Real.pi * Real.exp (11 / 25 : ℝ)) := by
    rw [show (351 / 3200 : ℝ) - Real.pi * Real.exp (11 / 25 : ℝ) =
      -(Real.pi * Real.exp (11 / 25 : ℝ) - (351 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (351 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (351 / 800 : ℝ)) := by
    have h := hpThetaJensenCell351_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5885868777 / 50000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell351_endpointUpper :
    hpThetaJensenKernelEndpointUpper (351 / 1600 : ℝ) (11 / 50 : ℝ) ≤ (2259957539 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 25 : ℝ)) (24389870645016149 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell351_product_upper
  have hD : (584827441507 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (351 / 800 : ℝ) - (11 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell351_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell351_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (351 / 800 : ℝ) - (11 / 100 : ℝ)) ≤
      (1 / (584827441507 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (584827441507 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 100 : ℝ) - Real.pi * Real.exp (351 / 800 : ℝ)) ≤
      (2 / (584827441507 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 100 : ℝ) - Real.pi * Real.exp (351 / 800 : ℝ) =
      -(Real.pi * Real.exp (351 / 800 : ℝ) - (11 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24389870645016149 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (24389870645016149 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell351_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (351 / 1600 : ℝ) (11 / 50 : ℝ)) :
    (11163949757 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2259957539 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell351_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell351_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell352_leftExp :
    (1940884023 / 1250000000 : ℝ) ≤ Real.exp (11 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 25 : ℝ) (1013844966011 / 1000000000000 : ℝ)
    (1940884023 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell352_rightExp :
    Real.exp (353 / 800 : ℝ) ≤ (7773246581 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (353 / 800 : ℝ) (202776914021 / 200000000000 : ℝ)
    (7773246581 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell352_denomUpper :
    Real.exp (23870377046143533 / 5000000000000000 : ℝ) ≤ (1184007917177 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23870377046143533 / 5000000000000000 : ℝ) (232178674297
    / 200000000000 : ℝ) (1184007917177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell352_denomLower :
    (1176436424219 / 10000000000 : ℝ) ≤ Real.exp (744946886823077 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (744946886823077 / 156250000000000 : ℝ) (290165164967 /
    250000000000 : ℝ) (1176436424219 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell352_product_lower :
    (762183214948077 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell352_leftExp
    (by norm_num : (0 : ℝ) ≤ (1940884023 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell352_product_upper :
    Real.pi * Real.exp (353 / 800 : ℝ) ≤ (24420377046143533 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell352_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell352_endpointLower :
    (445339119 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 50 : ℝ) (353 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (762183214948077 / 156250000000000 : ℝ) (Real.pi * Real.exp (11 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell352_product_lower
  have hD : Real.exp (Real.pi * Real.exp (353 / 800 : ℝ) - (11 / 100 : ℝ)) ≤
      (1184007917177 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell352_denomUpper
    linarith [hpThetaJensenCell352_product_upper]
  have hi : (1 / (1184007917177 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (353 / 800 : ℝ) - (11 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1184007917177 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1184007917177 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 100 : ℝ) - Real.pi * Real.exp (353 / 800 : ℝ)) := by
    rw [show (11 / 100 : ℝ) - Real.pi * Real.exp (353 / 800 : ℝ) =
      -(Real.pi * Real.exp (353 / 800 : ℝ) - (11 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 25 : ℝ)) := by
    have h := hpThetaJensenCell352_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1184007917177 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell352_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 50 : ℝ) (353 / 1600 : ℝ) ≤ (11269019769 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (353 / 800 : ℝ)) (24420377046143533 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (353 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell352_product_upper
  have hD : (1176436424219 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 25 : ℝ) - (353 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell352_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell352_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 25 : ℝ) - (353 / 3200 : ℝ)) ≤
      (1 / (1176436424219 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1176436424219 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((353 / 3200 : ℝ) - Real.pi * Real.exp (11 / 25 : ℝ)) ≤
      (2 / (1176436424219 / 10000000000 : ℝ) : ℝ) := by
    rw [show (353 / 3200 : ℝ) - Real.pi * Real.exp (11 / 25 : ℝ) =
      -(Real.pi * Real.exp (11 / 25 : ℝ) - (353 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24420377046143533 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (24420377046143533 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell352_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 50 : ℝ) (353 / 1600 : ℝ)) :
    (445339119 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11269019769 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell352_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell352_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell353_leftExp :
    (388662329 / 250000000 : ℝ) ≤ Real.exp (353 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (353 / 800 : ℝ) (126735571263 / 125000000000 : ℝ)
    (388662329 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell353_rightExp :
    Real.exp (177 / 400 : ℝ) ≤ (15565938429 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (177 / 400 : ℝ) (7921282623 / 7812500000 : ℝ)
    (15565938429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell353_denomUpper :
    Real.exp (47798718206977397 / 10000000000000000 : ℝ) ≤ (238178168627 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47798718206977397 / 10000000000000000 : ℝ)
    (1161103672271 / 1000000000000 : ℝ) (238178168627 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell353_denomLower :
    (591633151551 / 5000000000 : ℝ) ≤ Real.exp (149170276685971 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (149170276685971 / 31250000000000 : ℝ) (580435320793 /
    500000000000 : ℝ) (591633151551 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell353_product_lower :
    (152627307935971 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (353 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell353_leftExp
    (by norm_num : (0 : ℝ) ≤ (388662329 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell353_product_upper :
    Real.pi * Real.exp (177 / 400 : ℝ) ≤ (48901843206977397 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell353_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell353_endpointLower :
    (11102993511 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (353 / 1600 : ℝ) (177 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (152627307935971 / 31250000000000 : ℝ) (Real.pi * Real.exp (353 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell353_product_lower
  have hD : Real.exp (Real.pi * Real.exp (177 / 400 : ℝ) - (353 / 3200 : ℝ)) ≤
      (238178168627 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell353_denomUpper
    linarith [hpThetaJensenCell353_product_upper]
  have hi : (1 / (238178168627 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (177 / 400 : ℝ) - (353 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (238178168627 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (238178168627 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((353 / 3200 : ℝ) - Real.pi * Real.exp (177 / 400 : ℝ)) := by
    rw [show (353 / 3200 : ℝ) - Real.pi * Real.exp (177 / 400 : ℝ) =
      -(Real.pi * Real.exp (177 / 400 : ℝ) - (353 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (353 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (353 / 800 : ℝ)) := by
    have h := hpThetaJensenCell353_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (238178168627 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell353_endpointUpper :
    hpThetaJensenKernelEndpointUpper (353 / 1600 : ℝ) (177 / 800 : ℝ) ≤ (5619119363 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (177 / 400 : ℝ)) (48901843206977397 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (177 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell353_product_upper
  have hD : (591633151551 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (353 / 800 : ℝ) - (177 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell353_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell353_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (353 / 800 : ℝ) - (177 / 1600 : ℝ)) ≤
      (1 / (591633151551 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (591633151551 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((177 / 1600 : ℝ) - Real.pi * Real.exp (353 / 800 : ℝ)) ≤
      (2 / (591633151551 / 5000000000 : ℝ) : ℝ) := by
    rw [show (177 / 1600 : ℝ) - Real.pi * Real.exp (353 / 800 : ℝ) =
      -(Real.pi * Real.exp (353 / 800 : ℝ) - (177 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48901843206977397 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (48901843206977397 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell353_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (353 / 1600 : ℝ) (177 / 800 : ℝ)) :
    (11102993511 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5619119363 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell353_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell353_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell354_leftExp :
    (15565938427 / 10000000000 : ℝ) ≤ Real.exp (177 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (177 / 400 : ℝ) (1013924175743 / 1000000000000 : ℝ)
    (15565938427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell354_rightExp :
    Real.exp (71 / 160 : ℝ) ≤ (7792704009 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 160 : ℝ) (1013963782931 / 1000000000000 : ℝ)
    (7792704009 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell354_denomUpper :
    Real.exp (23928379365746337 / 5000000000000000 : ℝ) ≤ (598911466841 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23928379365746337 / 5000000000000000 : ℝ) (290328572113
    / 250000000000 : ℝ) (598911466841 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell354_denomLower :
    (238028983107 / 2000000000 : ℝ) ≤ Real.exp (5974056579344473 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5974056579344473 / 1250000000000000 : ℝ) (1161080938183
    / 1000000000000 : ℝ) (238028983107 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell354_product_lower :
    (6112728454344473 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (177 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell354_leftExp
    (by norm_num : (0 : ℝ) ≤ (15565938427 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell354_product_upper :
    Real.pi * Real.exp (71 / 160 : ℝ) ≤ (24481504365746337 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell354_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell354_endpointLower :
    (11072496843 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (177 / 800 : ℝ) (71 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6112728454344473 / 1250000000000000 : ℝ) (Real.pi * Real.exp (177 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell354_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 160 : ℝ) - (177 / 1600 : ℝ)) ≤
      (598911466841 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell354_denomUpper
    linarith [hpThetaJensenCell354_product_upper]
  have hi : (1 / (598911466841 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 160 : ℝ) - (177 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (598911466841 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (598911466841 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((177 / 1600 : ℝ) - Real.pi * Real.exp (71 / 160 : ℝ)) := by
    rw [show (177 / 1600 : ℝ) - Real.pi * Real.exp (71 / 160 : ℝ) =
      -(Real.pi * Real.exp (71 / 160 : ℝ) - (177 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (177 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (177 / 400 : ℝ)) := by
    have h := hpThetaJensenCell354_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (598911466841 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell354_endpointUpper :
    hpThetaJensenKernelEndpointUpper (177 / 800 : ℝ) (71 / 320 : ℝ) ≤ (11207445057 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 160 : ℝ)) (24481504365746337 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell354_product_upper
  have hD : (238028983107 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (177 / 400 : ℝ) - (71 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell354_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell354_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (177 / 400 : ℝ) - (71 / 640 : ℝ)) ≤
      (1 / (238028983107 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (238028983107 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 640 : ℝ) - Real.pi * Real.exp (177 / 400 : ℝ)) ≤
      (2 / (238028983107 / 2000000000 : ℝ) : ℝ) := by
    rw [show (71 / 640 : ℝ) - Real.pi * Real.exp (177 / 400 : ℝ) =
      -(Real.pi * Real.exp (177 / 400 : ℝ) - (71 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24481504365746337 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (24481504365746337 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell354_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (177 / 800 : ℝ) (71 / 320 : ℝ)) :
    (11072496843 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11207445057 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell354_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell354_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell355_leftExp :
    (974088001 / 625000000 : ℝ) ≤ Real.exp (71 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 160 : ℝ) (101396378293 / 100000000000 : ℝ)
    (974088001 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell355_rightExp :
    Real.exp (89 / 200 : ℝ) ≤ (15604901959 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89 / 200 : ℝ) (202800678333 / 200000000000 : ℝ)
    (15604901959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell355_denomUpper :
    Real.exp (47914875760080687 / 10000000000000000 : ℝ) ≤ (120480459267 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47914875760080687 / 10000000000000000 : ℝ) (116152522053
    / 100000000000 : ℝ) (120480459267 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell355_denomLower :
    (47882906471 / 400000000 : ℝ) ≤ Real.exp (373831977654699 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (373831977654699 / 78125000000000 : ℝ) (116129155017 /
    100000000000 : ℝ) (47882906471 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell355_product_lower :
    (382523383904699 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell355_leftExp
    (by norm_num : (0 : ℝ) ≤ (974088001 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell355_product_upper :
    Real.pi * Real.exp (89 / 200 : ℝ) ≤ (49024250760080687 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell355_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell355_endpointLower :
    (11041988453 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 320 : ℝ) (89 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (382523383904699 / 78125000000000 : ℝ) (Real.pi * Real.exp (71 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell355_product_lower
  have hD : Real.exp (Real.pi * Real.exp (89 / 200 : ℝ) - (71 / 640 : ℝ)) ≤
      (120480459267 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell355_denomUpper
    linarith [hpThetaJensenCell355_product_upper]
  have hi : (1 / (120480459267 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (89 / 200 : ℝ) - (71 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (120480459267 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (120480459267 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 640 : ℝ) - Real.pi * Real.exp (89 / 200 : ℝ)) := by
    rw [show (71 / 640 : ℝ) - Real.pi * Real.exp (89 / 200 : ℝ) =
      -(Real.pi * Real.exp (89 / 200 : ℝ) - (71 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 160 : ℝ)) := by
    have h := hpThetaJensenCell355_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (120480459267 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell355_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 320 : ℝ) (89 / 400 : ℝ) ≤ (5588319623 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (89 / 200 : ℝ)) (49024250760080687 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (89 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell355_product_upper
  have hD : (47882906471 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 160 : ℝ) - (89 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell355_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell355_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 160 : ℝ) - (89 / 800 : ℝ)) ≤
      (1 / (47882906471 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (47882906471 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((89 / 800 : ℝ) - Real.pi * Real.exp (71 / 160 : ℝ)) ≤
      (2 / (47882906471 / 400000000 : ℝ) : ℝ) := by
    rw [show (89 / 800 : ℝ) - Real.pi * Real.exp (71 / 160 : ℝ) =
      -(Real.pi * Real.exp (71 / 160 : ℝ) - (89 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49024250760080687 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (49024250760080687 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell355_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 320 : ℝ) (89 / 400 : ℝ)) :
    (11041988453 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5588319623 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell355_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell355_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell356_leftExp :
    (7802450979 / 5000000000 : ℝ) ≤ Real.exp (89 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (89 / 200 : ℝ) (63375211979 / 62500000000 : ℝ)
    (7802450979 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell356_rightExp :
    Real.exp (357 / 800 : ℝ) ≤ (15624420283 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (357 / 800 : ℝ) (507021500973 / 500000000000 : ℝ)
    (15624420283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell356_denomUpper :
    Real.exp (47973069390130819 / 10000000000000000 : ℝ) ≤ (1211836227927 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47973069390130819 / 10000000000000000 : ℝ) (145217058627
    / 125000000000 : ℝ) (1211836227927 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell356_denomLower :
    (602024972877 / 5000000000 : ℝ) ≤ Real.exp (2994288134502321 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2994288134502321 / 625000000000000 : ℝ) (1161502478059 /
    1000000000000 : ℝ) (602024972877 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell356_product_lower :
    (3064014697002321 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (89 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell356_leftExp
    (by norm_num : (0 : ℝ) ≤ (7802450979 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell356_product_upper :
    Real.pi * Real.exp (357 / 800 : ℝ) ≤ (49085569390130819 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell356_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell356_endpointLower :
    (550573441 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 400 : ℝ) (357 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3064014697002321 / 625000000000000 : ℝ) (Real.pi * Real.exp (89 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell356_product_lower
  have hD : Real.exp (Real.pi * Real.exp (357 / 800 : ℝ) - (89 / 800 : ℝ)) ≤
      (1211836227927 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell356_denomUpper
    linarith [hpThetaJensenCell356_product_upper]
  have hi : (1 / (1211836227927 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (357 / 800 : ℝ) - (89 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1211836227927 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1211836227927 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((89 / 800 : ℝ) - Real.pi * Real.exp (357 / 800 : ℝ)) := by
    rw [show (89 / 800 : ℝ) - Real.pi * Real.exp (357 / 800 : ℝ) =
      -(Real.pi * Real.exp (357 / 800 : ℝ) - (89 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (89 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (89 / 200 : ℝ)) := by
    have h := hpThetaJensenCell356_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1211836227927 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell356_endpointUpper :
    hpThetaJensenKernelEndpointUpper (89 / 400 : ℝ) (357 / 1600 : ℝ) ≤ (11145821773 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (357 / 800 : ℝ)) (49085569390130819 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (357 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell356_product_upper
  have hD : (602024972877 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (89 / 200 : ℝ) - (357 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell356_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell356_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (89 / 200 : ℝ) - (357 / 3200 : ℝ)) ≤
      (1 / (602024972877 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (602024972877 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((357 / 3200 : ℝ) - Real.pi * Real.exp (89 / 200 : ℝ)) ≤
      (2 / (602024972877 / 5000000000 : ℝ) : ℝ) := by
    rw [show (357 / 3200 : ℝ) - Real.pi * Real.exp (89 / 200 : ℝ) =
      -(Real.pi * Real.exp (89 / 200 : ℝ) - (357 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49085569390130819 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (49085569390130819 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell356_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (89 / 400 : ℝ) (357 / 1600 : ℝ)) :
    (550573441 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11145821773 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell356_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell356_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell357_leftExp :
    (15624420281 / 10000000000 : ℝ) ≤ Real.exp (357 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (357 / 800 : ℝ) (202808600389 / 200000000000 : ℝ)
    (15624420281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell357_rightExp :
    Real.exp (179 / 400 : ℝ) ≤ (782198151 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (179 / 400 : ℝ) (507041306887 / 500000000000 : ℝ)
    (782198151 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell357_denomUpper :
    Real.exp (2401566985794543 / 500000000000000 : ℝ) ≤ (152364781333 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2401566985794543 / 500000000000000 : ℝ) (1161948034411 /
    1000000000000 : ℝ) (152364781333 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell357_denomLower :
    (605538586941 / 5000000000 : ℝ) ≤ Real.exp (5995850469928419 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5995850469928419 / 1250000000000000 : ℝ) (580856861163 /
    500000000000 : ℝ) (605538586941 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell357_product_lower :
    (6135694219928419 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (357 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell357_leftExp
    (by norm_num : (0 : ℝ) ≤ (15624420281 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell357_product_upper :
    Real.pi * Real.exp (179 / 400 : ℝ) ≤ (2457348235794543 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell357_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell357_endpointLower :
    (10980938421 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (357 / 1600 : ℝ) (179 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6135694219928419 / 1250000000000000 : ℝ) (Real.pi * Real.exp (357 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell357_product_lower
  have hD : Real.exp (Real.pi * Real.exp (179 / 400 : ℝ) - (357 / 3200 : ℝ)) ≤
      (152364781333 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell357_denomUpper
    linarith [hpThetaJensenCell357_product_upper]
  have hi : (1 / (152364781333 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (179 / 400 : ℝ) - (357 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (152364781333 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (152364781333 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((357 / 3200 : ℝ) - Real.pi * Real.exp (179 / 400 : ℝ)) := by
    rw [show (357 / 3200 : ℝ) - Real.pi * Real.exp (179 / 400 : ℝ) =
      -(Real.pi * Real.exp (179 / 400 : ℝ) - (357 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (357 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (357 / 800 : ℝ)) := by
    have h := hpThetaJensenCell357_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (152364781333 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell357_endpointUpper :
    hpThetaJensenKernelEndpointUpper (357 / 1600 : ℝ) (179 / 800 : ℝ) ≤ (2778748283 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (179 / 400 : ℝ)) (2457348235794543 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (179 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell357_product_upper
  have hD : (605538586941 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (357 / 800 : ℝ) - (179 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell357_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell357_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (357 / 800 : ℝ) - (179 / 1600 : ℝ)) ≤
      (1 / (605538586941 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (605538586941 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((179 / 1600 : ℝ) - Real.pi * Real.exp (357 / 800 : ℝ)) ≤
      (2 / (605538586941 / 5000000000 : ℝ) : ℝ) := by
    rw [show (179 / 1600 : ℝ) - Real.pi * Real.exp (357 / 800 : ℝ) =
      -(Real.pi * Real.exp (357 / 800 : ℝ) - (179 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2457348235794543 / 500000000000000 : ℝ) ^ 2 - 6 *
      (2457348235794543 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell357_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (357 / 1600 : ℝ) (179 / 800 : ℝ)) :
    (10980938421 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2778748283 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell357_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell357_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell358_leftExp :
    (7821981509 / 5000000000 : ℝ) ≤ Real.exp (179 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (179 / 400 : ℝ) (1014082613773 / 1000000000000 : ℝ)
    (7821981509 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell358_rightExp :
    Real.exp (359 / 800 : ℝ) ≤ (15663530201 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (359 / 800 : ℝ) (20282444543 / 20000000000 : ℝ)
    (15663530201 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell358_denomUpper :
    Real.exp (48089686834750193 / 10000000000000000 : ℝ) ≤ (122605107621 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48089686834750193 / 10000000000000000 : ℝ)
    (1162159917227 / 1000000000000 : ℝ) (122605107621 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell358_denomLower :
    (609077379137 / 5000000000 : ℝ) ≤ Real.exp (3001567129102791 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3001567129102791 / 625000000000000 : ℝ) (1161925283507 /
    1000000000000 : ℝ) (609077379137 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell358_product_lower :
    (3071684316602791 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (179 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell358_leftExp
    (by norm_num : (0 : ℝ) ≤ (7821981509 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell358_product_upper :
    Real.pi * Real.exp (359 / 800 : ℝ) ≤ (49208436834750193 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell358_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell358_endpointLower :
    (5475198869 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (179 / 800 : ℝ) (359 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3071684316602791 / 625000000000000 : ℝ) (Real.pi * Real.exp (179 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell358_product_lower
  have hD : Real.exp (Real.pi * Real.exp (359 / 800 : ℝ) - (179 / 1600 : ℝ)) ≤
      (122605107621 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell358_denomUpper
    linarith [hpThetaJensenCell358_product_upper]
  have hi : (1 / (122605107621 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (359 / 800 : ℝ) - (179 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (122605107621 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (122605107621 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((179 / 1600 : ℝ) - Real.pi * Real.exp (359 / 800 : ℝ)) := by
    rw [show (179 / 1600 : ℝ) - Real.pi * Real.exp (359 / 800 : ℝ) =
      -(Real.pi * Real.exp (359 / 800 : ℝ) - (179 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (179 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (179 / 400 : ℝ)) := by
    have h := hpThetaJensenCell358_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (122605107621 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell358_endpointUpper :
    hpThetaJensenKernelEndpointUpper (179 / 800 : ℝ) (359 / 1600 : ℝ) ≤ (11084153797 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (359 / 800 : ℝ)) (49208436834750193 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (359 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell358_product_upper
  have hD : (609077379137 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (179 / 400 : ℝ) - (359 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell358_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell358_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (179 / 400 : ℝ) - (359 / 3200 : ℝ)) ≤
      (1 / (609077379137 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (609077379137 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((359 / 3200 : ℝ) - Real.pi * Real.exp (179 / 400 : ℝ)) ≤
      (2 / (609077379137 / 5000000000 : ℝ) : ℝ) := by
    rw [show (359 / 3200 : ℝ) - Real.pi * Real.exp (179 / 400 : ℝ) =
      -(Real.pi * Real.exp (179 / 400 : ℝ) - (359 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49208436834750193 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (49208436834750193 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell358_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (179 / 800 : ℝ) (359 / 1600 : ℝ)) :
    (5475198869 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11084153797 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell358_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell358_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell359_leftExp :
    (15663530199 / 10000000000 : ℝ) ≤ Real.exp (359 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (359 / 800 : ℝ) (1014122227149 / 1000000000000 : ℝ)
    (15663530199 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell359_rightExp :
    Real.exp (9 / 20 : ℝ) ≤ (3136624371 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 20 : ℝ) (1014161842073 / 1000000000000 : ℝ)
    (3136624371 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell359_denomUpper :
    Real.exp (9629622167563003 / 2000000000000000 : ℝ) ≤ (1233235123007 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9629622167563003 / 2000000000000000 : ℝ) (290593029489 /
    250000000000 : ℝ) (1233235123007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell359_denomLower :
    (1225283113667 / 10000000000 : ℝ) ≤ Real.exp (6010427645617101 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6010427645617101 / 1250000000000000 : ℝ) (145267145263 /
    125000000000 : ℝ) (1225283113667 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell359_product_lower :
    (6151052645617101 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (359 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell359_leftExp
    (by norm_num : (0 : ℝ) ≤ (15663530199 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell359_product_upper :
    Real.pi * Real.exp (9 / 20 : ℝ) ≤ (9853997167563003 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell359_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell359_endpointLower :
    (10919847251 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (359 / 1600 : ℝ) (9 / 40 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6151052645617101 / 1250000000000000 : ℝ) (Real.pi * Real.exp (359 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell359_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 20 : ℝ) - (359 / 3200 : ℝ)) ≤
      (1233235123007 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell359_denomUpper
    linarith [hpThetaJensenCell359_product_upper]
  have hi : (1 / (1233235123007 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 20 : ℝ) - (359 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1233235123007 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1233235123007 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((359 / 3200 : ℝ) - Real.pi * Real.exp (9 / 20 : ℝ)) := by
    rw [show (359 / 3200 : ℝ) - Real.pi * Real.exp (9 / 20 : ℝ) =
      -(Real.pi * Real.exp (9 / 20 : ℝ) - (359 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (359 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (359 / 800 : ℝ)) := by
    have h := hpThetaJensenCell359_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1233235123007 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell359_endpointUpper :
    hpThetaJensenKernelEndpointUpper (359 / 1600 : ℝ) (9 / 40 : ℝ) ≤ (44213217 / 40000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 20 : ℝ)) (9853997167563003 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell359_product_upper
  have hD : (1225283113667 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (359 / 800 : ℝ) - (9 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell359_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell359_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (359 / 800 : ℝ) - (9 / 80 : ℝ)) ≤
      (1 / (1225283113667 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1225283113667 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 80 : ℝ) - Real.pi * Real.exp (359 / 800 : ℝ)) ≤
      (2 / (1225283113667 / 10000000000 : ℝ) : ℝ) := by
    rw [show (9 / 80 : ℝ) - Real.pi * Real.exp (359 / 800 : ℝ) =
      -(Real.pi * Real.exp (359 / 800 : ℝ) - (9 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9853997167563003 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (9853997167563003 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell359_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (359 / 1600 : ℝ) (9 / 40 : ℝ)) :
    (10919847251 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (44213217 / 40000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell359_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell359_endpointUpper

def hpThetaJensenCellsBatch017Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (718635261 / 625000000 : ℝ)
  | 1 => (11467863799 / 10000000000 : ℝ)
  | 2 => (11437545419 / 10000000000 : ℝ)
  | 3 => (11407209517 / 10000000000 : ℝ)
  | 4 => (5688428289 / 5000000000 : ℝ)
  | 5 => (709155443 / 625000000 : ℝ)
  | 6 => (11316101539 / 10000000000 : ℝ)
  | 7 => (1128570041 / 1000000000 : ℝ)
  | 8 => (1406910523 / 1250000000 : ℝ)
  | 9 => (5612426671 / 5000000000 : ℝ)
  | 10 => (89555267 / 80000000 : ℝ)
  | 11 => (11163949757 / 10000000000 : ℝ)
  | 12 => (445339119 / 400000000 : ℝ)
  | 13 => (11102993511 / 10000000000 : ℝ)
  | 14 => (11072496843 / 10000000000 : ℝ)
  | 15 => (11041988453 / 10000000000 : ℝ)
  | 16 => (550573441 / 500000000 : ℝ)
  | 17 => (10980938421 / 10000000000 : ℝ)
  | 18 => (5475198869 / 5000000000 : ℝ)
  | 19 => (10919847251 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch017Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2909307539 / 2500000000 : ℝ)
  | 1 => (11606638647 / 10000000000 : ℝ)
  | 2 => (11576028651 / 10000000000 : ℝ)
  | 3 => (577270033 / 500000000 : ℝ)
  | 4 => (359836099 / 312500000 : ℝ)
  | 5 => (2296818533 / 2000000000 : ℝ)
  | 6 => (11453413631 / 10000000000 : ℝ)
  | 7 => (71391991 / 62500000 : ℝ)
  | 8 => (5696003973 / 5000000000 : ℝ)
  | 9 => (5680641137 / 5000000000 : ℝ)
  | 10 => (5665271013 / 5000000000 : ℝ)
  | 11 => (2259957539 / 2000000000 : ℝ)
  | 12 => (11269019769 / 10000000000 : ℝ)
  | 13 => (5619119363 / 5000000000 : ℝ)
  | 14 => (11207445057 / 10000000000 : ℝ)
  | 15 => (5588319623 / 5000000000 : ℝ)
  | 16 => (11145821773 / 10000000000 : ℝ)
  | 17 => (2778748283 / 2500000000 : ℝ)
  | 18 => (11084153797 / 10000000000 : ℝ)
  | 19 => (44213217 / 40000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch017_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch017Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch017Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell340_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell341_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell342_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell343_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell344_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell345_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell346_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell347_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell348_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell349_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell350_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell351_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell352_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell353_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell354_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell355_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell356_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell357_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell358_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell359_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper] at h ⊢
    exact h

end HodgeProofHP
