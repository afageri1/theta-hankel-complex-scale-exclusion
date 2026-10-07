import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1380_leftExp :
    (11225042059 / 2000000000 : ℝ) ≤ Real.exp (69 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 40 : ℝ) (1055385655111 / 1000000000000 : ℝ)
    (11225042059 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1380_rightExp :
    Real.exp (1381 / 800 : ℝ) ≤ (28097705339 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1381 / 800 : ℝ) (1649104503 / 1562500000 : ℝ)
    (28097705339 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1380_denomUpper :
    Real.exp (86115304409065027 / 5000000000000000 : ℝ) ≤ (75477987370006693 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (86115304409065027 / 5000000000000000 : ℝ) (1712956204657
    / 1000000000000 : ℝ) (75477987370006693 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1380_denomLower :
    (18452031611480227 / 625000000 : ℝ) ≤ Real.exp (4300172166527241 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4300172166527241 / 250000000000000 : ℝ) (855879520569 /
    500000000000 : ℝ) (18452031611480227 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1380_product_lower :
    (4408062791527241 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1380_leftExp
    (by norm_num : (0 : ℝ) ≤ (11225042059 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1380_product_upper :
    Real.pi * Real.exp (1381 / 800 : ℝ) ≤ (88271554409065027 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1380_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1380_endpointLower :
    (188431 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 80 : ℝ) (1381 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4408062791527241 / 250000000000000 : ℝ) (Real.pi * Real.exp (69 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1380_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1381 / 800 : ℝ) - (69 / 160 : ℝ)) ≤
      (75477987370006693 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1380_denomUpper
    linarith [hpThetaJensenCell1380_product_upper]
  have hi : (1 / (75477987370006693 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1381 / 800 : ℝ) - (69 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (75477987370006693 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (75477987370006693 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 160 : ℝ) - Real.pi * Real.exp (1381 / 800 : ℝ)) := by
    rw [show (69 / 160 : ℝ) - Real.pi * Real.exp (1381 / 800 : ℝ) =
      -(Real.pi * Real.exp (1381 / 800 : ℝ) - (69 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1380_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (75477987370006693 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1380_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 80 : ℝ) (1381 / 1600 : ℝ) ≤ (48427 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1381 / 800 : ℝ)) (88271554409065027 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1381 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1380_product_upper
  have hD : (18452031611480227 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 40 : ℝ) - (1381 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1380_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1380_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 40 : ℝ) - (1381 / 3200 : ℝ)) ≤
      (1 / (18452031611480227 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18452031611480227 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1381 / 3200 : ℝ) - Real.pi * Real.exp (69 / 40 : ℝ)) ≤
      (2 / (18452031611480227 / 625000000 : ℝ) : ℝ) := by
    rw [show (1381 / 3200 : ℝ) - Real.pi * Real.exp (69 / 40 : ℝ) =
      -(Real.pi * Real.exp (69 / 40 : ℝ) - (1381 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88271554409065027 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (88271554409065027 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1380_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 80 : ℝ) (1381 / 1600 : ℝ)) :
    (188431 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (48427 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1380_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1380_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1381_leftExp :
    (2247816427 / 400000000 : ℝ) ≤ Real.exp (1381 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1381 / 800 : ℝ) (1055426881919 / 1000000000000 : ℝ)
    (2247816427 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1381_rightExp :
    Real.exp (691 / 400 : ℝ) ≤ (28132849431 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (691 / 400 : ℝ) (527734055169 / 500000000000 : ℝ)
    (28132849431 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1381_denomUpper :
    Real.exp (86224150342483583 / 5000000000000000 : ℝ) ≤ (77139096667528459 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (86224150342483583 / 5000000000000000 : ℝ) (857060951549
    / 500000000000 : ℝ) (77139096667528459 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1381_denomLower :
    (150860808814729137 / 5000000000 : ℝ) ≤ Real.exp (861121513066473 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (861121513066473 / 50000000000000 : ℝ) (428230611987 /
    250000000000 : ℝ) (150860808814729137 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1381_product_lower :
    (882715263066473 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1381 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1381_leftExp
    (by norm_num : (0 : ℝ) ≤ (2247816427 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1381_product_upper :
    Real.pi * Real.exp (691 / 400 : ℝ) ≤ (88381962842483583 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1381_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1381_endpointLower :
    (29577 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (1381 / 1600 : ℝ) (691 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (882715263066473 / 50000000000000 : ℝ) (Real.pi * Real.exp (1381 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1381_product_lower
  have hD : Real.exp (Real.pi * Real.exp (691 / 400 : ℝ) - (1381 / 3200 : ℝ)) ≤
      (77139096667528459 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1381_denomUpper
    linarith [hpThetaJensenCell1381_product_upper]
  have hi : (1 / (77139096667528459 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (691 / 400 : ℝ) - (1381 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (77139096667528459 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (77139096667528459 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1381 / 3200 : ℝ) - Real.pi * Real.exp (691 / 400 : ℝ)) := by
    rw [show (1381 / 3200 : ℝ) - Real.pi * Real.exp (691 / 400 : ℝ) =
      -(Real.pi * Real.exp (691 / 400 : ℝ) - (1381 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1381 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1381 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1381_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (77139096667528459 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1381_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1381 / 1600 : ℝ) (691 / 800 : ℝ) ≤ (380077 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (691 / 400 : ℝ)) (88381962842483583 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (691 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1381_product_upper
  have hD : (150860808814729137 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1381 / 800 : ℝ) - (691 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1381_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1381_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1381 / 800 : ℝ) - (691 / 1600 : ℝ)) ≤
      (1 / (150860808814729137 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (150860808814729137 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((691 / 1600 : ℝ) - Real.pi * Real.exp (1381 / 800 : ℝ)) ≤
      (2 / (150860808814729137 / 5000000000 : ℝ) : ℝ) := by
    rw [show (691 / 1600 : ℝ) - Real.pi * Real.exp (1381 / 800 : ℝ) =
      -(Real.pi * Real.exp (1381 / 800 : ℝ) - (691 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88381962842483583 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (88381962842483583 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1381_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1381 / 1600 : ℝ) (691 / 800 : ℝ)) :
    (29577 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (380077 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1381_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1381_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1382_leftExp :
    (2813284943 / 500000000 : ℝ) ≤ Real.exp (691 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (691 / 400 : ℝ) (1055468110337 / 1000000000000 : ℝ)
    (2813284943 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1382_rightExp :
    Real.exp (1383 / 800 : ℝ) ≤ (56336074961 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1383 / 800 : ℝ) (527754670183 / 500000000000 : ℝ)
    (56336074961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1382_denomUpper :
    Real.exp (172666268744952873 / 10000000000000000 : ℝ) ≤ (19709735220242759 / 625000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (172666268744952873 / 10000000000000000 : ℝ)
    (1715289875291 / 1000000000000 : ℝ) (19709735220242759 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1382_denomLower :
    (154180931974985571 / 5000000000 : ℝ) ≤ Real.exp (1077762465081157 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1077762465081157 / 62500000000000 : ℝ) (1714088123057 /
    1000000000000 : ℝ) (154180931974985571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1382_product_lower :
    (1104774183831157 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (691 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1382_leftExp
    (by norm_num : (0 : ℝ) ≤ (2813284943 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1382_product_upper :
    Real.pi * Real.exp (1383 / 800 : ℝ) ≤ (176985018744952873 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1382_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1382_endpointLower :
    (725377 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (691 / 800 : ℝ) (1383 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1104774183831157 / 62500000000000 : ℝ) (Real.pi * Real.exp (691 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1382_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1383 / 800 : ℝ) - (691 / 1600 : ℝ)) ≤
      (19709735220242759 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1382_denomUpper
    linarith [hpThetaJensenCell1382_product_upper]
  have hi : (1 / (19709735220242759 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1383 / 800 : ℝ) - (691 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19709735220242759 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19709735220242759 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((691 / 1600 : ℝ) - Real.pi * Real.exp (1383 / 800 : ℝ)) := by
    rw [show (691 / 1600 : ℝ) - Real.pi * Real.exp (1383 / 800 : ℝ) =
      -(Real.pi * Real.exp (1383 / 800 : ℝ) - (691 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (691 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (691 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1382_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19709735220242759 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1382_endpointUpper :
    hpThetaJensenKernelEndpointUpper (691 / 800 : ℝ) (1383 / 1600 : ℝ) ≤ (745733 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1383 / 800 : ℝ)) (176985018744952873 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1383 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1382_product_upper
  have hD : (154180931974985571 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (691 / 400 : ℝ) - (1383 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1382_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1382_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (691 / 400 : ℝ) - (1383 / 3200 : ℝ)) ≤
      (1 / (154180931974985571 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (154180931974985571 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1383 / 3200 : ℝ) - Real.pi * Real.exp (691 / 400 : ℝ)) ≤
      (2 / (154180931974985571 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1383 / 3200 : ℝ) - Real.pi * Real.exp (691 / 400 : ℝ) =
      -(Real.pi * Real.exp (691 / 400 : ℝ) - (1383 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (176985018744952873 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (176985018744952873 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1382_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (691 / 800 : ℝ) (1383 / 1600 : ℝ)) :
    (725377 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (745733 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1382_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1382_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1383_leftExp :
    (56336074959 / 10000000000 : ℝ) ≤ Real.exp (1383 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1383 / 800 : ℝ) (211101868073 / 200000000000 : ℝ)
    (56336074959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1383_rightExp :
    Real.exp (173 / 100 : ℝ) ≤ (28203269543 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (173 / 100 : ℝ) (211110114401 / 200000000000 : ℝ)
    (28203269543 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1383_denomUpper :
    Real.exp (86442256673401999 / 5000000000000000 : ℝ) ≤ (161156942636811831 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (86442256673401999 / 5000000000000000 : ℝ) (107278757917
    / 62500000000 : ℝ) (161156942636811831 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1383_denomLower :
    (39394619007680157 / 1250000000 : ℝ) ≤ Real.exp (21582495300324341 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (21582495300324341 / 1250000000000000 : ℝ) (343051214371
    / 200000000000 : ℝ) (39394619007680157 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1383_product_lower :
    (22123120300324341 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1383 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1383_leftExp
    (by norm_num : (0 : ℝ) ≤ (56336074959 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1383_product_upper :
    Real.pi * Real.exp (173 / 100 : ℝ) ≤ (88603194173401999 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1383_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1383_endpointLower :
    (711577 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1383 / 1600 : ℝ) (173 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22123120300324341 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1383 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1383_product_lower
  have hD : Real.exp (Real.pi * Real.exp (173 / 100 : ℝ) - (1383 / 3200 : ℝ)) ≤
      (161156942636811831 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1383_denomUpper
    linarith [hpThetaJensenCell1383_product_upper]
  have hi : (1 / (161156942636811831 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (173 / 100 : ℝ) - (1383 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (161156942636811831 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (161156942636811831 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1383 / 3200 : ℝ) - Real.pi * Real.exp (173 / 100 : ℝ)) := by
    rw [show (1383 / 3200 : ℝ) - Real.pi * Real.exp (173 / 100 : ℝ) =
      -(Real.pi * Real.exp (173 / 100 : ℝ) - (1383 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1383 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1383 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1383_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (161156942636811831 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1383_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1383 / 1600 : ℝ) (173 / 200 : ℝ) ≤ (146313 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (173 / 100 : ℝ)) (88603194173401999 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (173 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1383_product_upper
  have hD : (39394619007680157 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1383 / 800 : ℝ) - (173 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1383_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1383_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1383 / 800 : ℝ) - (173 / 400 : ℝ)) ≤
      (1 / (39394619007680157 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (39394619007680157 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((173 / 400 : ℝ) - Real.pi * Real.exp (1383 / 800 : ℝ)) ≤
      (2 / (39394619007680157 / 1250000000 : ℝ) : ℝ) := by
    rw [show (173 / 400 : ℝ) - Real.pi * Real.exp (1383 / 800 : ℝ) =
      -(Real.pi * Real.exp (1383 / 800 : ℝ) - (173 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (88603194173401999 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (88603194173401999 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1383_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1383 / 1600 : ℝ) (173 / 200 : ℝ)) :
    (711577 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (146313 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1383_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1383_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1384_leftExp :
    (56406539083 / 10000000000 : ℝ) ≤ Real.exp (173 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (173 / 100 : ℝ) (263887643001 / 250000000000 : ℝ)
    (56406539083 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1384_rightExp :
    Real.exp (277 / 160 : ℝ) ≤ (11295418269 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (277 / 160 : ℝ) (527795902627 / 500000000000 : ℝ)
    (11295418269 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1384_denomUpper :
    Real.exp (34620606965962517 / 2000000000000000 : ℝ) ≤ (65886930959425337 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (34620606965962517 / 2000000000000000 : ℝ) (1717632662641
    / 1000000000000 : ℝ) (65886930959425337 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1384_denomLower :
    (322110684794041009 / 10000000000 : ℝ) ≤ Real.exp (21609775866355017 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (21609775866355017 / 1250000000000000 : ℝ) (1716426299779
    / 1000000000000 : ℝ) (322110684794041009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1384_product_lower :
    (22150791491355017 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (173 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1384_leftExp
    (by norm_num : (0 : ℝ) ≤ (56406539083 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1384_product_upper :
    Real.pi * Real.exp (277 / 160 : ℝ) ≤ (35485606965962517 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1384_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1384_endpointLower :
    (698019 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (173 / 200 : ℝ) (277 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22150791491355017 / 1250000000000000 : ℝ) (Real.pi * Real.exp (173 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1384_product_lower
  have hD : Real.exp (Real.pi * Real.exp (277 / 160 : ℝ) - (173 / 400 : ℝ)) ≤
      (65886930959425337 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1384_denomUpper
    linarith [hpThetaJensenCell1384_product_upper]
  have hi : (1 / (65886930959425337 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (277 / 160 : ℝ) - (173 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65886930959425337 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65886930959425337 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((173 / 400 : ℝ) - Real.pi * Real.exp (277 / 160 : ℝ)) := by
    rw [show (173 / 400 : ℝ) - Real.pi * Real.exp (277 / 160 : ℝ) =
      -(Real.pi * Real.exp (277 / 160 : ℝ) - (173 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (173 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (173 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1384_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65886930959425337 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1384_endpointUpper :
    hpThetaJensenKernelEndpointUpper (173 / 200 : ℝ) (277 / 320 : ℝ) ≤ (717647 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (277 / 160 : ℝ)) (35485606965962517 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (277 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1384_product_upper
  have hD : (322110684794041009 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (173 / 100 : ℝ) - (277 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1384_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1384_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (173 / 100 : ℝ) - (277 / 640 : ℝ)) ≤
      (1 / (322110684794041009 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (322110684794041009 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((277 / 640 : ℝ) - Real.pi * Real.exp (173 / 100 : ℝ)) ≤
      (2 / (322110684794041009 / 10000000000 : ℝ) : ℝ) := by
    rw [show (277 / 640 : ℝ) - Real.pi * Real.exp (173 / 100 : ℝ) =
      -(Real.pi * Real.exp (173 / 100 : ℝ) - (277 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35485606965962517 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (35485606965962517 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1384_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (173 / 200 : ℝ) (277 / 320 : ℝ)) :
    (698019 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (717647 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1384_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1384_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1385_leftExp :
    (28238545671 / 5000000000 : ℝ) ≤ Real.exp (277 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (277 / 160 : ℝ) (1055591805253 / 1000000000000 : ℝ)
    (28238545671 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1385_rightExp :
    Real.exp (693 / 400 : ℝ) ≤ (14136932963 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (693 / 400 : ℝ) (211126608023 / 200000000000 : ℝ)
    (14136932963 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1385_denomUpper :
    Real.exp (43330458388030059 / 2500000000000000 : ℝ) ≤ (336722076150970733 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (43330458388030059 / 2500000000000000 : ℝ) (1718807488711
    / 1000000000000 : ℝ) (336722076150970733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1385_denomLower :
    (65845392551666031 / 2000000000 : ℝ) ≤ Real.exp (10818545521456029 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10818545521456029 / 625000000000000 : ℝ) (858799406131 /
    500000000000 : ℝ) (65845392551666031 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1385_product_lower :
    (11089248646456029 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (277 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1385_leftExp
    (by norm_num : (0 : ℝ) ≤ (28238545671 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1385_product_upper :
    Real.pi * Real.exp (693 / 400 : ℝ) ≤ (44412489638030059 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1385_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1385_endpointLower :
    (684701 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (277 / 320 : ℝ) (693 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11089248646456029 / 625000000000000 : ℝ) (Real.pi * Real.exp (277 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1385_product_lower
  have hD : Real.exp (Real.pi * Real.exp (693 / 400 : ℝ) - (277 / 640 : ℝ)) ≤
      (336722076150970733 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1385_denomUpper
    linarith [hpThetaJensenCell1385_product_upper]
  have hi : (1 / (336722076150970733 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (693 / 400 : ℝ) - (277 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (336722076150970733 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (336722076150970733 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((277 / 640 : ℝ) - Real.pi * Real.exp (693 / 400 : ℝ)) := by
    rw [show (277 / 640 : ℝ) - Real.pi * Real.exp (693 / 400 : ℝ) =
      -(Real.pi * Real.exp (693 / 400 : ℝ) - (277 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (277 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (277 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1385_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (336722076150970733 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1385_endpointUpper :
    hpThetaJensenKernelEndpointUpper (277 / 320 : ℝ) (693 / 800 : ℝ) ≤ (703973 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (693 / 400 : ℝ)) (44412489638030059 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (693 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1385_product_upper
  have hD : (65845392551666031 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (277 / 160 : ℝ) - (693 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1385_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1385_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (277 / 160 : ℝ) - (693 / 1600 : ℝ)) ≤
      (1 / (65845392551666031 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (65845392551666031 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((693 / 1600 : ℝ) - Real.pi * Real.exp (277 / 160 : ℝ)) ≤
      (2 / (65845392551666031 / 2000000000 : ℝ) : ℝ) := by
    rw [show (693 / 1600 : ℝ) - Real.pi * Real.exp (277 / 160 : ℝ) =
      -(Real.pi * Real.exp (277 / 160 : ℝ) - (693 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44412489638030059 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (44412489638030059 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1385_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (277 / 320 : ℝ) (693 / 800 : ℝ)) :
    (684701 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (703973 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1385_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1385_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1386_leftExp :
    (56547731849 / 10000000000 : ℝ) ≤ Real.exp (693 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (693 / 400 : ℝ) (527816520057 / 500000000000 : ℝ)
    (56547731849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1386_rightExp :
    Real.exp (1387 / 800 : ℝ) ≤ (56618460713 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1387 / 800 : ℝ) (527837138293 / 500000000000 : ℝ)
    (56618460713 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1386_denomUpper :
    Real.exp (173540909846735809 / 10000000000000000 : ℝ) ≤ (86045063963909173 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (173540909846735809 / 10000000000000000 : ℝ)
    (429996152569 / 250000000000 : ℝ) (86045063963909173 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1386_denomLower :
    (336509787383622461 / 10000000000 : ℝ) ≤ Real.exp (21664440874370451 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (21664440874370451 / 1250000000000000 : ℝ) (4296934037 /
    2500000000 : ℝ) (336509787383622461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1386_product_lower :
    (22206237749370451 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (693 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1386_leftExp
    (by norm_num : (0 : ℝ) ≤ (56547731849 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1386_product_upper :
    Real.pi * Real.exp (1387 / 800 : ℝ) ≤ (177872159846735809 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1386_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1386_endpointLower :
    (335809 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (693 / 800 : ℝ) (1387 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22206237749370451 / 1250000000000000 : ℝ) (Real.pi * Real.exp (693 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1386_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1387 / 800 : ℝ) - (693 / 1600 : ℝ)) ≤
      (86045063963909173 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1386_denomUpper
    linarith [hpThetaJensenCell1386_product_upper]
  have hi : (1 / (86045063963909173 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1387 / 800 : ℝ) - (693 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (86045063963909173 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (86045063963909173 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((693 / 1600 : ℝ) - Real.pi * Real.exp (1387 / 800 : ℝ)) := by
    rw [show (693 / 1600 : ℝ) - Real.pi * Real.exp (1387 / 800 : ℝ) =
      -(Real.pi * Real.exp (1387 / 800 : ℝ) - (693 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (693 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (693 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1386_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (86045063963909173 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1386_endpointUpper :
    hpThetaJensenKernelEndpointUpper (693 / 800 : ℝ) (1387 / 1600 : ℝ) ≤ (690541 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1387 / 800 : ℝ)) (177872159846735809 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1387 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1386_product_upper
  have hD : (336509787383622461 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (693 / 400 : ℝ) - (1387 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1386_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1386_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (693 / 400 : ℝ) - (1387 / 3200 : ℝ)) ≤
      (1 / (336509787383622461 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (336509787383622461 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1387 / 3200 : ℝ) - Real.pi * Real.exp (693 / 400 : ℝ)) ≤
      (2 / (336509787383622461 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1387 / 3200 : ℝ) - Real.pi * Real.exp (693 / 400 : ℝ) =
      -(Real.pi * Real.exp (693 / 400 : ℝ) - (1387 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (177872159846735809 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (177872159846735809 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1386_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (693 / 800 : ℝ) (1387 / 1600 : ℝ)) :
    (335809 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (690541 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1386_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1386_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1387_leftExp :
    (5661846071 / 1000000000 : ℝ) ≤ Real.exp (1387 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1387 / 800 : ℝ) (211134855317 / 200000000000 : ℝ)
    (5661846071 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1387_rightExp :
    Real.exp (347 / 200 : ℝ) ≤ (56689278039 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (347 / 200 : ℝ) (1055715514667 / 1000000000000 : ℝ)
    (56689278039 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1387_denomUpper :
    Real.exp (173760264062376127 / 10000000000000000 : ℝ) ≤ (351813406993167613 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (173760264062376127 / 10000000000000000 : ℝ)
    (860582016413 / 500000000000 : ℝ) (351813406993167613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1387_denomLower :
    (343963262592012257 / 10000000000 : ℝ) ≤ Real.exp (2169182540235629 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2169182540235629 / 125000000000000 : ℝ) (859975356393 /
    500000000000 : ℝ) (343963262592012257 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1387_product_lower :
    (2223401290235629 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1387 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1387_leftExp
    (by norm_num : (0 : ℝ) ≤ (5661846071 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1387_product_upper :
    Real.pi * Real.exp (347 / 200 : ℝ) ≤ (178094639062376127 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1387_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1387_endpointLower :
    (658767 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1387 / 1600 : ℝ) (347 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2223401290235629 / 125000000000000 : ℝ) (Real.pi * Real.exp (1387 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1387_product_lower
  have hD : Real.exp (Real.pi * Real.exp (347 / 200 : ℝ) - (1387 / 3200 : ℝ)) ≤
      (351813406993167613 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1387_denomUpper
    linarith [hpThetaJensenCell1387_product_upper]
  have hi : (1 / (351813406993167613 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (347 / 200 : ℝ) - (1387 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (351813406993167613 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (351813406993167613 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1387 / 3200 : ℝ) - Real.pi * Real.exp (347 / 200 : ℝ)) := by
    rw [show (1387 / 3200 : ℝ) - Real.pi * Real.exp (347 / 200 : ℝ) =
      -(Real.pi * Real.exp (347 / 200 : ℝ) - (1387 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1387 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1387 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1387_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (351813406993167613 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1387_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1387 / 1600 : ℝ) (347 / 400 : ℝ) ≤ (677347 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (347 / 200 : ℝ)) (178094639062376127 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (347 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1387_product_upper
  have hD : (343963262592012257 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1387 / 800 : ℝ) - (347 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1387_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1387_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1387 / 800 : ℝ) - (347 / 800 : ℝ)) ≤
      (1 / (343963262592012257 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (343963262592012257 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((347 / 800 : ℝ) - Real.pi * Real.exp (1387 / 800 : ℝ)) ≤
      (2 / (343963262592012257 / 10000000000 : ℝ) : ℝ) := by
    rw [show (347 / 800 : ℝ) - Real.pi * Real.exp (1387 / 800 : ℝ) =
      -(Real.pi * Real.exp (1387 / 800 : ℝ) - (347 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (178094639062376127 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (178094639062376127 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1387_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1387 / 1600 : ℝ) (347 / 400 : ℝ)) :
    (658767 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (677347 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1387_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1387_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1388_leftExp :
    (14172319509 / 2500000000 : ℝ) ≤ Real.exp (347 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (347 / 200 : ℝ) (527857757333 / 500000000000 : ℝ)
    (14172319509 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1388_rightExp :
    Real.exp (1389 / 800 : ℝ) ≤ (7095022993 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1389 / 800 : ℝ) (26393918859 / 25000000000 : ℝ)
    (7095022993 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1388_denomUpper :
    Real.exp (21747487069647849 / 1250000000000000 : ℝ) ≤ (71925170382865593 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (21747487069647849 / 1250000000000000 : ℝ) (430586440479
    / 250000000000 : ℝ) (71925170382865593 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1388_denomLower :
    (4394894985155571 / 125000000 : ℝ) ≤ Real.exp (5429811167614791 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5429811167614791 / 312500000000000 : ℝ) (1721130111711 /
    1000000000000 : ℝ) (4394894985155571 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1388_product_lower :
    (5565455698864791 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (347 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1388_leftExp
    (by norm_num : (0 : ℝ) ≤ (14172319509 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1388_product_upper :
    Real.pi * Real.exp (1389 / 800 : ℝ) ≤ (22289674569647849 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1388_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1388_endpointLower :
    (631 / 9765625 : ℝ) ≤ hpThetaTraceEndpointLower (347 / 400 : ℝ) (1389 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5565455698864791 / 312500000000000 : ℝ) (Real.pi * Real.exp (347 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1388_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1389 / 800 : ℝ) - (347 / 800 : ℝ)) ≤
      (71925170382865593 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1388_denomUpper
    linarith [hpThetaJensenCell1388_product_upper]
  have hi : (1 / (71925170382865593 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1389 / 800 : ℝ) - (347 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71925170382865593 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71925170382865593 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((347 / 800 : ℝ) - Real.pi * Real.exp (1389 / 800 : ℝ)) := by
    rw [show (347 / 800 : ℝ) - Real.pi * Real.exp (1389 / 800 : ℝ) =
      -(Real.pi * Real.exp (1389 / 800 : ℝ) - (347 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (347 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (347 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1388_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71925170382865593 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1388_endpointUpper :
    hpThetaJensenKernelEndpointUpper (347 / 400 : ℝ) (1389 / 1600 : ℝ) ≤ (332193 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1389 / 800 : ℝ)) (22289674569647849 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1389 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1388_product_upper
  have hD : (4394894985155571 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (347 / 200 : ℝ) - (1389 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1388_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1388_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (347 / 200 : ℝ) - (1389 / 3200 : ℝ)) ≤
      (1 / (4394894985155571 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4394894985155571 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1389 / 3200 : ℝ) - Real.pi * Real.exp (347 / 200 : ℝ)) ≤
      (2 / (4394894985155571 / 125000000 : ℝ) : ℝ) := by
    rw [show (1389 / 3200 : ℝ) - Real.pi * Real.exp (347 / 200 : ℝ) =
      -(Real.pi * Real.exp (347 / 200 : ℝ) - (1389 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22289674569647849 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (22289674569647849 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1388_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (347 / 400 : ℝ) (1389 / 1600 : ℝ)) :
    (631 / 9765625 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (332193 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1388_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1388_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1389_leftExp :
    (56760183941 / 10000000000 : ℝ) ≤ Real.exp (1389 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1389 / 800 : ℝ) (1055756754359 / 1000000000000 : ℝ)
    (56760183941 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1389_rightExp :
    Real.exp (139 / 80 : ℝ) ≤ (7103897317 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (139 / 80 : ℝ) (65987374729 / 62500000000 : ℝ)
    (7103897317 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1389_denomUpper :
    Real.exp (21774975958805981 / 1250000000000000 : ℝ) ≤ (367622024163454913 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (21774975958805981 / 1250000000000000 : ℝ) (430882450753
    / 250000000000 : ℝ) (367622024163454913 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1389_denomLower :
    (35939911566083411 / 1000000000 : ℝ) ≤ Real.exp (21746698723446759 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (21746698723446759 / 1250000000000000 : ℝ) (1722311817129
    / 1000000000000 : ℝ) (35939911566083411 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1389_product_lower :
    (22289667473446759 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1389 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1389_leftExp
    (by norm_num : (0 : ℝ) ≤ (56760183941 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1389_product_upper :
    Real.pi * Real.exp (139 / 80 : ℝ) ≤ (22317554083805981 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1389_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1389_endpointLower :
    (39609 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1389 / 1600 : ℝ) (139 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22289667473446759 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1389 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1389_product_lower
  have hD : Real.exp (Real.pi * Real.exp (139 / 80 : ℝ) - (1389 / 3200 : ℝ)) ≤
      (367622024163454913 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1389_denomUpper
    linarith [hpThetaJensenCell1389_product_upper]
  have hi : (1 / (367622024163454913 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (139 / 80 : ℝ) - (1389 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (367622024163454913 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (367622024163454913 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1389 / 3200 : ℝ) - Real.pi * Real.exp (139 / 80 : ℝ)) := by
    rw [show (1389 / 3200 : ℝ) - Real.pi * Real.exp (139 / 80 : ℝ) =
      -(Real.pi * Real.exp (139 / 80 : ℝ) - (1389 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1389 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1389 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1389_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (367622024163454913 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1389_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1389 / 1600 : ℝ) (139 / 160 : ℝ) ≤ (325827 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (139 / 80 : ℝ)) (22317554083805981 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (139 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1389_product_upper
  have hD : (35939911566083411 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1389 / 800 : ℝ) - (139 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1389_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1389_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1389 / 800 : ℝ) - (139 / 320 : ℝ)) ≤
      (1 / (35939911566083411 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35939911566083411 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((139 / 320 : ℝ) - Real.pi * Real.exp (1389 / 800 : ℝ)) ≤
      (2 / (35939911566083411 / 1000000000 : ℝ) : ℝ) := by
    rw [show (139 / 320 : ℝ) - Real.pi * Real.exp (1389 / 800 : ℝ) =
      -(Real.pi * Real.exp (1389 / 800 : ℝ) - (139 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22317554083805981 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (22317554083805981 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1389_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1389 / 1600 : ℝ) (139 / 160 : ℝ)) :
    (39609 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (325827 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1389_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1389_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1390_leftExp :
    (28415589267 / 5000000000 : ℝ) ≤ Real.exp (139 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (139 / 80 : ℝ) (1055797995663 / 1000000000000 : ℝ)
    (28415589267 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1390_rightExp :
    Real.exp (1391 / 800 : ℝ) ≤ (7112782741 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1391 / 800 : ℝ) (1055839238579 / 1000000000000 : ℝ)
    (7112782741 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1390_denomUpper :
    Real.exp (21802499719646413 / 1250000000000000 : ℝ) ≤ (187903236375462137 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (21802499719646413 / 1250000000000000 : ℝ) (1724716161681
    / 1000000000000 : ℝ) (187903236375462137 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1390_denomLower :
    (367390244012333717 / 10000000000 : ℝ) ≤ Real.exp (10887093802061633 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10887093802061633 / 625000000000000 : ℝ) (68939833381 /
    40000000000 : ℝ) (367390244012333717 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1390_product_lower :
    (11158773489561633 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (139 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1390_leftExp
    (by norm_num : (0 : ℝ) ≤ (28415589267 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1390_product_upper :
    Real.pi * Real.exp (1391 / 800 : ℝ) ≤ (22345468469646413 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1390_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1390_endpointLower :
    (124313 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (139 / 160 : ℝ) (1391 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11158773489561633 / 625000000000000 : ℝ) (Real.pi * Real.exp (139 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1390_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1391 / 800 : ℝ) - (139 / 320 : ℝ)) ≤
      (187903236375462137 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1390_denomUpper
    linarith [hpThetaJensenCell1390_product_upper]
  have hi : (1 / (187903236375462137 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1391 / 800 : ℝ) - (139 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (187903236375462137 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (187903236375462137 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((139 / 320 : ℝ) - Real.pi * Real.exp (1391 / 800 : ℝ)) := by
    rw [show (139 / 320 : ℝ) - Real.pi * Real.exp (1391 / 800 : ℝ) =
      -(Real.pi * Real.exp (1391 / 800 : ℝ) - (139 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (139 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (139 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1390_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (187903236375462137 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1390_endpointUpper :
    hpThetaJensenKernelEndpointUpper (139 / 160 : ℝ) (1391 / 1600 : ℝ) ≤ (639149 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1391 / 800 : ℝ)) (22345468469646413 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1391 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1390_product_upper
  have hD : (367390244012333717 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (139 / 80 : ℝ) - (1391 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1390_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1390_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (139 / 80 : ℝ) - (1391 / 3200 : ℝ)) ≤
      (1 / (367390244012333717 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (367390244012333717 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1391 / 3200 : ℝ) - Real.pi * Real.exp (139 / 80 : ℝ)) ≤
      (2 / (367390244012333717 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1391 / 3200 : ℝ) - Real.pi * Real.exp (139 / 80 : ℝ) =
      -(Real.pi * Real.exp (139 / 80 : ℝ) - (1391 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22345468469646413 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (22345468469646413 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1390_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (139 / 160 : ℝ) (1391 / 1600 : ℝ)) :
    (124313 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (639149 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1390_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1390_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1391_leftExp :
    (2276090477 / 400000000 : ℝ) ≤ Real.exp (1391 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1391 / 800 : ℝ) (527919619289 / 500000000000 : ℝ)
    (2276090477 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1391_rightExp :
    Real.exp (87 / 50 : ℝ) ≤ (56973434227 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87 / 50 : ℝ) (32996265097 / 31250000000 : ℝ)
    (56973434227 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1391_denomUpper :
    Real.exp (174640467153503611 / 10000000000000000 : ℝ) ≤ (38418386396306257 / 1000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (174640467153503611 / 10000000000000000 : ℝ) (8629524217
    / 5000000000 : ℝ) (38418386396306257 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1391_denomLower :
    (187784764818878751 / 5000000000 : ℝ) ≤ Real.exp (872068454227423 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (872068454227423 / 50000000000000 : ℝ) (431170542353 /
    250000000000 : ℝ) (187784764818878751 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1391_product_lower :
    (893818454227423 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1391 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1391_leftExp
    (by norm_num : (0 : ℝ) ≤ (2276090477 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1391_product_upper :
    Real.pi * Real.exp (87 / 50 : ℝ) ≤ (178987342153503611 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1391_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1391_endpointLower :
    (609603 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1391 / 1600 : ℝ) (87 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (893818454227423 / 50000000000000 : ℝ) (Real.pi * Real.exp (1391 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1391_product_lower
  have hD : Real.exp (Real.pi * Real.exp (87 / 50 : ℝ) - (1391 / 3200 : ℝ)) ≤
      (38418386396306257 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1391_denomUpper
    linarith [hpThetaJensenCell1391_product_upper]
  have hi : (1 / (38418386396306257 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (87 / 50 : ℝ) - (1391 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38418386396306257 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38418386396306257 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1391 / 3200 : ℝ) - Real.pi * Real.exp (87 / 50 : ℝ)) := by
    rw [show (1391 / 3200 : ℝ) - Real.pi * Real.exp (87 / 50 : ℝ) =
      -(Real.pi * Real.exp (87 / 50 : ℝ) - (1391 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1391 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1391 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1391_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38418386396306257 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1391_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1391 / 1600 : ℝ) (87 / 100 : ℝ) ≤ (313433 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (87 / 50 : ℝ)) (178987342153503611 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (87 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1391_product_upper
  have hD : (187784764818878751 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1391 / 800 : ℝ) - (87 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1391_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1391_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1391 / 800 : ℝ) - (87 / 200 : ℝ)) ≤
      (1 / (187784764818878751 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (187784764818878751 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((87 / 200 : ℝ) - Real.pi * Real.exp (1391 / 800 : ℝ)) ≤
      (2 / (187784764818878751 / 5000000000 : ℝ) : ℝ) := by
    rw [show (87 / 200 : ℝ) - Real.pi * Real.exp (1391 / 800 : ℝ) =
      -(Real.pi * Real.exp (1391 / 800 : ℝ) - (87 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (178987342153503611 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (178987342153503611 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1391_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1391 / 1600 : ℝ) (87 / 100 : ℝ)) :
    (609603 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (313433 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1391_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1391_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1392_leftExp :
    (2278937369 / 400000000 : ℝ) ≤ Real.exp (87 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87 / 50 : ℝ) (1055880483103 / 1000000000000 : ℝ)
    (2278937369 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1392_rightExp :
    Real.exp (1393 / 800 : ℝ) ≤ (57044695549 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1393 / 800 : ℝ) (1055921729241 / 1000000000000 : ℝ)
    (57044695549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1392_denomUpper :
    Real.exp (174861216223869557 / 10000000000000000 : ℝ) ≤ (392758986340261333 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (174861216223869557 / 10000000000000000 : ℝ)
    (431773963453 / 250000000000 : ℝ) (392758986340261333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1392_denomLower :
    (383941636353336591 / 10000000000 : ℝ) ≤ Real.exp (873170800868931 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (873170800868931 / 50000000000000 : ℝ) (215733853417 /
    125000000000 : ℝ) (383941636353336591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1392_product_lower :
    (894936425868931 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (87 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1392_leftExp
    (by norm_num : (0 : ℝ) ≤ (2278937369 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1392_product_upper :
    Real.pi * Real.exp (1393 / 800 : ℝ) ≤ (179211216223869557 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1392_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1392_endpointLower :
    (119571 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 100 : ℝ) (1393 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (894936425868931 / 50000000000000 : ℝ) (Real.pi * Real.exp (87 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1392_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1393 / 800 : ℝ) - (87 / 200 : ℝ)) ≤
      (392758986340261333 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1392_denomUpper
    linarith [hpThetaJensenCell1392_product_upper]
  have hi : (1 / (392758986340261333 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1393 / 800 : ℝ) - (87 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (392758986340261333 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (392758986340261333 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((87 / 200 : ℝ) - Real.pi * Real.exp (1393 / 800 : ℝ)) := by
    rw [show (87 / 200 : ℝ) - Real.pi * Real.exp (1393 / 800 : ℝ) =
      -(Real.pi * Real.exp (1393 / 800 : ℝ) - (87 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (87 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (87 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1392_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (392758986340261333 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1392_endpointUpper :
    hpThetaJensenKernelEndpointUpper (87 / 100 : ℝ) (1393 / 1600 : ℝ) ≤ (307401 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1393 / 800 : ℝ)) (179211216223869557 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1393 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1392_product_upper
  have hD : (383941636353336591 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (87 / 50 : ℝ) - (1393 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1392_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1392_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (87 / 50 : ℝ) - (1393 / 3200 : ℝ)) ≤
      (1 / (383941636353336591 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (383941636353336591 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1393 / 3200 : ℝ) - Real.pi * Real.exp (87 / 50 : ℝ)) ≤
      (2 / (383941636353336591 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1393 / 3200 : ℝ) - Real.pi * Real.exp (87 / 50 : ℝ) =
      -(Real.pi * Real.exp (87 / 50 : ℝ) - (1393 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (179211216223869557 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (179211216223869557 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1392_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (87 / 100 : ℝ) (1393 / 1600 : ℝ)) :
    (119571 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (307401 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1392_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1392_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1393_leftExp :
    (57044695547 / 10000000000 : ℝ) ≤ Real.exp (1393 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1393 / 800 : ℝ) (26398043231 / 25000000000 : ℝ)
    (57044695547 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1393_rightExp :
    Real.exp (697 / 400 : ℝ) ≤ (11423209201 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (697 / 400 : ℝ) (105596297699 / 100000000000 : ℝ)
    (11423209201 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1393_denomUpper :
    Real.exp (35016449063397193 / 2000000000000000 : ℝ) ≤ (50192094040454791 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (35016449063397193 / 2000000000000000 : ℝ) (172828919849
    / 100000000000 : ℝ) (50192094040454791 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1393_denomLower :
    (196255674660629143 / 5000000000 : ℝ) ≤ Real.exp (21856863646611353 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (21856863646611353 / 1250000000000000 : ℝ) (1727061813889
    / 1000000000000 : ℝ) (196255674660629143 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1393_product_lower :
    (22401394896611353 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1393 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1393_leftExp
    (by norm_num : (0 : ℝ) ≤ (57044695547 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1393_product_upper :
    Real.pi * Real.exp (697 / 400 : ℝ) ≤ (35887074063397193 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1393_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1393_endpointLower :
    (146579 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1393 / 1600 : ℝ) (697 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22401394896611353 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1393 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1393_product_lower
  have hD : Real.exp (Real.pi * Real.exp (697 / 400 : ℝ) - (1393 / 3200 : ℝ)) ≤
      (50192094040454791 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1393_denomUpper
    linarith [hpThetaJensenCell1393_product_upper]
  have hi : (1 / (50192094040454791 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (697 / 400 : ℝ) - (1393 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (50192094040454791 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (50192094040454791 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1393 / 3200 : ℝ) - Real.pi * Real.exp (697 / 400 : ℝ)) := by
    rw [show (1393 / 3200 : ℝ) - Real.pi * Real.exp (697 / 400 : ℝ) =
      -(Real.pi * Real.exp (697 / 400 : ℝ) - (1393 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1393 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1393 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1393_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (50192094040454791 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1393_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1393 / 1600 : ℝ) (697 / 800 : ℝ) ≤ (602953 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (697 / 400 : ℝ)) (35887074063397193 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (697 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1393_product_upper
  have hD : (196255674660629143 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1393 / 800 : ℝ) - (697 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1393_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1393_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1393 / 800 : ℝ) - (697 / 1600 : ℝ)) ≤
      (1 / (196255674660629143 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (196255674660629143 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((697 / 1600 : ℝ) - Real.pi * Real.exp (1393 / 800 : ℝ)) ≤
      (2 / (196255674660629143 / 5000000000 : ℝ) : ℝ) := by
    rw [show (697 / 1600 : ℝ) - Real.pi * Real.exp (1393 / 800 : ℝ) =
      -(Real.pi * Real.exp (1393 / 800 : ℝ) - (697 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35887074063397193 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (35887074063397193 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1393_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1393 / 1600 : ℝ) (697 / 800 : ℝ)) :
    (146579 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (602953 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1393_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1393_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1394_leftExp :
    (28558023001 / 5000000000 : ℝ) ≤ Real.exp (697 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (697 / 400 : ℝ) (1055962976989 / 1000000000000 : ℝ)
    (28558023001 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1394_rightExp :
    Real.exp (279 / 160 : ℝ) ≤ (28593742851 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (279 / 160 : ℝ) (1056004226349 / 1000000000000 : ℝ)
    (28593742851 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1394_denomUpper :
    Real.exp (87651777384501643 / 5000000000000000 : ℝ) ≤ (82104440337669199 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (87651777384501643 / 5000000000000000 : ℝ) (1729484882953
    / 1000000000000 : ℝ) (82104440337669199 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1394_denomLower :
    (401283577881193039 / 10000000000 : ℝ) ≤ Real.exp (10942246136969699 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10942246136969699 / 625000000000000 : ℝ) (345651026929 /
    200000000000 : ℝ) (401283577881193039 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1394_product_lower :
    (11214707074469699 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (697 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1394_leftExp
    (by norm_num : (0 : ℝ) ≤ (28558023001 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1394_product_upper :
    Real.pi * Real.exp (279 / 160 : ℝ) ≤ (89829902384501643 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1394_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1394_endpointLower :
    (71873 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (697 / 800 : ℝ) (279 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11214707074469699 / 625000000000000 : ℝ) (Real.pi * Real.exp (697 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1394_product_lower
  have hD : Real.exp (Real.pi * Real.exp (279 / 160 : ℝ) - (697 / 1600 : ℝ)) ≤
      (82104440337669199 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1394_denomUpper
    linarith [hpThetaJensenCell1394_product_upper]
  have hi : (1 / (82104440337669199 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (279 / 160 : ℝ) - (697 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (82104440337669199 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (82104440337669199 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((697 / 1600 : ℝ) - Real.pi * Real.exp (279 / 160 : ℝ)) := by
    rw [show (697 / 1600 : ℝ) - Real.pi * Real.exp (279 / 160 : ℝ) =
      -(Real.pi * Real.exp (279 / 160 : ℝ) - (697 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (697 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (697 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1394_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (82104440337669199 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1394_endpointUpper :
    hpThetaJensenKernelEndpointUpper (697 / 800 : ℝ) (279 / 320 : ℝ) ≤ (147829 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (279 / 160 : ℝ)) (89829902384501643 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (279 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1394_product_upper
  have hD : (401283577881193039 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (697 / 400 : ℝ) - (279 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1394_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1394_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (697 / 400 : ℝ) - (279 / 640 : ℝ)) ≤
      (1 / (401283577881193039 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (401283577881193039 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((279 / 640 : ℝ) - Real.pi * Real.exp (697 / 400 : ℝ)) ≤
      (2 / (401283577881193039 / 10000000000 : ℝ) : ℝ) := by
    rw [show (279 / 640 : ℝ) - Real.pi * Real.exp (697 / 400 : ℝ) =
      -(Real.pi * Real.exp (697 / 400 : ℝ) - (279 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (89829902384501643 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (89829902384501643 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1394_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (697 / 800 : ℝ) (279 / 320 : ℝ)) :
    (71873 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (147829 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1394_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1394_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1395_leftExp :
    (57187485699 / 10000000000 : ℝ) ≤ Real.exp (279 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (279 / 160 : ℝ) (264001056587 / 250000000000 : ℝ)
    (57187485699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1395_rightExp :
    Real.exp (349 / 200 : ℝ) ≤ (14314753689 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (349 / 200 : ℝ) (26401136933 / 25000000000 : ℝ)
    (14314753689 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1395_denomUpper :
    Real.exp (43881286236086577 / 2500000000000000 : ℝ) ≤ (83944101336418463 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (43881286236086577 / 2500000000000000 : ℝ) (216335364111
    / 125000000000 : ℝ) (83944101336418463 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1395_denomLower :
    (205131679434833481 / 5000000000 : ℝ) ≤ Real.exp (21912155946511601 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (21912155946511601 / 1250000000000000 : ℝ) (432362698789
    / 250000000000 : ℝ) (205131679434833481 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1395_product_lower :
    (22457468446511601 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (279 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1395_leftExp
    (by norm_num : (0 : ℝ) ≤ (57187485699 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1395_product_upper :
    Real.pi * Real.exp (349 / 200 : ℝ) ≤ (44971129986086577 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1395_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1395_endpointLower :
    (112771 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (279 / 320 : ℝ) (349 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22457468446511601 / 1250000000000000 : ℝ) (Real.pi * Real.exp (279 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1395_product_lower
  have hD : Real.exp (Real.pi * Real.exp (349 / 200 : ℝ) - (279 / 640 : ℝ)) ≤
      (83944101336418463 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1395_denomUpper
    linarith [hpThetaJensenCell1395_product_upper]
  have hi : (1 / (83944101336418463 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (349 / 200 : ℝ) - (279 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (83944101336418463 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (83944101336418463 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((279 / 640 : ℝ) - Real.pi * Real.exp (349 / 200 : ℝ)) := by
    rw [show (279 / 640 : ℝ) - Real.pi * Real.exp (349 / 200 : ℝ) =
      -(Real.pi * Real.exp (349 / 200 : ℝ) - (279 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (279 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (279 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1395_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (83944101336418463 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1395_endpointUpper :
    hpThetaJensenKernelEndpointUpper (279 / 320 : ℝ) (349 / 400 : ℝ) ≤ (579887 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (349 / 200 : ℝ)) (44971129986086577 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (349 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1395_product_upper
  have hD : (205131679434833481 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (279 / 160 : ℝ) - (349 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1395_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1395_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (279 / 160 : ℝ) - (349 / 800 : ℝ)) ≤
      (1 / (205131679434833481 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (205131679434833481 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((349 / 800 : ℝ) - Real.pi * Real.exp (279 / 160 : ℝ)) ≤
      (2 / (205131679434833481 / 5000000000 : ℝ) : ℝ) := by
    rw [show (349 / 800 : ℝ) - Real.pi * Real.exp (279 / 160 : ℝ) =
      -(Real.pi * Real.exp (279 / 160 : ℝ) - (349 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44971129986086577 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (44971129986086577 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1395_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (279 / 320 : ℝ) (349 / 400 : ℝ)) :
    (112771 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (579887 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1395_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1395_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1396_leftExp :
    (57259014753 / 10000000000 : ℝ) ≤ Real.exp (349 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (349 / 200 : ℝ) (1056045477319 / 1000000000000 : ℝ)
    (57259014753 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1396_rightExp :
    Real.exp (1397 / 800 : ℝ) ≤ (14332658319 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1397 / 800 : ℝ) (528043364951 / 500000000000 : ℝ)
    (14332658319 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1396_denomUpper :
    Real.exp (43936754046362167 / 2500000000000000 : ℝ) ≤ (107284243383420061 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (43936754046362167 / 2500000000000000 : ℝ) (865941646937
    / 500000000000 : ℝ) (107284243383420061 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1396_denomLower :
    (419455861138019343 / 10000000000 : ℝ) ≤ Real.exp (21939854709488347 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (21939854709488347 / 1250000000000000 : ℝ) (1730648801091
    / 1000000000000 : ℝ) (419455861138019343 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1396_product_lower :
    (22485557834488347 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (349 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1396_leftExp
    (by norm_num : (0 : ℝ) ≤ (57259014753 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1396_product_upper :
    Real.pi * Real.exp (1397 / 800 : ℝ) ≤ (45027379046362167 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1396_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1396_endpointLower :
    (276463 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (349 / 400 : ℝ) (1397 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22485557834488347 / 1250000000000000 : ℝ) (Real.pi * Real.exp (349 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1396_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1397 / 800 : ℝ) - (349 / 800 : ℝ)) ≤
      (107284243383420061 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1396_denomUpper
    linarith [hpThetaJensenCell1396_product_upper]
  have hi : (1 / (107284243383420061 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1397 / 800 : ℝ) - (349 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (107284243383420061 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (107284243383420061 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((349 / 800 : ℝ) - Real.pi * Real.exp (1397 / 800 : ℝ)) := by
    rw [show (349 / 800 : ℝ) - Real.pi * Real.exp (1397 / 800 : ℝ) =
      -(Real.pi * Real.exp (1397 / 800 : ℝ) - (349 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (349 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (349 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1396_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (107284243383420061 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1396_endpointUpper :
    hpThetaJensenKernelEndpointUpper (349 / 400 : ℝ) (1397 / 1600 : ℝ) ≤ (568663 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1397 / 800 : ℝ)) (45027379046362167 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1397 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1396_product_upper
  have hD : (419455861138019343 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (349 / 200 : ℝ) - (1397 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1396_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1396_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (349 / 200 : ℝ) - (1397 / 3200 : ℝ)) ≤
      (1 / (419455861138019343 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (419455861138019343 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1397 / 3200 : ℝ) - Real.pi * Real.exp (349 / 200 : ℝ)) ≤
      (2 / (419455861138019343 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1397 / 3200 : ℝ) - Real.pi * Real.exp (349 / 200 : ℝ) =
      -(Real.pi * Real.exp (349 / 200 : ℝ) - (1397 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45027379046362167 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (45027379046362167 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1396_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (349 / 400 : ℝ) (1397 / 1600 : ℝ)) :
    (276463 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (568663 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1396_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1396_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1397_leftExp :
    (28665316637 / 5000000000 : ℝ) ≤ Real.exp (1397 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1397 / 800 : ℝ) (1056086729901 / 1000000000000 : ℝ)
    (28665316637 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1397_rightExp :
    Real.exp (699 / 400 : ℝ) ≤ (57402341377 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (699 / 400 : ℝ) (33003999503 / 31250000000 : ℝ)
    (57402341377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1397_denomUpper :
    Real.exp (175969168853593561 / 10000000000000000 : ℝ) ≤ (219388523926333757 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (175969168853593561 / 10000000000000000 : ℝ)
    (216635753951 / 125000000000 : ℝ) (219388523926333757 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1397_denomLower :
    (13402074615863519 / 312500000 : ℝ) ≤ Real.exp (10983794303033263 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10983794303033263 / 625000000000000 : ℝ) (1731849158047
    / 1000000000000 : ℝ) (13402074615863519 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1397_product_lower :
    (11256841178033263 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1397 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1397_leftExp
    (by norm_num : (0 : ℝ) ≤ (28665316637 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1397_product_upper :
    Real.pi * Real.exp (699 / 400 : ℝ) ≤ (180334793853593561 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1397_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1397_endpointLower :
    (542193 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1397 / 1600 : ℝ) (699 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11256841178033263 / 625000000000000 : ℝ) (Real.pi * Real.exp (1397 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1397_product_lower
  have hD : Real.exp (Real.pi * Real.exp (699 / 400 : ℝ) - (1397 / 3200 : ℝ)) ≤
      (219388523926333757 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1397_denomUpper
    linarith [hpThetaJensenCell1397_product_upper]
  have hi : (1 / (219388523926333757 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (699 / 400 : ℝ) - (1397 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (219388523926333757 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (219388523926333757 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1397 / 3200 : ℝ) - Real.pi * Real.exp (699 / 400 : ℝ)) := by
    rw [show (1397 / 3200 : ℝ) - Real.pi * Real.exp (699 / 400 : ℝ) =
      -(Real.pi * Real.exp (699 / 400 : ℝ) - (1397 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1397 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1397 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1397_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (219388523926333757 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1397_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1397 / 1600 : ℝ) (699 / 800 : ℝ) ≤ (557641 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (699 / 400 : ℝ)) (180334793853593561 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (699 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1397_product_upper
  have hD : (13402074615863519 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1397 / 800 : ℝ) - (699 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1397_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1397_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1397 / 800 : ℝ) - (699 / 1600 : ℝ)) ≤
      (1 / (13402074615863519 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13402074615863519 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((699 / 1600 : ℝ) - Real.pi * Real.exp (1397 / 800 : ℝ)) ≤
      (2 / (13402074615863519 / 312500000 : ℝ) : ℝ) := by
    rw [show (699 / 1600 : ℝ) - Real.pi * Real.exp (1397 / 800 : ℝ) =
      -(Real.pi * Real.exp (1397 / 800 : ℝ) - (699 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (180334793853593561 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (180334793853593561 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1397_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1397 / 1600 : ℝ) (699 / 800 : ℝ)) :
    (542193 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (557641 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1397_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1397_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1398_leftExp :
    (28701170687 / 5000000000 : ℝ) ≤ Real.exp (699 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (699 / 400 : ℝ) (211225596819 / 200000000000 : ℝ)
    (28701170687 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1398_rightExp :
    Real.exp (1399 / 800 : ℝ) ≤ (1796066849 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1399 / 800 : ℝ) (1056169239901 / 1000000000000 : ℝ)
    (1796066849 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1398_denomUpper :
    Real.exp (5505987602850457 / 312500000000000 : ℝ) ≤ (112161579197224333 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (5505987602850457 / 312500000000000 : ℝ) (1734291131699 /
    1000000000000 : ℝ) (112161579197224333 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1398_denomLower :
    (43850038033831661 / 1000000000 : ℝ) ≤ Real.exp (10997678840114213 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (10997678840114213 / 625000000000000 : ℝ) (1733051871669
    / 1000000000000 : ℝ) (43850038033831661 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1398_product_lower :
    (11270921027614213 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (699 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1398_leftExp
    (by norm_num : (0 : ℝ) ≤ (28701170687 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1398_product_upper :
    Real.pi * Real.exp (1399 / 800 : ℝ) ≤ (5642511040350457 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1398_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1398_endpointLower :
    (265827 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (699 / 800 : ℝ) (1399 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11270921027614213 / 625000000000000 : ℝ) (Real.pi * Real.exp (699 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1398_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1399 / 800 : ℝ) - (699 / 1600 : ℝ)) ≤
      (112161579197224333 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1398_denomUpper
    linarith [hpThetaJensenCell1398_product_upper]
  have hi : (1 / (112161579197224333 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1399 / 800 : ℝ) - (699 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (112161579197224333 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (112161579197224333 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((699 / 1600 : ℝ) - Real.pi * Real.exp (1399 / 800 : ℝ)) := by
    rw [show (699 / 1600 : ℝ) - Real.pi * Real.exp (1399 / 800 : ℝ) =
      -(Real.pi * Real.exp (1399 / 800 : ℝ) - (699 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (699 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (699 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1398_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (112161579197224333 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1398_endpointUpper :
    hpThetaJensenKernelEndpointUpper (699 / 800 : ℝ) (1399 / 1600 : ℝ) ≤ (534 / 9765625 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1399 / 800 : ℝ)) (5642511040350457 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1399 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1398_product_upper
  have hD : (43850038033831661 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (699 / 400 : ℝ) - (1399 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1398_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1398_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (699 / 400 : ℝ) - (1399 / 3200 : ℝ)) ≤
      (1 / (43850038033831661 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (43850038033831661 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1399 / 3200 : ℝ) - Real.pi * Real.exp (699 / 400 : ℝ)) ≤
      (2 / (43850038033831661 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1399 / 3200 : ℝ) - Real.pi * Real.exp (699 / 400 : ℝ) =
      -(Real.pi * Real.exp (699 / 400 : ℝ) - (1399 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5642511040350457 / 312500000000000 : ℝ) ^ 2 - 6 *
      (5642511040350457 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1398_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (699 / 800 : ℝ) (1399 / 1600 : ℝ)) :
    (265827 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (534 / 9765625 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1398_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1398_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1399_leftExp :
    (11494827833 / 2000000000 : ℝ) ≤ Real.exp (1399 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1399 / 800 : ℝ) (10561692399 / 10000000000 : ℝ)
    (11494827833 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1399_rightExp :
    Real.exp (7 / 4 : ℝ) ≤ (57546026761 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 4 : ℝ) (1056210497317 / 1000000000000 : ℝ)
    (57546026761 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1399_denomUpper :
    Real.exp (176414319850170273 / 10000000000000000 : ℝ) ≤ (229375257059358777 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (176414319850170273 / 10000000000000000 : ℝ)
    (1735498599821 / 1000000000000 : ℝ) (229375257059358777 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1399_denomLower :
    (448363423064946957 / 10000000000 : ℝ) ≤ Real.exp (4404632395191267 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4404632395191267 / 250000000000000 : ℝ) (867128473809 /
    500000000000 : ℝ) (448363423064946957 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1399_product_lower :
    (4514007395191267 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1399 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1399_leftExp
    (by norm_num : (0 : ℝ) ≤ (11494827833 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1399_product_upper :
    Real.pi * Real.exp (7 / 4 : ℝ) ≤ (180786194850170273 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1399_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1399_endpointLower :
    (65163 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1399 / 1600 : ℝ) (7 / 8 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4514007395191267 / 250000000000000 : ℝ) (Real.pi * Real.exp (1399 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1399_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 4 : ℝ) - (1399 / 3200 : ℝ)) ≤
      (229375257059358777 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1399_denomUpper
    linarith [hpThetaJensenCell1399_product_upper]
  have hi : (1 / (229375257059358777 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 4 : ℝ) - (1399 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (229375257059358777 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (229375257059358777 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1399 / 3200 : ℝ) - Real.pi * Real.exp (7 / 4 : ℝ)) := by
    rw [show (1399 / 3200 : ℝ) - Real.pi * Real.exp (7 / 4 : ℝ) =
      -(Real.pi * Real.exp (7 / 4 : ℝ) - (1399 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1399 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1399 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1399_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (229375257059358777 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1399_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1399 / 1600 : ℝ) (7 / 8 : ℝ) ≤ (536187 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 4 : ℝ)) (180786194850170273 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 8 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1399_product_upper
  have hD : (448363423064946957 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1399 / 800 : ℝ) - (7 / 16 : ℝ)) := by
    apply le_trans hpThetaJensenCell1399_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1399_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1399 / 800 : ℝ) - (7 / 16 : ℝ)) ≤
      (1 / (448363423064946957 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (448363423064946957 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 16 : ℝ) - Real.pi * Real.exp (1399 / 800 : ℝ)) ≤
      (2 / (448363423064946957 / 10000000000 : ℝ) : ℝ) := by
    rw [show (7 / 16 : ℝ) - Real.pi * Real.exp (1399 / 800 : ℝ) =
      -(Real.pi * Real.exp (1399 / 800 : ℝ) - (7 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (180786194850170273 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (180786194850170273 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1399_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1399 / 1600 : ℝ) (7 / 8 : ℝ)) :
    (65163 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (536187 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1399_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1399_endpointUpper

def hpThetaJensenCellsBatch069Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (188431 / 2500000000 : ℝ)
  | 1 => (29577 / 400000000 : ℝ)
  | 2 => (725377 / 10000000000 : ℝ)
  | 3 => (711577 / 10000000000 : ℝ)
  | 4 => (698019 / 10000000000 : ℝ)
  | 5 => (684701 / 10000000000 : ℝ)
  | 6 => (335809 / 5000000000 : ℝ)
  | 7 => (658767 / 10000000000 : ℝ)
  | 8 => (631 / 9765625 : ℝ)
  | 9 => (39609 / 625000000 : ℝ)
  | 10 => (124313 / 2000000000 : ℝ)
  | 11 => (609603 / 10000000000 : ℝ)
  | 12 => (119571 / 2000000000 : ℝ)
  | 13 => (146579 / 2500000000 : ℝ)
  | 14 => (71873 / 1250000000 : ℝ)
  | 15 => (112771 / 2000000000 : ℝ)
  | 16 => (276463 / 5000000000 : ℝ)
  | 17 => (542193 / 10000000000 : ℝ)
  | 18 => (265827 / 5000000000 : ℝ)
  | 19 => (65163 / 1250000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch069Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (48427 / 625000000 : ℝ)
  | 1 => (380077 / 5000000000 : ℝ)
  | 2 => (745733 / 10000000000 : ℝ)
  | 3 => (146313 / 2000000000 : ℝ)
  | 4 => (717647 / 10000000000 : ℝ)
  | 5 => (703973 / 10000000000 : ℝ)
  | 6 => (690541 / 10000000000 : ℝ)
  | 7 => (677347 / 10000000000 : ℝ)
  | 8 => (332193 / 5000000000 : ℝ)
  | 9 => (325827 / 5000000000 : ℝ)
  | 10 => (639149 / 10000000000 : ℝ)
  | 11 => (313433 / 5000000000 : ℝ)
  | 12 => (307401 / 5000000000 : ℝ)
  | 13 => (602953 / 10000000000 : ℝ)
  | 14 => (147829 / 2500000000 : ℝ)
  | 15 => (579887 / 10000000000 : ℝ)
  | 16 => (568663 / 10000000000 : ℝ)
  | 17 => (557641 / 10000000000 : ℝ)
  | 18 => (534 / 9765625 : ℝ)
  | 19 => (536187 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch069_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch069Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch069Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1380_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1381_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1382_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1383_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1384_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1385_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1386_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1387_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1388_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1389_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1390_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1391_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1392_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1393_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1394_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1395_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1396_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1397_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1398_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1399_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper] at h ⊢
    exact h

end HodgeProofHP
