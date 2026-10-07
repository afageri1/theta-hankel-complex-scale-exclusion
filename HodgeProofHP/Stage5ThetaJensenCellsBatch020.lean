import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell401_leftExp :
    (1031739663 / 625000000 : ℝ) ≤ Real.exp (401 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (401 / 800 : ℝ) (507893693503 / 500000000000 : ℝ)
    (1031739663 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell401_rightExp :
    Real.exp (201 / 400 : ℝ) ≤ (3305696461 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (201 / 400 : ℝ) (1015827066977 / 1000000000000 : ℝ)
    (3305696461 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell401_denomUpper :
    Real.exp (10134527862002373 / 2000000000000000 : ℝ) ≤ (396848526637 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10134527862002373 / 2000000000000000 : ℝ) (1171578515247
    / 1000000000000 : ℝ) (396848526637 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell401_denomLower :
    (1576635156267 / 10000000000 : ℝ) ≤ Real.exp (395348680795437 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (395348680795437 / 78125000000000 : ℝ) (1171329551363 /
    1000000000000 : ℝ) (1576635156267 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell401_product_lower :
    (405163133920437 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (401 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell401_leftExp
    (by norm_num : (0 : ℝ) ≤ (1031739663 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell401_product_upper :
    Real.pi * Real.exp (201 / 400 : ℝ) ≤ (10385152862002373 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell401_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell401_endpointLower :
    (1926818569 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (401 / 1600 : ℝ) (201 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (405163133920437 / 78125000000000 : ℝ) (Real.pi * Real.exp (401 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell401_product_lower
  have hD : Real.exp (Real.pi * Real.exp (201 / 400 : ℝ) - (401 / 3200 : ℝ)) ≤
      (396848526637 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell401_denomUpper
    linarith [hpThetaJensenCell401_product_upper]
  have hi : (1 / (396848526637 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (201 / 400 : ℝ) - (401 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (396848526637 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (396848526637 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((401 / 3200 : ℝ) - Real.pi * Real.exp (201 / 400 : ℝ)) := by
    rw [show (401 / 3200 : ℝ) - Real.pi * Real.exp (201 / 400 : ℝ) =
      -(Real.pi * Real.exp (201 / 400 : ℝ) - (401 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (401 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (401 / 800 : ℝ)) := by
    have h := hpThetaJensenCell401_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (396848526637 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell401_endpointUpper :
    hpThetaJensenKernelEndpointUpper (401 / 1600 : ℝ) (201 / 800 : ℝ) ≤ (9754688267 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (201 / 400 : ℝ)) (10385152862002373 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (201 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell401_product_upper
  have hD : (1576635156267 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (401 / 800 : ℝ) - (201 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell401_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell401_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (401 / 800 : ℝ) - (201 / 1600 : ℝ)) ≤
      (1 / (1576635156267 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1576635156267 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((201 / 1600 : ℝ) - Real.pi * Real.exp (401 / 800 : ℝ)) ≤
      (2 / (1576635156267 / 10000000000 : ℝ) : ℝ) := by
    rw [show (201 / 1600 : ℝ) - Real.pi * Real.exp (401 / 800 : ℝ) =
      -(Real.pi * Real.exp (401 / 800 : ℝ) - (201 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10385152862002373 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (10385152862002373 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell401_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (401 / 1600 : ℝ) (201 / 800 : ℝ)) :
    (1926818569 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9754688267 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell401_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell401_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell402_leftExp :
    (16141096 / 9765625 : ℝ) ≤ Real.exp (201 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (201 / 400 : ℝ) (31744595843 / 31250000000 : ℝ) (16141096
    / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell402_rightExp :
    Real.exp (403 / 800 : ℝ) ≤ (8274577913 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (403 / 800 : ℝ) (1015866748497 / 1000000000000 : ℝ)
    (8274577913 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell402_denomUpper :
    Real.exp (25367231049435409 / 5000000000000000 : ℝ) ≤ (24956847153 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25367231049435409 / 5000000000000000 : ℝ) (73237805103 /
    62500000000 : ℝ) (24956847153 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell402_denomLower :
    (317279934521 / 2000000000 : ℝ) ≤ Real.exp (98957759332789 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (98957759332789 / 19531250000000 : ℝ) (1171555572553 /
    1000000000000 : ℝ) (317279934521 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell402_product_lower :
    (792324032263 / 152587890625 : ℝ) ≤ Real.pi * Real.exp (201 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell402_leftExp
    (by norm_num : (0 : ℝ) ≤ (16141096 / 9765625 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell402_product_upper :
    Real.pi * Real.exp (403 / 800 : ℝ) ≤ (25995356049435409 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell402_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell402_endpointLower :
    (960356217 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (201 / 800 : ℝ) (403 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (792324032263 / 152587890625 : ℝ) (Real.pi * Real.exp (201 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell402_product_lower
  have hD : Real.exp (Real.pi * Real.exp (403 / 800 : ℝ) - (201 / 1600 : ℝ)) ≤
      (24956847153 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell402_denomUpper
    linarith [hpThetaJensenCell402_product_upper]
  have hi : (1 / (24956847153 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (403 / 800 : ℝ) - (201 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (24956847153 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (24956847153 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((201 / 1600 : ℝ) - Real.pi * Real.exp (403 / 800 : ℝ)) := by
    rw [show (201 / 1600 : ℝ) - Real.pi * Real.exp (403 / 800 : ℝ) =
      -(Real.pi * Real.exp (403 / 800 : ℝ) - (201 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (201 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (201 / 400 : ℝ)) := by
    have h := hpThetaJensenCell402_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (24956847153 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell402_endpointUpper :
    hpThetaJensenKernelEndpointUpper (201 / 800 : ℝ) (403 / 1600 : ℝ) ≤ (194476913 / 200000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (403 / 800 : ℝ)) (25995356049435409 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (403 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell402_product_upper
  have hD : (317279934521 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (201 / 400 : ℝ) - (403 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell402_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell402_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (201 / 400 : ℝ) - (403 / 3200 : ℝ)) ≤
      (1 / (317279934521 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (317279934521 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((403 / 3200 : ℝ) - Real.pi * Real.exp (201 / 400 : ℝ)) ≤
      (2 / (317279934521 / 2000000000 : ℝ) : ℝ) := by
    rw [show (403 / 3200 : ℝ) - Real.pi * Real.exp (201 / 400 : ℝ) =
      -(Real.pi * Real.exp (201 / 400 : ℝ) - (403 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25995356049435409 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (25995356049435409 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell402_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (201 / 800 : ℝ) (403 / 1600 : ℝ)) :
    (960356217 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (194476913 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell402_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell402_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell403_leftExp :
    (661966233 / 400000000 : ℝ) ≤ Real.exp (403 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (403 / 800 : ℝ) (63491671781 / 62500000000 : ℝ)
    (661966233 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell403_rightExp :
    Real.exp (101 / 200 : ℝ) ≤ (8284927603 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (101 / 200 : ℝ) (1015906431567 / 1000000000000 : ℝ)
    (8284927603 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell403_denomUpper :
    Real.exp (25398183063091579 / 5000000000000000 : ℝ) ≤ (1607156432819 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25398183063091579 / 5000000000000000 : ℝ) (117203158933
    / 100000000000 : ℝ) (1607156432819 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell403_denomLower :
    (1596237613619 / 10000000000 : ℝ) ≤ Real.exp (253640977732867 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (253640977732867 / 50000000000000 : ℝ) (234356386889 /
    200000000000 : ℝ) (1596237613619 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell403_product_lower :
    (259953477732867 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (403 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell403_leftExp
    (by norm_num : (0 : ℝ) ≤ (661966233 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell403_product_upper :
    Real.pi * Real.exp (101 / 200 : ℝ) ≤ (26027870563091579 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell403_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell403_endpointLower :
    (9573041931 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (403 / 1600 : ℝ) (101 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (259953477732867 / 50000000000000 : ℝ) (Real.pi * Real.exp (403 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell403_product_lower
  have hD : Real.exp (Real.pi * Real.exp (101 / 200 : ℝ) - (403 / 3200 : ℝ)) ≤
      (1607156432819 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell403_denomUpper
    linarith [hpThetaJensenCell403_product_upper]
  have hi : (1 / (1607156432819 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (101 / 200 : ℝ) - (403 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1607156432819 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1607156432819 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((403 / 3200 : ℝ) - Real.pi * Real.exp (101 / 200 : ℝ)) := by
    rw [show (403 / 3200 : ℝ) - Real.pi * Real.exp (101 / 200 : ℝ) =
      -(Real.pi * Real.exp (101 / 200 : ℝ) - (403 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (403 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (403 / 800 : ℝ)) := by
    have h := hpThetaJensenCell403_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1607156432819 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell403_endpointUpper :
    hpThetaJensenKernelEndpointUpper (403 / 1600 : ℝ) (101 / 400 : ℝ) ≤ (9693013281 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (101 / 200 : ℝ)) (26027870563091579 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (101 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell403_product_upper
  have hD : (1596237613619 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (403 / 800 : ℝ) - (101 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell403_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell403_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (403 / 800 : ℝ) - (101 / 800 : ℝ)) ≤
      (1 / (1596237613619 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1596237613619 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((101 / 800 : ℝ) - Real.pi * Real.exp (403 / 800 : ℝ)) ≤
      (2 / (1596237613619 / 10000000000 : ℝ) : ℝ) := by
    rw [show (101 / 800 : ℝ) - Real.pi * Real.exp (403 / 800 : ℝ) =
      -(Real.pi * Real.exp (403 / 800 : ℝ) - (101 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26027870563091579 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26027870563091579 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell403_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (403 / 1600 : ℝ) (101 / 400 : ℝ)) :
    (9573041931 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9693013281 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell403_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell403_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell404_leftExp :
    (4142463801 / 2500000000 : ℝ) ≤ Real.exp (101 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (101 / 200 : ℝ) (507953215783 / 500000000000 : ℝ)
    (4142463801 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell404_rightExp :
    Real.exp (81 / 160 : ℝ) ≤ (663623219 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81 / 160 : ℝ) (1015946116187 / 1000000000000 : ℝ)
    (663623219 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell404_denomUpper :
    Real.exp (2034334059447867 / 400000000000000 : ℝ) ≤ (101071836791 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2034334059447867 / 400000000000000 : ℝ) (1172258638819 /
    1000000000000 : ℝ) (101071836791 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell404_denomLower :
    (1606149611457 / 10000000000 : ℝ) ≤ Real.exp (1587190610938899 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1587190610938899 / 312500000000000 : ℝ) (1465010797 /
    1250000000 : ℝ) (1606149611457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell404_product_lower :
    (1626741392188899 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (101 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell404_leftExp
    (by norm_num : (0 : ℝ) ≤ (4142463801 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell404_product_upper :
    Real.pi * Real.exp (81 / 160 : ℝ) ≤ (2084834059447867 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell404_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell404_endpointLower :
    (381701303 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (101 / 400 : ℝ) (81 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1626741392188899 / 312500000000000 : ℝ) (Real.pi * Real.exp (101 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell404_product_lower
  have hD : Real.exp (Real.pi * Real.exp (81 / 160 : ℝ) - (101 / 800 : ℝ)) ≤
      (101071836791 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell404_denomUpper
    linarith [hpThetaJensenCell404_product_upper]
  have hi : (1 / (101071836791 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (81 / 160 : ℝ) - (101 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (101071836791 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (101071836791 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((101 / 800 : ℝ) - Real.pi * Real.exp (81 / 160 : ℝ)) := by
    rw [show (101 / 800 : ℝ) - Real.pi * Real.exp (81 / 160 : ℝ) =
      -(Real.pi * Real.exp (81 / 160 : ℝ) - (101 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (101 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (101 / 200 : ℝ)) := by
    have h := hpThetaJensenCell404_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (101071836791 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell404_endpointUpper :
    hpThetaJensenKernelEndpointUpper (101 / 400 : ℝ) (81 / 320 : ℝ) ≤ (2415547899 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (81 / 160 : ℝ)) (2084834059447867 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (81 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell404_product_upper
  have hD : (1606149611457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (101 / 200 : ℝ) - (81 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell404_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell404_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (101 / 200 : ℝ) - (81 / 640 : ℝ)) ≤
      (1 / (1606149611457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1606149611457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((81 / 640 : ℝ) - Real.pi * Real.exp (101 / 200 : ℝ)) ≤
      (2 / (1606149611457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (81 / 640 : ℝ) - Real.pi * Real.exp (101 / 200 : ℝ) =
      -(Real.pi * Real.exp (101 / 200 : ℝ) - (81 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2084834059447867 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2084834059447867 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell404_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (101 / 400 : ℝ) (81 / 320 : ℝ)) :
    (381701303 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2415547899 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell404_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell404_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell405_leftExp :
    (8295290237 / 5000000000 : ℝ) ≤ Real.exp (81 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (81 / 160 : ℝ) (507973058093 / 500000000000 : ℝ)
    (8295290237 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell405_rightExp :
    Real.exp (203 / 400 : ℝ) ≤ (16611331667 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (203 / 400 : ℝ) (1015985802357 / 1000000000000 : ℝ)
    (16611331667 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell405_denomUpper :
    Real.exp (50920418285725531 / 10000000000000000 : ℝ) ≤ (1627217730551 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (50920418285725531 / 10000000000000000 : ℝ) (117248603069
    / 100000000000 : ℝ) (1627217730551 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell405_denomLower :
    (1616136304283 / 10000000000 : ℝ) ≤ Real.exp (3178255305779663 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3178255305779663 / 625000000000000 : ℝ) (1172235682579 /
    1000000000000 : ℝ) (1616136304283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell405_product_lower :
    (3257552180779663 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (81 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell405_leftExp
    (by norm_num : (0 : ℝ) ≤ (8295290237 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell405_product_upper :
    Real.pi * Real.exp (203 / 400 : ℝ) ≤ (52186043285725531 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell405_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell405_endpointLower :
    (1189004317 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 320 : ℝ) (203 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3257552180779663 / 625000000000000 : ℝ) (Real.pi * Real.exp (81 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell405_product_lower
  have hD : Real.exp (Real.pi * Real.exp (203 / 400 : ℝ) - (81 / 640 : ℝ)) ≤
      (1627217730551 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell405_denomUpper
    linarith [hpThetaJensenCell405_product_upper]
  have hi : (1 / (1627217730551 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (203 / 400 : ℝ) - (81 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1627217730551 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1627217730551 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((81 / 640 : ℝ) - Real.pi * Real.exp (203 / 400 : ℝ)) := by
    rw [show (81 / 640 : ℝ) - Real.pi * Real.exp (203 / 400 : ℝ) =
      -(Real.pi * Real.exp (203 / 400 : ℝ) - (81 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (81 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (81 / 160 : ℝ)) := by
    have h := hpThetaJensenCell405_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1627217730551 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell405_endpointUpper :
    hpThetaJensenKernelEndpointUpper (81 / 320 : ℝ) (203 / 800 : ℝ) ≤ (4815690519 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (203 / 400 : ℝ)) (52186043285725531 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (203 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell405_product_upper
  have hD : (1616136304283 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (81 / 160 : ℝ) - (203 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell405_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell405_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (81 / 160 : ℝ) - (203 / 1600 : ℝ)) ≤
      (1 / (1616136304283 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1616136304283 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((203 / 1600 : ℝ) - Real.pi * Real.exp (81 / 160 : ℝ)) ≤
      (2 / (1616136304283 / 10000000000 : ℝ) : ℝ) := by
    rw [show (203 / 1600 : ℝ) - Real.pi * Real.exp (81 / 160 : ℝ) =
      -(Real.pi * Real.exp (81 / 160 : ℝ) - (203 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (52186043285725531 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (52186043285725531 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell405_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (81 / 320 : ℝ) (203 / 800 : ℝ)) :
    (1189004317 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4815690519 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell405_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell405_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell406_leftExp :
    (8305665833 / 5000000000 : ℝ) ≤ Real.exp (203 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (203 / 400 : ℝ) (253996450589 / 250000000000 : ℝ)
    (8305665833 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell406_rightExp :
    Real.exp (407 / 800 : ℝ) ≤ (3326421763 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (407 / 800 : ℝ) (1016025490077 / 1000000000000 : ℝ)
    (3326421763 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell406_denomUpper :
    Real.exp (10196513325688459 / 2000000000000000 : ℝ) ≤ (818681054599 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10196513325688459 / 2000000000000000 : ℝ) (586356882751
    / 500000000000 : ℝ) (818681054599 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell406_denomLower :
    (406549583829 / 2500000000 : ℝ) ≤ Real.exp (3182134479453267 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3182134479453267 / 625000000000000 : ℝ) (7327894187 /
    6250000000 : ℝ) (406549583829 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell406_product_lower :
    (3261626666953267 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (203 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell406_leftExp
    (by norm_num : (0 : ℝ) ≤ (8305665833 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell406_product_upper :
    Real.pi * Real.exp (407 / 800 : ℝ) ≤ (10450263325688459 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell406_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell406_endpointLower :
    (9481548247 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (203 / 800 : ℝ) (407 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3261626666953267 / 625000000000000 : ℝ) (Real.pi * Real.exp (203 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell406_product_lower
  have hD : Real.exp (Real.pi * Real.exp (407 / 800 : ℝ) - (203 / 1600 : ℝ)) ≤
      (818681054599 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell406_denomUpper
    linarith [hpThetaJensenCell406_product_upper]
  have hi : (1 / (818681054599 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (407 / 800 : ℝ) - (203 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (818681054599 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (818681054599 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((203 / 1600 : ℝ) - Real.pi * Real.exp (407 / 800 : ℝ)) := by
    rw [show (203 / 1600 : ℝ) - Real.pi * Real.exp (407 / 800 : ℝ) =
      -(Real.pi * Real.exp (407 / 800 : ℝ) - (203 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (203 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (203 / 400 : ℝ)) := by
    have h := hpThetaJensenCell406_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (818681054599 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell406_endpointUpper :
    hpThetaJensenKernelEndpointUpper (203 / 800 : ℝ) (407 / 1600 : ℝ) ≤ (9600582053 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (407 / 800 : ℝ)) (10450263325688459 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (407 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell406_product_upper
  have hD : (406549583829 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (203 / 400 : ℝ) - (407 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell406_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell406_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (203 / 400 : ℝ) - (407 / 3200 : ℝ)) ≤
      (1 / (406549583829 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (406549583829 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((407 / 3200 : ℝ) - Real.pi * Real.exp (203 / 400 : ℝ)) ≤
      (2 / (406549583829 / 2500000000 : ℝ) : ℝ) := by
    rw [show (407 / 3200 : ℝ) - Real.pi * Real.exp (203 / 400 : ℝ) =
      -(Real.pi * Real.exp (203 / 400 : ℝ) - (407 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10450263325688459 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (10450263325688459 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell406_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (203 / 800 : ℝ) (407 / 1600 : ℝ)) :
    (9481548247 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9600582053 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell406_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell406_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell407_leftExp :
    (16632108813 / 10000000000 : ℝ) ≤ Real.exp (407 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (407 / 800 : ℝ) (254006372519 / 250000000000 : ℝ)
    (16632108813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell407_rightExp :
    Real.exp (51 / 100 : ℝ) ≤ (333058239 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 100 : ℝ) (254016294837 / 250000000000 : ℝ)
    (333058239 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell407_denomUpper :
    Real.exp (1020895932234727 / 200000000000000 : ℝ) ≤ (65903327231 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1020895932234727 / 200000000000000 : ℝ) (586470921899 /
    500000000000 : ℝ) (65903327231 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell407_denomLower :
    (818168177483 / 5000000000 : ℝ) ≤ Real.exp (6372037498756287 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6372037498756287 / 1250000000000000 : ℝ) (234538160037 /
    200000000000 : ℝ) (818168177483 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell407_product_lower :
    (6531412498756287 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (407 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell407_leftExp
    (by norm_num : (0 : ℝ) ≤ (16632108813 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell407_product_upper :
    Real.pi * Real.exp (51 / 100 : ℝ) ≤ (1046333432234727 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell407_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell407_endpointLower :
    (9451074147 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (407 / 1600 : ℝ) (51 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6531412498756287 / 1250000000000000 : ℝ) (Real.pi * Real.exp (407 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell407_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 100 : ℝ) - (407 / 3200 : ℝ)) ≤
      (65903327231 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell407_denomUpper
    linarith [hpThetaJensenCell407_product_upper]
  have hi : (1 / (65903327231 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 100 : ℝ) - (407 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65903327231 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65903327231 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((407 / 3200 : ℝ) - Real.pi * Real.exp (51 / 100 : ℝ)) := by
    rw [show (407 / 3200 : ℝ) - Real.pi * Real.exp (51 / 100 : ℝ) =
      -(Real.pi * Real.exp (51 / 100 : ℝ) - (407 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (407 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (407 / 800 : ℝ)) := by
    have h := hpThetaJensenCell407_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65903327231 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell407_endpointUpper :
    hpThetaJensenKernelEndpointUpper (407 / 1600 : ℝ) (51 / 200 : ℝ) ≤ (4784897539 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 100 : ℝ)) (1046333432234727 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell407_product_upper
  have hD : (818168177483 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (407 / 800 : ℝ) - (51 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell407_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell407_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (407 / 800 : ℝ) - (51 / 400 : ℝ)) ≤
      (1 / (818168177483 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (818168177483 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 400 : ℝ) - Real.pi * Real.exp (407 / 800 : ℝ)) ≤
      (2 / (818168177483 / 5000000000 : ℝ) : ℝ) := by
    rw [show (51 / 400 : ℝ) - Real.pi * Real.exp (407 / 800 : ℝ) =
      -(Real.pi * Real.exp (407 / 800 : ℝ) - (51 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1046333432234727 / 200000000000000 : ℝ) ^ 2 - 6 *
      (1046333432234727 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell407_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (407 / 1600 : ℝ) (51 / 200 : ℝ)) :
    (9451074147 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4784897539 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell407_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell407_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell408_leftExp :
    (16652911949 / 10000000000 : ℝ) ≤ Real.exp (51 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 100 : ℝ) (1016065179347 / 1000000000000 : ℝ)
    (16652911949 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell408_rightExp :
    Real.exp (409 / 800 : ℝ) ≤ (8336870553 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (409 / 800 : ℝ) (101610487017 / 100000000000 : ℝ)
    (8336870553 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell408_denomUpper :
    Real.exp (25553554171210929 / 5000000000000000 : ℝ) ≤ (1657881609027 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25553554171210929 / 5000000000000000 : ℝ) (23463405323 /
    20000000000 : ℝ) (1657881609027 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell408_denomLower :
    (164655102043 / 1000000000 : ℝ) ≤ Real.exp (6379816244460351 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6379816244460351 / 1250000000000000 : ℝ) (1172918873949
    / 1000000000000 : ℝ) (164655102043 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell408_product_lower :
    (6539581869460351 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell408_leftExp
    (by norm_num : (0 : ℝ) ≤ (16652911949 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell408_product_upper :
    Real.pi * Real.exp (409 / 800 : ℝ) ≤ (26191054171210929 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell408_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell408_endpointLower :
    (9420612669 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 200 : ℝ) (409 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6539581869460351 / 1250000000000000 : ℝ) (Real.pi * Real.exp (51 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell408_product_lower
  have hD : Real.exp (Real.pi * Real.exp (409 / 800 : ℝ) - (51 / 400 : ℝ)) ≤
      (1657881609027 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell408_denomUpper
    linarith [hpThetaJensenCell408_product_upper]
  have hi : (1 / (1657881609027 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (409 / 800 : ℝ) - (51 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1657881609027 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1657881609027 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 400 : ℝ) - Real.pi * Real.exp (409 / 800 : ℝ)) := by
    rw [show (51 / 400 : ℝ) - Real.pi * Real.exp (409 / 800 : ℝ) =
      -(Real.pi * Real.exp (409 / 800 : ℝ) - (51 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 100 : ℝ)) := by
    have h := hpThetaJensenCell408_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1657881609027 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell408_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 200 : ℝ) (409 / 1600 : ℝ) ≤ (9539020547 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (409 / 800 : ℝ)) (26191054171210929 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (409 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell408_product_upper
  have hD : (164655102043 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 100 : ℝ) - (409 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell408_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell408_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 100 : ℝ) - (409 / 3200 : ℝ)) ≤
      (1 / (164655102043 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (164655102043 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((409 / 3200 : ℝ) - Real.pi * Real.exp (51 / 100 : ℝ)) ≤
      (2 / (164655102043 / 1000000000 : ℝ) : ℝ) := by
    rw [show (409 / 3200 : ℝ) - Real.pi * Real.exp (51 / 100 : ℝ) =
      -(Real.pi * Real.exp (51 / 100 : ℝ) - (409 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26191054171210929 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26191054171210929 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell408_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 200 : ℝ) (409 / 1600 : ℝ)) :
    (9420612669 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9539020547 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell408_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell408_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell409_leftExp :
    (1042108819 / 625000000 : ℝ) ≤ Real.exp (409 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (409 / 800 : ℝ) (1016104870169 / 1000000000000 : ℝ)
    (1042108819 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell409_rightExp :
    Real.exp (41 / 80 : ℝ) ≤ (8347298157 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 80 : ℝ) (1016144562541 / 1000000000000 : ℝ)
    (8347298157 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell409_denomUpper :
    Real.exp (25584750958944101 / 5000000000000000 : ℝ) ≤ (834129031341 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25584750958944101 / 5000000000000000 : ℝ) (11733990331 /
    10000000000 : ℝ) (834129031341 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell409_denomLower :
    (165684299311 / 1000000000 : ℝ) ≤ Real.exp (399225325487481 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (399225325487481 / 78125000000000 : ℝ) (1173147291741 /
    1000000000000 : ℝ) (165684299311 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell409_product_lower :
    (409235091112481 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (409 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell409_leftExp
    (by norm_num : (0 : ℝ) ≤ (1042108819 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell409_product_upper :
    Real.pi * Real.exp (41 / 80 : ℝ) ≤ (26223813458944101 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell409_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell409_endpointLower :
    (9390164247 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (409 / 1600 : ℝ) (41 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (409235091112481 / 78125000000000 : ℝ) (Real.pi * Real.exp (409 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell409_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 80 : ℝ) - (409 / 3200 : ℝ)) ≤
      (834129031341 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell409_denomUpper
    linarith [hpThetaJensenCell409_product_upper]
  have hi : (1 / (834129031341 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 80 : ℝ) - (409 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (834129031341 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (834129031341 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((409 / 3200 : ℝ) - Real.pi * Real.exp (41 / 80 : ℝ)) := by
    rw [show (409 / 3200 : ℝ) - Real.pi * Real.exp (41 / 80 : ℝ) =
      -(Real.pi * Real.exp (41 / 80 : ℝ) - (409 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (409 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (409 / 800 : ℝ)) := by
    have h := hpThetaJensenCell409_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (834129031341 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell409_endpointUpper :
    hpThetaJensenKernelEndpointUpper (409 / 1600 : ℝ) (41 / 160 : ℝ) ≤ (1901651781 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 80 : ℝ)) (26223813458944101 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell409_product_upper
  have hD : (165684299311 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (409 / 800 : ℝ) - (41 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell409_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell409_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (409 / 800 : ℝ) - (41 / 320 : ℝ)) ≤
      (1 / (165684299311 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (165684299311 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 320 : ℝ) - Real.pi * Real.exp (409 / 800 : ℝ)) ≤
      (2 / (165684299311 / 1000000000 : ℝ) : ℝ) := by
    rw [show (41 / 320 : ℝ) - Real.pi * Real.exp (409 / 800 : ℝ) =
      -(Real.pi * Real.exp (409 / 800 : ℝ) - (41 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26223813458944101 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26223813458944101 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell409_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (409 / 1600 : ℝ) (41 / 160 : ℝ)) :
    (9390164247 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1901651781 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell409_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell409_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell410_leftExp :
    (2086824539 / 1250000000 : ℝ) ≤ Real.exp (41 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 80 : ℝ) (50807228127 / 50000000000 : ℝ) (2086824539
    / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell410_rightExp :
    Real.exp (411 / 800 : ℝ) ≤ (2089434701 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (411 / 800 : ℝ) (63511516029 / 62500000000 : ℝ)
    (2089434701 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell410_denomUpper :
    Real.exp (6403997180618693 / 1250000000000000 : ℝ) ≤ (1678713218451 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6403997180618693 / 1250000000000000 : ℝ) (46945125809 /
    40000000000 : ℝ) (1678713218451 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell410_denomLower :
    (416803235677 / 2500000000 : ℝ) ≤ Real.exp (799425550265761 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (799425550265761 / 156250000000000 : ℝ) (586688027067 /
    500000000000 : ℝ) (416803235677 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell410_product_lower :
    (819493909640761 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell410_leftExp
    (by norm_num : (0 : ℝ) ≤ (2086824539 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell410_product_upper :
    Real.pi * Real.exp (411 / 800 : ℝ) ≤ (6564153430618693 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell410_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell410_endpointLower :
    (9359729309 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 160 : ℝ) (411 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (819493909640761 / 156250000000000 : ℝ) (Real.pi * Real.exp (41 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell410_product_lower
  have hD : Real.exp (Real.pi * Real.exp (411 / 800 : ℝ) - (41 / 320 : ℝ)) ≤
      (1678713218451 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell410_denomUpper
    linarith [hpThetaJensenCell410_product_upper]
  have hi : (1 / (1678713218451 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (411 / 800 : ℝ) - (41 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1678713218451 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1678713218451 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 320 : ℝ) - Real.pi * Real.exp (411 / 800 : ℝ)) := by
    rw [show (41 / 320 : ℝ) - Real.pi * Real.exp (411 / 800 : ℝ) =
      -(Real.pi * Real.exp (411 / 800 : ℝ) - (41 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 80 : ℝ)) := by
    have h := hpThetaJensenCell410_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1678713218451 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell410_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 160 : ℝ) (411 / 1600 : ℝ) ≤ (4738755293 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (411 / 800 : ℝ)) (6564153430618693 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (411 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell410_product_upper
  have hD : (416803235677 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 80 : ℝ) - (411 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell410_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell410_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 80 : ℝ) - (411 / 3200 : ℝ)) ≤
      (1 / (416803235677 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (416803235677 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((411 / 3200 : ℝ) - Real.pi * Real.exp (41 / 80 : ℝ)) ≤
      (2 / (416803235677 / 2500000000 : ℝ) : ℝ) := by
    rw [show (411 / 3200 : ℝ) - Real.pi * Real.exp (41 / 80 : ℝ) =
      -(Real.pi * Real.exp (41 / 80 : ℝ) - (411 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6564153430618693 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (6564153430618693 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell410_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 160 : ℝ) (411 / 1600 : ℝ)) :
    (9359729309 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4738755293 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell410_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell410_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell411_leftExp :
    (8357738803 / 5000000000 : ℝ) ≤ Real.exp (411 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (411 / 800 : ℝ) (1016184256463 / 1000000000000 : ℝ)
    (8357738803 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell411_rightExp :
    Real.exp (103 / 200 : ℝ) ≤ (16736385019 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (103 / 200 : ℝ) (15878499249 / 15625000000 : ℝ)
    (16736385019 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell411_denomUpper :
    Real.exp (51294535020995267 / 10000000000000000 : ℝ) ≤ (1689247757829 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51294535020995267 / 10000000000000000 : ℝ) (234771520613
    / 200000000000 : ℝ) (1689247757829 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell411_denomLower :
    (1677661545063 / 10000000000 : ℝ) ≤ Real.exp (3201606920199297 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3201606920199297 / 625000000000000 : ℝ) (234721032339 /
    200000000000 : ℝ) (1677661545063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell411_product_lower :
    (3282075670199297 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (411 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell411_leftExp
    (by norm_num : (0 : ℝ) ≤ (8357738803 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell411_product_upper :
    Real.pi * Real.exp (103 / 200 : ℝ) ≤ (52578910020995267 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell411_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell411_endpointLower :
    (9329308293 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (411 / 1600 : ℝ) (103 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3282075670199297 / 625000000000000 : ℝ) (Real.pi * Real.exp (411 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell411_product_lower
  have hD : Real.exp (Real.pi * Real.exp (103 / 200 : ℝ) - (411 / 3200 : ℝ)) ≤
      (1689247757829 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell411_denomUpper
    linarith [hpThetaJensenCell411_product_upper]
  have hi : (1 / (1689247757829 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (103 / 200 : ℝ) - (411 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1689247757829 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1689247757829 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((411 / 3200 : ℝ) - Real.pi * Real.exp (103 / 200 : ℝ)) := by
    rw [show (411 / 3200 : ℝ) - Real.pi * Real.exp (103 / 200 : ℝ) =
      -(Real.pi * Real.exp (103 / 200 : ℝ) - (411 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (411 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (411 / 800 : ℝ)) := by
    have h := hpThetaJensenCell411_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1689247757829 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell411_endpointUpper :
    hpThetaJensenKernelEndpointUpper (411 / 1600 : ℝ) (103 / 400 : ℝ) ≤ (472338801 / 500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (103 / 200 : ℝ)) (52578910020995267 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (103 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell411_product_upper
  have hD : (1677661545063 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (411 / 800 : ℝ) - (103 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell411_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell411_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (411 / 800 : ℝ) - (103 / 800 : ℝ)) ≤
      (1 / (1677661545063 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1677661545063 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((103 / 800 : ℝ) - Real.pi * Real.exp (411 / 800 : ℝ)) ≤
      (2 / (1677661545063 / 10000000000 : ℝ) : ℝ) := by
    rw [show (103 / 800 : ℝ) - Real.pi * Real.exp (411 / 800 : ℝ) =
      -(Real.pi * Real.exp (411 / 800 : ℝ) - (103 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (52578910020995267 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (52578910020995267 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell411_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (411 / 1600 : ℝ) (103 / 400 : ℝ)) :
    (9329308293 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (472338801 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell411_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell411_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell412_leftExp :
    (16736385017 / 10000000000 : ℝ) ≤ Real.exp (103 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (103 / 200 : ℝ) (203244790387 / 200000000000 : ℝ)
    (16736385017 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell412_rightExp :
    Real.exp (413 / 800 : ℝ) ≤ (16757318581 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (413 / 800 : ℝ) (3175823903 / 3125000000 : ℝ)
    (16757318581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell412_denomUpper :
    Real.exp (51357174752839533 / 10000000000000000 : ℝ) ≤ (849931185293 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51357174752839533 / 10000000000000000 : ℝ) (587043703599
    / 500000000000 : ℝ) (849931185293 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell412_denomLower :
    (211023685161 / 1250000000 : ℝ) ≤ Real.exp (6411033534790883 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6411033534790883 / 1250000000000000 : ℝ) (234766922993 /
    200000000000 : ℝ) (211023685161 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell412_product_lower :
    (6572361659790883 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (103 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell412_leftExp
    (by norm_num : (0 : ℝ) ≤ (16736385017 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell412_product_upper :
    Real.pi * Real.exp (413 / 800 : ℝ) ≤ (52644674752839533 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell412_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell412_endpointLower :
    (9298901621 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (103 / 400 : ℝ) (413 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6572361659790883 / 1250000000000000 : ℝ) (Real.pi * Real.exp (103 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell412_product_lower
  have hD : Real.exp (Real.pi * Real.exp (413 / 800 : ℝ) - (103 / 800 : ℝ)) ≤
      (849931185293 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell412_denomUpper
    linarith [hpThetaJensenCell412_product_upper]
  have hi : (1 / (849931185293 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (413 / 800 : ℝ) - (103 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (849931185293 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (849931185293 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((103 / 800 : ℝ) - Real.pi * Real.exp (413 / 800 : ℝ)) := by
    rw [show (103 / 800 : ℝ) - Real.pi * Real.exp (413 / 800 : ℝ) =
      -(Real.pi * Real.exp (413 / 800 : ℝ) - (103 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (103 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (103 / 200 : ℝ)) := by
    have h := hpThetaJensenCell412_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (849931185293 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell412_endpointUpper :
    hpThetaJensenKernelEndpointUpper (103 / 400 : ℝ) (413 / 1600 : ℝ) ≤ (9416055649 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (413 / 800 : ℝ)) (52644674752839533 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (413 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell412_product_upper
  have hD : (211023685161 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (103 / 200 : ℝ) - (413 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell412_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell412_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (103 / 200 : ℝ) - (413 / 3200 : ℝ)) ≤
      (1 / (211023685161 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (211023685161 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((413 / 3200 : ℝ) - Real.pi * Real.exp (103 / 200 : ℝ)) ≤
      (2 / (211023685161 / 1250000000 : ℝ) : ℝ) := by
    rw [show (413 / 3200 : ℝ) - Real.pi * Real.exp (103 / 200 : ℝ) =
      -(Real.pi * Real.exp (103 / 200 : ℝ) - (413 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (52644674752839533 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (52644674752839533 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell412_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (103 / 400 : ℝ) (413 / 1600 : ℝ)) :
    (9298901621 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9416055649 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell412_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell412_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell413_leftExp :
    (16757318579 / 10000000000 : ℝ) ≤ Real.exp (413 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (413 / 800 : ℝ) (1016263648959 / 1000000000000 : ℝ)
    (16757318579 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell413_rightExp :
    Real.exp (207 / 400 : ℝ) ≤ (8389139163 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (207 / 400 : ℝ) (508151673767 / 500000000000 : ℝ)
    (8389139163 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell413_denomUpper :
    Real.exp (25709948370506659 / 5000000000000000 : ℝ) ≤ (855278876021 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25709948370506659 / 5000000000000000 : ℝ) (1174317558179
    / 1000000000000 : ℝ) (855278876021 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell413_denomLower :
    (1698797440721 / 10000000000 : ℝ) ≤ Real.exp (6418863498654721 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6418863498654721 / 1250000000000000 : ℝ) (587032207261 /
    500000000000 : ℝ) (1698797440721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell413_product_lower :
    (6580582248654721 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (413 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell413_leftExp
    (by norm_num : (0 : ℝ) ≤ (16757318579 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell413_product_upper :
    Real.pi * Real.exp (207 / 400 : ℝ) ≤ (26355260870506659 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell413_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell413_endpointLower :
    (2317127431 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (413 / 1600 : ℝ) (207 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6580582248654721 / 1250000000000000 : ℝ) (Real.pi * Real.exp (413 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell413_product_lower
  have hD : Real.exp (Real.pi * Real.exp (207 / 400 : ℝ) - (413 / 3200 : ℝ)) ≤
      (855278876021 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell413_denomUpper
    linarith [hpThetaJensenCell413_product_upper]
  have hi : (1 / (855278876021 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (207 / 400 : ℝ) - (413 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (855278876021 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (855278876021 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((413 / 3200 : ℝ) - Real.pi * Real.exp (207 / 400 : ℝ)) := by
    rw [show (413 / 3200 : ℝ) - Real.pi * Real.exp (207 / 400 : ℝ) =
      -(Real.pi * Real.exp (207 / 400 : ℝ) - (413 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (413 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (413 / 800 : ℝ)) := by
    have h := hpThetaJensenCell413_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (855278876021 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell413_endpointUpper :
    hpThetaJensenKernelEndpointUpper (413 / 1600 : ℝ) (207 / 800 : ℝ) ≤ (93853499 / 100000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (207 / 400 : ℝ)) (26355260870506659 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (207 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell413_product_upper
  have hD : (1698797440721 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (413 / 800 : ℝ) - (207 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell413_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell413_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (413 / 800 : ℝ) - (207 / 1600 : ℝ)) ≤
      (1 / (1698797440721 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1698797440721 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((207 / 1600 : ℝ) - Real.pi * Real.exp (413 / 800 : ℝ)) ≤
      (2 / (1698797440721 / 10000000000 : ℝ) : ℝ) := by
    rw [show (207 / 1600 : ℝ) - Real.pi * Real.exp (413 / 800 : ℝ) =
      -(Real.pi * Real.exp (413 / 800 : ℝ) - (207 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26355260870506659 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26355260870506659 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell413_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (413 / 1600 : ℝ) (207 / 800 : ℝ)) :
    (2317127431 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (93853499 / 100000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell413_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell413_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell414_leftExp :
    (671131133 / 400000000 : ℝ) ≤ Real.exp (207 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (207 / 400 : ℝ) (1016303347533 / 1000000000000 : ℝ)
    (671131133 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell414_rightExp :
    Real.exp (83 / 160 : ℝ) ≤ (524977009 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83 / 160 : ℝ) (1016343047659 / 1000000000000 : ℝ)
    (524977009 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell414_denomUpper :
    Real.exp (1608834409135337 / 312500000000000 : ℝ) ≤ (1721334605307 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1608834409135337 / 312500000000000 : ℝ) (1174548056587 /
    1000000000000 : ℝ) (1721334605307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell414_denomLower :
    (341897223733 / 2000000000 : ℝ) ≤ Real.exp (257068149797967 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (257068149797967 / 50000000000000 : ℝ) (117429456093 /
    100000000000 : ℝ) (341897223733 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell414_product_lower :
    (263552524797967 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (207 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell414_leftExp
    (by norm_num : (0 : ℝ) ≤ (671131133 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell414_product_upper :
    Real.pi * Real.exp (83 / 160 : ℝ) ≤ (1649264096635337 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell414_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell414_endpointLower :
    (2309533257 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (207 / 800 : ℝ) (83 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (263552524797967 / 50000000000000 : ℝ) (Real.pi * Real.exp (207 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell414_product_lower
  have hD : Real.exp (Real.pi * Real.exp (83 / 160 : ℝ) - (207 / 1600 : ℝ)) ≤
      (1721334605307 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell414_denomUpper
    linarith [hpThetaJensenCell414_product_upper]
  have hi : (1 / (1721334605307 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (83 / 160 : ℝ) - (207 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1721334605307 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1721334605307 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((207 / 1600 : ℝ) - Real.pi * Real.exp (83 / 160 : ℝ)) := by
    rw [show (207 / 1600 : ℝ) - Real.pi * Real.exp (83 / 160 : ℝ) =
      -(Real.pi * Real.exp (83 / 160 : ℝ) - (207 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (207 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (207 / 400 : ℝ)) := by
    have h := hpThetaJensenCell414_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1721334605307 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell414_endpointUpper :
    hpThetaJensenKernelEndpointUpper (207 / 800 : ℝ) (83 / 320 : ℝ) ≤ (4677329603 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (83 / 160 : ℝ)) (1649264096635337 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (83 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell414_product_upper
  have hD : (341897223733 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (207 / 400 : ℝ) - (83 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell414_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell414_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (207 / 400 : ℝ) - (83 / 640 : ℝ)) ≤
      (1 / (341897223733 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (341897223733 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((83 / 640 : ℝ) - Real.pi * Real.exp (207 / 400 : ℝ)) ≤
      (2 / (341897223733 / 2000000000 : ℝ) : ℝ) := by
    rw [show (83 / 640 : ℝ) - Real.pi * Real.exp (207 / 400 : ℝ) =
      -(Real.pi * Real.exp (207 / 400 : ℝ) - (83 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1649264096635337 / 312500000000000 : ℝ) ^ 2 - 6 *
      (1649264096635337 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell414_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (207 / 800 : ℝ) (83 / 320 : ℝ)) :
    (2309533257 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4677329603 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell414_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell414_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell415_leftExp :
    (8399632143 / 5000000000 : ℝ) ≤ Real.exp (83 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (83 / 160 : ℝ) (508171523829 / 500000000000 : ℝ)
    (8399632143 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell415_rightExp :
    Real.exp (13 / 25 : ℝ) ≤ (8410138249 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 25 : ℝ) (203276549867 / 200000000000 : ℝ)
    (8410138249 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell415_denomUpper :
    Real.exp (25772793952090657 / 5000000000000000 : ℝ) ≤ (866096819279 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25772793952090657 / 5000000000000000 : ℝ) (234955780593
    / 200000000000 : ℝ) (866096819279 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell415_denomLower :
    (344051243251 / 2000000000 : ℝ) ≤ Real.exp (3217277142923957 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3217277142923957 / 625000000000000 : ℝ) (234905010947 /
    200000000000 : ℝ) (344051243251 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell415_product_lower :
    (3298527142923957 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (83 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell415_leftExp
    (by norm_num : (0 : ℝ) ≤ (8399632143 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell415_product_upper :
    Real.pi * Real.exp (13 / 25 : ℝ) ≤ (26421231452090657 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell415_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell415_endpointLower :
    (9207771959 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 320 : ℝ) (13 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3298527142923957 / 625000000000000 : ℝ) (Real.pi * Real.exp (83 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell415_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 25 : ℝ) - (83 / 640 : ℝ)) ≤
      (866096819279 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell415_denomUpper
    linarith [hpThetaJensenCell415_product_upper]
  have hi : (1 / (866096819279 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 25 : ℝ) - (83 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (866096819279 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (866096819279 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((83 / 640 : ℝ) - Real.pi * Real.exp (13 / 25 : ℝ)) := by
    rw [show (83 / 640 : ℝ) - Real.pi * Real.exp (13 / 25 : ℝ) =
      -(Real.pi * Real.exp (13 / 25 : ℝ) - (83 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (83 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (83 / 160 : ℝ)) := by
    have h := hpThetaJensenCell415_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (866096819279 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell415_endpointUpper :
    hpThetaJensenKernelEndpointUpper (83 / 320 : ℝ) (13 / 50 : ℝ) ≤ (9323983999 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 25 : ℝ)) (26421231452090657 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell415_product_upper
  have hD : (344051243251 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (83 / 160 : ℝ) - (13 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell415_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell415_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (83 / 160 : ℝ) - (13 / 100 : ℝ)) ≤
      (1 / (344051243251 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (344051243251 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 100 : ℝ) - Real.pi * Real.exp (83 / 160 : ℝ)) ≤
      (2 / (344051243251 / 2000000000 : ℝ) : ℝ) := by
    rw [show (13 / 100 : ℝ) - Real.pi * Real.exp (83 / 160 : ℝ) =
      -(Real.pi * Real.exp (83 / 160 : ℝ) - (13 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26421231452090657 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (26421231452090657 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell415_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (83 / 320 : ℝ) (13 / 50 : ℝ)) :
    (9207771959 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9323983999 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell415_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell415_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell416_leftExp :
    (1051267281 / 625000000 : ℝ) ≤ Real.exp (13 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 25 : ℝ) (508191374667 / 500000000000 : ℝ)
    (1051267281 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell416_rightExp :
    Real.exp (417 / 800 : ℝ) ≤ (1684131499 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (417 / 800 : ℝ) (1016422452561 / 1000000000000 : ℝ)
    (1684131499 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell416_denomUpper :
    Real.exp (5160855728337907 / 1000000000000000 : ℝ) ≤ (43578389213 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5160855728337907 / 1000000000000000 : ℝ) (1175010097893
    / 1000000000000 : ℝ) (43578389213 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell416_denomLower :
    (432777110713 / 2500000000 : ℝ) ≤ Real.exp (402650945918919 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (402650945918919 / 78125000000000 : ℝ) (234951179303 /
    200000000000 : ℝ) (432777110713 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell416_product_lower :
    (412831609981419 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell416_leftExp
    (by norm_num : (0 : ℝ) ≤ (1051267281 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell416_product_upper :
    Real.pi * Real.exp (417 / 800 : ℝ) ≤ (5290855728337907 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell416_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell416_endpointLower :
    (4588713471 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 50 : ℝ) (417 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (412831609981419 / 78125000000000 : ℝ) (Real.pi * Real.exp (13 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell416_product_lower
  have hD : Real.exp (Real.pi * Real.exp (417 / 800 : ℝ) - (13 / 100 : ℝ)) ≤
      (43578389213 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell416_denomUpper
    linarith [hpThetaJensenCell416_product_upper]
  have hi : (1 / (43578389213 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (417 / 800 : ℝ) - (13 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (43578389213 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (43578389213 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 100 : ℝ) - Real.pi * Real.exp (417 / 800 : ℝ)) := by
    rw [show (13 / 100 : ℝ) - Real.pi * Real.exp (417 / 800 : ℝ) =
      -(Real.pi * Real.exp (417 / 800 : ℝ) - (13 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 25 : ℝ)) := by
    have h := hpThetaJensenCell416_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (43578389213 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell416_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 50 : ℝ) (417 / 1600 : ℝ) ≤ (2323331177 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (417 / 800 : ℝ)) (5290855728337907 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (417 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell416_product_upper
  have hD : (432777110713 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 25 : ℝ) - (417 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell416_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell416_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 25 : ℝ) - (417 / 3200 : ℝ)) ≤
      (1 / (432777110713 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (432777110713 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((417 / 3200 : ℝ) - Real.pi * Real.exp (13 / 25 : ℝ)) ≤
      (2 / (432777110713 / 2500000000 : ℝ) : ℝ) := by
    rw [show (417 / 3200 : ℝ) - Real.pi * Real.exp (13 / 25 : ℝ) =
      -(Real.pi * Real.exp (13 / 25 : ℝ) - (417 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5290855728337907 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5290855728337907 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell416_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 50 : ℝ) (417 / 1600 : ℝ)) :
    (4588713471 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2323331177 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell416_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell416_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell417_leftExp :
    (4210328747 / 2500000000 : ℝ) ≤ Real.exp (417 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (417 / 800 : ℝ) (12705280657 / 12500000000 : ℝ)
    (4210328747 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell417_rightExp :
    Real.exp (209 / 400 : ℝ) ≤ (4215594949 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (209 / 400 : ℝ) (1016462157339 / 1000000000000 : ℝ)
    (4215594949 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell417_denomUpper :
    Real.exp (12917902332613757 / 2500000000000000 : ℝ) ≤ (1754161117771 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12917902332613757 / 2500000000000000 : ℝ) (1175241641929
    / 1000000000000 : ℝ) (1754161117771 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell417_denomLower :
    (87102175711 / 500000000 : ℝ) ≤ Real.exp (1612571576118153 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1612571576118153 / 312500000000000 : ℝ) (1174987086839 /
    1000000000000 : ℝ) (87102175711 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell417_product_lower :
    (1653391888618153 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (417 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell417_leftExp
    (by norm_num : (0 : ℝ) ≤ (4210328747 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell417_product_upper :
    Real.pi * Real.exp (209 / 400 : ℝ) ≤ (13243683582613757 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell417_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell417_endpointLower :
    (9147098401 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (417 / 1600 : ℝ) (209 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1653391888618153 / 312500000000000 : ℝ) (Real.pi * Real.exp (417 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell417_product_lower
  have hD : Real.exp (Real.pi * Real.exp (209 / 400 : ℝ) - (417 / 3200 : ℝ)) ≤
      (1754161117771 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell417_denomUpper
    linarith [hpThetaJensenCell417_product_upper]
  have hi : (1 / (1754161117771 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (209 / 400 : ℝ) - (417 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1754161117771 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1754161117771 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((417 / 3200 : ℝ) - Real.pi * Real.exp (209 / 400 : ℝ)) := by
    rw [show (417 / 3200 : ℝ) - Real.pi * Real.exp (209 / 400 : ℝ) =
      -(Real.pi * Real.exp (209 / 400 : ℝ) - (417 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (417 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (417 / 800 : ℝ)) := by
    have h := hpThetaJensenCell417_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1754161117771 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell417_endpointUpper :
    hpThetaJensenKernelEndpointUpper (417 / 1600 : ℝ) (209 / 800 : ℝ) ≤ (9262681757 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (209 / 400 : ℝ)) (13243683582613757 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (209 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell417_product_upper
  have hD : (87102175711 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (417 / 800 : ℝ) - (209 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell417_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell417_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (417 / 800 : ℝ) - (209 / 1600 : ℝ)) ≤
      (1 / (87102175711 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (87102175711 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((209 / 1600 : ℝ) - Real.pi * Real.exp (417 / 800 : ℝ)) ≤
      (2 / (87102175711 / 500000000 : ℝ) : ℝ) := by
    rw [show (209 / 1600 : ℝ) - Real.pi * Real.exp (417 / 800 : ℝ) =
      -(Real.pi * Real.exp (417 / 800 : ℝ) - (209 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13243683582613757 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (13243683582613757 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell417_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (417 / 1600 : ℝ) (209 / 800 : ℝ)) :
    (9147098401 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9262681757 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell417_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell417_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell418_leftExp :
    (3372475959 / 2000000000 : ℝ) ≤ Real.exp (209 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (209 / 400 : ℝ) (508231078669 / 500000000000 : ℝ)
    (3372475959 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell418_rightExp :
    Real.exp (419 / 800 : ℝ) ≤ (337669419 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (419 / 800 : ℝ) (1016501863667 / 1000000000000 : ℝ)
    (337669419 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell418_denomUpper :
    Real.exp (1034694883044467 / 200000000000000 : ℝ) ≤ (1765271016901 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1034694883044467 / 200000000000000 : ℝ) (1175473535653 /
    1000000000000 : ℝ) (1765271016901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell418_denomLower :
    (876531076459 / 5000000000 : ℝ) ≤ Real.exp (1291633561623341 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1291633561623341 / 250000000000000 : ℝ) (587609313137 /
    500000000000 : ℝ) (876531076459 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell418_product_lower :
    (1324367936623341 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (209 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell418_leftExp
    (by norm_num : (0 : ℝ) ≤ (3372475959 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell418_product_upper :
    Real.pi * Real.exp (419 / 800 : ℝ) ≤ (1060819883044467 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell418_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell418_endpointLower :
    (2279196689 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (209 / 800 : ℝ) (419 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1324367936623341 / 250000000000000 : ℝ) (Real.pi * Real.exp (209 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell418_product_lower
  have hD : Real.exp (Real.pi * Real.exp (419 / 800 : ℝ) - (209 / 1600 : ℝ)) ≤
      (1765271016901 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell418_denomUpper
    linarith [hpThetaJensenCell418_product_upper]
  have hi : (1 / (1765271016901 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (419 / 800 : ℝ) - (209 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1765271016901 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1765271016901 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((209 / 1600 : ℝ) - Real.pi * Real.exp (419 / 800 : ℝ)) := by
    rw [show (209 / 1600 : ℝ) - Real.pi * Real.exp (419 / 800 : ℝ) =
      -(Real.pi * Real.exp (419 / 800 : ℝ) - (209 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (209 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (209 / 400 : ℝ)) := by
    have h := hpThetaJensenCell418_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1765271016901 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell418_endpointUpper :
    hpThetaJensenKernelEndpointUpper (209 / 800 : ℝ) (419 / 1600 : ℝ) ≤ (369282223 / 400000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (419 / 800 : ℝ)) (1060819883044467 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (419 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell418_product_upper
  have hD : (876531076459 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (209 / 400 : ℝ) - (419 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell418_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell418_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (209 / 400 : ℝ) - (419 / 3200 : ℝ)) ≤
      (1 / (876531076459 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (876531076459 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((419 / 3200 : ℝ) - Real.pi * Real.exp (209 / 400 : ℝ)) ≤
      (2 / (876531076459 / 5000000000 : ℝ) : ℝ) := by
    rw [show (419 / 3200 : ℝ) - Real.pi * Real.exp (209 / 400 : ℝ) =
      -(Real.pi * Real.exp (209 / 400 : ℝ) - (419 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1060819883044467 / 200000000000000 : ℝ) ^ 2 - 6 *
      (1060819883044467 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell418_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (209 / 800 : ℝ) (419 / 1600 : ℝ)) :
    (2279196689 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (369282223 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell418_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell418_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell419_leftExp :
    (4220867737 / 2500000000 : ℝ) ≤ Real.exp (419 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (419 / 800 : ℝ) (508250931833 / 500000000000 : ℝ)
    (4220867737 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell419_rightExp :
    Real.exp (21 / 40 : ℝ) ≤ (3380917697 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 40 : ℝ) (1016541571547 / 1000000000000 : ℝ)
    (3380917697 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell419_denomUpper :
    Real.exp (10359592370471321 / 2000000000000000 : ℝ) ≤ (222058250383 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10359592370471321 / 2000000000000000 : ℝ) (235141155927
    / 200000000000 : ℝ) (222058250383 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell419_denomLower :
    (882082543773 / 5000000000 : ℝ) ≤ Real.exp (1616514914452163 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1616514914452163 / 312500000000000 : ℝ) (146931314421 /
    125000000000 : ℝ) (882082543773 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell419_product_lower :
    (1657530539452163 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (419 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell419_leftExp
    (by norm_num : (0 : ℝ) ≤ (4220867737 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell419_product_upper :
    Real.pi * Real.exp (21 / 40 : ℝ) ≤ (10621467370471321 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell419_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell419_endpointLower :
    (363459697 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (419 / 1600 : ℝ) (21 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1657530539452163 / 312500000000000 : ℝ) (Real.pi * Real.exp (419 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell419_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 40 : ℝ) - (419 / 3200 : ℝ)) ≤
      (222058250383 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell419_denomUpper
    linarith [hpThetaJensenCell419_product_upper]
  have hi : (1 / (222058250383 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 40 : ℝ) - (419 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (222058250383 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (222058250383 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((419 / 3200 : ℝ) - Real.pi * Real.exp (21 / 40 : ℝ)) := by
    rw [show (419 / 3200 : ℝ) - Real.pi * Real.exp (21 / 40 : ℝ) =
      -(Real.pi * Real.exp (21 / 40 : ℝ) - (419 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (419 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (419 / 800 : ℝ)) := by
    have h := hpThetaJensenCell419_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (222058250383 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell419_endpointUpper :
    hpThetaJensenKernelEndpointUpper (419 / 1600 : ℝ) (21 / 80 : ℝ) ≤ (9201446593 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 40 : ℝ)) (10621467370471321 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell419_product_upper
  have hD : (882082543773 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (419 / 800 : ℝ) - (21 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell419_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell419_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (419 / 800 : ℝ) - (21 / 160 : ℝ)) ≤
      (1 / (882082543773 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (882082543773 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 160 : ℝ) - Real.pi * Real.exp (419 / 800 : ℝ)) ≤
      (2 / (882082543773 / 5000000000 : ℝ) : ℝ) := by
    rw [show (21 / 160 : ℝ) - Real.pi * Real.exp (419 / 800 : ℝ) =
      -(Real.pi * Real.exp (419 / 800 : ℝ) - (21 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10621467370471321 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (10621467370471321 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell419_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (419 / 1600 : ℝ) (21 / 80 : ℝ)) :
    (363459697 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9201446593 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell419_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell419_endpointUpper

def hpThetaJensenCellsBatch020Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4832316761 / 5000000000 : ℝ)
  | 1 => (1926818569 / 2000000000 : ℝ)
  | 2 => (960356217 / 1000000000 : ℝ)
  | 3 => (9573041931 / 10000000000 : ℝ)
  | 4 => (381701303 / 400000000 : ℝ)
  | 5 => (1189004317 / 1250000000 : ℝ)
  | 6 => (9481548247 / 10000000000 : ℝ)
  | 7 => (9451074147 / 10000000000 : ℝ)
  | 8 => (9420612669 / 10000000000 : ℝ)
  | 9 => (9390164247 / 10000000000 : ℝ)
  | 10 => (9359729309 / 10000000000 : ℝ)
  | 11 => (9329308293 / 10000000000 : ℝ)
  | 12 => (9298901621 / 10000000000 : ℝ)
  | 13 => (2317127431 / 2500000000 : ℝ)
  | 14 => (2309533257 / 2500000000 : ℝ)
  | 15 => (9207771959 / 10000000000 : ℝ)
  | 16 => (4588713471 / 5000000000 : ℝ)
  | 17 => (9147098401 / 10000000000 : ℝ)
  | 18 => (2279196689 / 2500000000 : ℝ)
  | 19 => (363459697 / 400000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch020Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4892770341 / 5000000000 : ℝ)
  | 1 => (9754688267 / 10000000000 : ℝ)
  | 2 => (194476913 / 200000000 : ℝ)
  | 3 => (9693013281 / 10000000000 : ℝ)
  | 4 => (2415547899 / 2500000000 : ℝ)
  | 5 => (4815690519 / 5000000000 : ℝ)
  | 6 => (9600582053 / 10000000000 : ℝ)
  | 7 => (4784897539 / 5000000000 : ℝ)
  | 8 => (9539020547 / 10000000000 : ℝ)
  | 9 => (1901651781 / 2000000000 : ℝ)
  | 10 => (4738755293 / 5000000000 : ℝ)
  | 11 => (472338801 / 500000000 : ℝ)
  | 12 => (9416055649 / 10000000000 : ℝ)
  | 13 => (93853499 / 100000000 : ℝ)
  | 14 => (4677329603 / 5000000000 : ℝ)
  | 15 => (9323983999 / 10000000000 : ℝ)
  | 16 => (2323331177 / 2500000000 : ℝ)
  | 17 => (9262681757 / 10000000000 : ℝ)
  | 18 => (369282223 / 400000000 : ℝ)
  | 19 => (9201446593 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch020_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch020Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch020Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell400_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell401_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell402_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell403_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell404_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell405_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell406_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell407_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell408_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell409_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell410_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell411_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell412_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell413_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell414_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell415_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell416_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell417_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell418_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell419_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper] at h ⊢
    exact h

end HodgeProofHP
