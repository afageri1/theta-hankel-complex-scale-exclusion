import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1260_leftExp :
    (48307416179 / 10000000000 : ℝ) ≤ Real.exp (63 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 40 : ℝ) (105045011157 / 100000000000 : ℝ)
    (48307416179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1260_rightExp :
    Real.exp (1261 / 800 : ℝ) ≤ (47234217 / 9765625 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1261 / 800 : ℝ) (52524557279 / 50000000000 : ℝ)
    (47234217 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1260_denomUpper :
    Real.exp (144545470643931 / 9765625000000 : ℝ) ≤ (26803453173449283 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (144545470643931 / 9765625000000 : ℝ) (317622278273 /
    200000000000 : ℝ) (26803453173449283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1260_denomLower :
    (657278010705461 / 250000000 : ℝ) ≤ Real.exp (18477695901077121 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (18477695901077121 / 1250000000000000 : ℝ) (1587153876603
    / 1000000000000 : ℝ) (657278010705461 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1260_product_lower :
    (18970274026077121 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (63 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1260_leftExp
    (by norm_num : (0 : ℝ) ≤ (48307416179 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1260_product_upper :
    Real.pi * Real.exp (1261 / 800 : ℝ) ≤ (148390685487681 / 9765625000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1260_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1260_endpointLower :
    (3097411 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 80 : ℝ) (1261 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (18970274026077121 / 1250000000000000 : ℝ) (Real.pi * Real.exp (63 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1260_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1261 / 800 : ℝ) - (63 / 160 : ℝ)) ≤
      (26803453173449283 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1260_denomUpper
    linarith [hpThetaJensenCell1260_product_upper]
  have hi : (1 / (26803453173449283 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1261 / 800 : ℝ) - (63 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26803453173449283 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26803453173449283 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 160 : ℝ) - Real.pi * Real.exp (1261 / 800 : ℝ)) := by
    rw [show (63 / 160 : ℝ) - Real.pi * Real.exp (1261 / 800 : ℝ) =
      -(Real.pi * Real.exp (1261 / 800 : ℝ) - (63 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1260_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26803453173449283 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1260_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 80 : ℝ) (1261 / 1600 : ℝ) ≤ (3174449 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1261 / 800 : ℝ)) (148390685487681 / 9765625000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1261 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1260_product_upper
  have hD : (657278010705461 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 40 : ℝ) - (1261 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1260_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1260_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 40 : ℝ) - (1261 / 3200 : ℝ)) ≤
      (1 / (657278010705461 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (657278010705461 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1261 / 3200 : ℝ) - Real.pi * Real.exp (63 / 40 : ℝ)) ≤
      (2 / (657278010705461 / 250000000 : ℝ) : ℝ) := by
    rw [show (1261 / 3200 : ℝ) - Real.pi * Real.exp (63 / 40 : ℝ) =
      -(Real.pi * Real.exp (63 / 40 : ℝ) - (1261 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (148390685487681 / 9765625000000 : ℝ) ^ 2 - 6 *
      (148390685487681 / 9765625000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1260_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 80 : ℝ) (1261 / 1600 : ℝ)) :
    (3097411 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3174449 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1260_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1260_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1261_leftExp :
    (9673567641 / 2000000000 : ℝ) ≤ Real.exp (1261 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1261 / 800 : ℝ) (1050491145579 / 1000000000000 : ℝ)
    (9673567641 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1261_rightExp :
    Real.exp (631 / 400 : ℝ) ≤ (48428335809 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (631 / 400 : ℝ) (131316522649 / 125000000000 : ℝ)
    (48428335809 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1261_denomUpper :
    Real.exp (148201495779203737 / 10000000000000000 : ℝ) ≤ (27309212868167173 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (148201495779203737 / 10000000000000000 : ℝ)
    (1589039386643 / 1000000000000 : ℝ) (27309212868167173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1261_denomLower :
    (3348322082774857 / 1250000000 : ℝ) ≤ Real.exp (3700206589053059 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3700206589053059 / 250000000000000 : ℝ) (794040066891 /
    500000000000 : ℝ) (3348322082774857 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1261_product_lower :
    (3798800339053059 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1261 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1261_leftExp
    (by norm_num : (0 : ℝ) ≤ (9673567641 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1261_product_upper :
    Real.pi * Real.exp (631 / 400 : ℝ) ≤ (152142120779203737 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1261_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1261_endpointLower :
    (121923 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (1261 / 1600 : ℝ) (631 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3798800339053059 / 250000000000000 : ℝ) (Real.pi * Real.exp (1261 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1261_product_lower
  have hD : Real.exp (Real.pi * Real.exp (631 / 400 : ℝ) - (1261 / 3200 : ℝ)) ≤
      (27309212868167173 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1261_denomUpper
    linarith [hpThetaJensenCell1261_product_upper]
  have hi : (1 / (27309212868167173 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (631 / 400 : ℝ) - (1261 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27309212868167173 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27309212868167173 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1261 / 3200 : ℝ) - Real.pi * Real.exp (631 / 400 : ℝ)) := by
    rw [show (1261 / 3200 : ℝ) - Real.pi * Real.exp (631 / 400 : ℝ) =
      -(Real.pi * Real.exp (631 / 400 : ℝ) - (1261 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1261 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1261 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1261_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27309212868167173 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1261_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1261 / 1600 : ℝ) (631 / 800 : ℝ) ≤ (6247919 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (631 / 400 : ℝ)) (152142120779203737 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (631 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1261_product_upper
  have hD : (3348322082774857 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1261 / 800 : ℝ) - (631 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1261_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1261_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1261 / 800 : ℝ) - (631 / 1600 : ℝ)) ≤
      (1 / (3348322082774857 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3348322082774857 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((631 / 1600 : ℝ) - Real.pi * Real.exp (1261 / 800 : ℝ)) ≤
      (2 / (3348322082774857 / 1250000000 : ℝ) : ℝ) := by
    rw [show (631 / 1600 : ℝ) - Real.pi * Real.exp (1261 / 800 : ℝ) =
      -(Real.pi * Real.exp (1261 / 800 : ℝ) - (631 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (152142120779203737 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (152142120779203737 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1261_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1261 / 1600 : ℝ) (631 / 800 : ℝ)) :
    (121923 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6247919 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1261_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1261_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1262_leftExp :
    (48428335807 / 10000000000 : ℝ) ≤ Real.exp (631 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (631 / 400 : ℝ) (1050532181191 / 1000000000000 : ℝ)
    (48428335807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1262_rightExp :
    Real.exp (1263 / 800 : ℝ) ≤ (48488909079 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1263 / 800 : ℝ) (1050573218407 / 1000000000000 : ℝ)
    (48488909079 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1262_denomUpper :
    Real.exp (148388667340222847 / 10000000000000000 : ℝ) ≤ (27825177298537367 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (148388667340222847 / 10000000000000000 : ℝ)
    (794984552669 / 500000000000 : ℝ) (27825177298537367 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1262_denomLower :
    (27292017754037163 / 10000000000 : ℝ) ≤ Real.exp (18524399668073093 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18524399668073093 / 1250000000000000 : ℝ) (158900811051
    / 100000000000 : ℝ) (27292017754037163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1262_product_lower :
    (19017759043073093 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (631 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1262_leftExp
    (by norm_num : (0 : ℝ) ≤ (48428335807 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1262_product_upper :
    Real.pi * Real.exp (1263 / 800 : ℝ) ≤ (152332417340222847 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1262_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1262_endpointLower :
    (2999453 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (631 / 800 : ℝ) (1263 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19017759043073093 / 1250000000000000 : ℝ) (Real.pi * Real.exp (631 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1262_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1263 / 800 : ℝ) - (631 / 1600 : ℝ)) ≤
      (27825177298537367 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1262_denomUpper
    linarith [hpThetaJensenCell1262_product_upper]
  have hi : (1 / (27825177298537367 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1263 / 800 : ℝ) - (631 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27825177298537367 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27825177298537367 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((631 / 1600 : ℝ) - Real.pi * Real.exp (1263 / 800 : ℝ)) := by
    rw [show (631 / 1600 : ℝ) - Real.pi * Real.exp (1263 / 800 : ℝ) =
      -(Real.pi * Real.exp (1263 / 800 : ℝ) - (631 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (631 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (631 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1262_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27825177298537367 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1262_endpointUpper :
    hpThetaJensenKernelEndpointUpper (631 / 800 : ℝ) (1263 / 1600 : ℝ) ≤ (3074199 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1263 / 800 : ℝ)) (152332417340222847 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1263 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1262_product_upper
  have hD : (27292017754037163 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (631 / 400 : ℝ) - (1263 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1262_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1262_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (631 / 400 : ℝ) - (1263 / 3200 : ℝ)) ≤
      (1 / (27292017754037163 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (27292017754037163 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1263 / 3200 : ℝ) - Real.pi * Real.exp (631 / 400 : ℝ)) ≤
      (2 / (27292017754037163 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1263 / 3200 : ℝ) - Real.pi * Real.exp (631 / 400 : ℝ) =
      -(Real.pi * Real.exp (631 / 400 : ℝ) - (1263 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (152332417340222847 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (152332417340222847 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1262_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (631 / 800 : ℝ) (1263 / 1600 : ℝ)) :
    (2999453 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3074199 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1262_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1262_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1263_leftExp :
    (48488909077 / 10000000000 : ℝ) ≤ Real.exp (1263 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1263 / 800 : ℝ) (525286609203 / 500000000000 : ℝ)
    (48488909077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1263_rightExp :
    Real.exp (79 / 50 : ℝ) ≤ (24274779057 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 50 : ℝ) (42024570289 / 40000000000 : ℝ)
    (24274779057 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1263_denomUpper :
    Real.exp (74288038462017801 / 5000000000000000 : ℝ) ≤ (7087891221502653 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (74288038462017801 / 5000000000000000 : ℝ) (1590900551341
    / 1000000000000 : ℝ) (7087891221502653 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1263_denomLower :
    (347595714268659 / 125000000 : ℝ) ≤ Real.exp (18547796105628823 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (18547796105628823 / 1250000000000000 : ℝ) (317987562121
    / 200000000000 : ℝ) (347595714268659 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1263_product_lower :
    (19041546105628823 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1263 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1263_leftExp
    (by norm_num : (0 : ℝ) ≤ (48488909077 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1263_product_upper :
    Real.pi * Real.exp (79 / 50 : ℝ) ≤ (76261475962017801 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1263_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1263_endpointLower :
    (5903071 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1263 / 1600 : ℝ) (79 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19041546105628823 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1263 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1263_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 50 : ℝ) - (1263 / 3200 : ℝ)) ≤
      (7087891221502653 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1263_denomUpper
    linarith [hpThetaJensenCell1263_product_upper]
  have hi : (1 / (7087891221502653 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 50 : ℝ) - (1263 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7087891221502653 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7087891221502653 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1263 / 3200 : ℝ) - Real.pi * Real.exp (79 / 50 : ℝ)) := by
    rw [show (1263 / 3200 : ℝ) - Real.pi * Real.exp (79 / 50 : ℝ) =
      -(Real.pi * Real.exp (79 / 50 : ℝ) - (1263 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1263 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1263 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1263_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7087891221502653 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1263_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1263 / 1600 : ℝ) (79 / 100 : ℝ) ≤ (3025159 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 50 : ℝ)) (76261475962017801 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1263_product_upper
  have hD : (347595714268659 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1263 / 800 : ℝ) - (79 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1263_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1263_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1263 / 800 : ℝ) - (79 / 200 : ℝ)) ≤
      (1 / (347595714268659 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (347595714268659 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 200 : ℝ) - Real.pi * Real.exp (1263 / 800 : ℝ)) ≤
      (2 / (347595714268659 / 125000000 : ℝ) : ℝ) := by
    rw [show (79 / 200 : ℝ) - Real.pi * Real.exp (1263 / 800 : ℝ) =
      -(Real.pi * Real.exp (1263 / 800 : ℝ) - (79 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (76261475962017801 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (76261475962017801 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1263_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1263 / 1600 : ℝ) (79 / 100 : ℝ)) :
    (5903071 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3025159 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1263_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1263_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1264_leftExp :
    (48549558111 / 10000000000 : ℝ) ≤ Real.exp (79 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 50 : ℝ) (131326782153 / 125000000000 : ℝ)
    (48549558111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1264_rightExp :
    Real.exp (253 / 160 : ℝ) ≤ (48610283007 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (253 / 160 : ℝ) (525327648823 / 500000000000 : ℝ)
    (48610283007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1264_denomUpper :
    Real.exp (148763724822810151 / 10000000000000000 : ℝ) ≤ (14444299475458991 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (148763724822810151 / 10000000000000000 : ℝ)
    (1591833728501 / 1000000000000 : ℝ) (14444299475458991 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1264_denomLower :
    (28333713107300059 / 10000000000 : ℝ) ≤ Real.exp (18571222295631589 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18571222295631589 / 1250000000000000 : ℝ) (1590869237957
    / 1000000000000 : ℝ) (28333713107300059 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1264_product_lower :
    (19065362920631589 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1264_leftExp
    (by norm_num : (0 : ℝ) ≤ (48549558111 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1264_product_upper :
    Real.pi * Real.exp (253 / 160 : ℝ) ≤ (152713724822810151 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1264_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1264_endpointLower :
    (1452157 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 100 : ℝ) (253 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19065362920631589 / 1250000000000000 : ℝ) (Real.pi * Real.exp (79 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1264_product_lower
  have hD : Real.exp (Real.pi * Real.exp (253 / 160 : ℝ) - (79 / 200 : ℝ)) ≤
      (14444299475458991 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1264_denomUpper
    linarith [hpThetaJensenCell1264_product_upper]
  have hi : (1 / (14444299475458991 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (253 / 160 : ℝ) - (79 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14444299475458991 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14444299475458991 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 200 : ℝ) - Real.pi * Real.exp (253 / 160 : ℝ)) := by
    rw [show (79 / 200 : ℝ) - Real.pi * Real.exp (253 / 160 : ℝ) =
      -(Real.pi * Real.exp (253 / 160 : ℝ) - (79 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1264_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14444299475458991 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1264_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 100 : ℝ) (253 / 320 : ℝ) ≤ (297683 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (253 / 160 : ℝ)) (152713724822810151 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (253 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1264_product_upper
  have hD : (28333713107300059 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 50 : ℝ) - (253 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1264_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1264_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 50 : ℝ) - (253 / 640 : ℝ)) ≤
      (1 / (28333713107300059 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28333713107300059 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((253 / 640 : ℝ) - Real.pi * Real.exp (79 / 50 : ℝ)) ≤
      (2 / (28333713107300059 / 10000000000 : ℝ) : ℝ) := by
    rw [show (253 / 640 : ℝ) - Real.pi * Real.exp (79 / 50 : ℝ) =
      -(Real.pi * Real.exp (79 / 50 : ℝ) - (253 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (152713724822810151 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (152713724822810151 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1264_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 100 : ℝ) (253 / 320 : ℝ)) :
    (1452157 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (297683 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1264_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1264_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1265_leftExp :
    (12152570751 / 2500000000 : ℝ) ≤ Real.exp (253 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (253 / 160 : ℝ) (210131059529 / 200000000000 : ℝ)
    (12152570751 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1265_rightExp :
    Real.exp (633 / 400 : ℝ) ≤ (48671083853 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (633 / 400 : ℝ) (105069633967 / 100000000000 : ℝ)
    (48671083853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1265_denomUpper :
    Real.exp (148951611334997829 / 10000000000000000 : ℝ) ≤ (7359126969459843 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (148951611334997829 / 10000000000000000 : ℝ)
    (199096080089 / 125000000000 : ℝ) (7359126969459843 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1265_denomLower :
    (14435204424829647 / 5000000000 : ℝ) ≤ Real.exp (4648669568846949 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4648669568846949 / 312500000000000 : ℝ) (49743824889 /
    31250000000 : ℝ) (14435204424829647 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1265_product_lower :
    (4772302381346949 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (253 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1265_leftExp
    (by norm_num : (0 : ℝ) ≤ (12152570751 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1265_product_upper :
    Real.pi * Real.exp (633 / 400 : ℝ) ≤ (152904736334997829 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1265_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1265_endpointLower :
    (2857779 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (253 / 320 : ℝ) (633 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4772302381346949 / 312500000000000 : ℝ) (Real.pi * Real.exp (253 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1265_product_lower
  have hD : Real.exp (Real.pi * Real.exp (633 / 400 : ℝ) - (253 / 640 : ℝ)) ≤
      (7359126969459843 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1265_denomUpper
    linarith [hpThetaJensenCell1265_product_upper]
  have hi : (1 / (7359126969459843 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (633 / 400 : ℝ) - (253 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7359126969459843 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7359126969459843 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((253 / 640 : ℝ) - Real.pi * Real.exp (633 / 400 : ℝ)) := by
    rw [show (253 / 640 : ℝ) - Real.pi * Real.exp (633 / 400 : ℝ) =
      -(Real.pi * Real.exp (633 / 400 : ℝ) - (253 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (253 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (253 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1265_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7359126969459843 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1265_endpointUpper :
    hpThetaJensenKernelEndpointUpper (253 / 320 : ℝ) (633 / 800 : ℝ) ≤ (2929203 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (633 / 400 : ℝ)) (152904736334997829 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (633 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1265_product_upper
  have hD : (14435204424829647 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (253 / 160 : ℝ) - (633 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1265_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1265_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (253 / 160 : ℝ) - (633 / 1600 : ℝ)) ≤
      (1 / (14435204424829647 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14435204424829647 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((633 / 1600 : ℝ) - Real.pi * Real.exp (253 / 160 : ℝ)) ≤
      (2 / (14435204424829647 / 5000000000 : ℝ) : ℝ) := by
    rw [show (633 / 1600 : ℝ) - Real.pi * Real.exp (253 / 160 : ℝ) =
      -(Real.pi * Real.exp (253 / 160 : ℝ) - (633 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (152904736334997829 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (152904736334997829 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1265_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (253 / 320 : ℝ) (633 / 800 : ℝ)) :
    (2857779 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2929203 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1265_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1265_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1266_leftExp :
    (973421677 / 200000000 : ℝ) ≤ Real.exp (633 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (633 / 400 : ℝ) (1050696339669 / 1000000000000 : ℝ)
    (973421677 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1266_rightExp :
    Real.exp (1267 / 800 : ℝ) ≤ (48731960747 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1267 / 800 : ℝ) (1050737383297 / 1000000000000 : ℝ)
    (48731960747 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1266_denomUpper :
    Real.exp (149139736759049971 / 10000000000000000 : ℝ) ≤ (29995525212279993 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (149139736759049971 / 10000000000000000 : ℝ) (49803290371
    / 31250000000 : ℝ) (29995525212279993 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1266_denomLower :
    (29417972599072457 / 10000000000 : ℝ) ≤ Real.exp (372363281636223 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (372363281636223 / 25000000000000 : ℝ) (796368644977 /
    500000000000 : ℝ) (29417972599072457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1266_product_lower :
    (382261719136223 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (633 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1266_leftExp
    (by norm_num : (0 : ℝ) ≤ (973421677 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1266_product_upper :
    Real.pi * Real.exp (1267 / 800 : ℝ) ≤ (153095986759049971 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1266_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1266_endpointLower :
    (1124769 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (633 / 800 : ℝ) (1267 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (382261719136223 / 25000000000000 : ℝ) (Real.pi * Real.exp (633 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1266_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1267 / 800 : ℝ) - (633 / 1600 : ℝ)) ≤
      (29995525212279993 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1266_denomUpper
    linarith [hpThetaJensenCell1266_product_upper]
  have hi : (1 / (29995525212279993 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1267 / 800 : ℝ) - (633 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29995525212279993 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29995525212279993 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((633 / 1600 : ℝ) - Real.pi * Real.exp (1267 / 800 : ℝ)) := by
    rw [show (633 / 1600 : ℝ) - Real.pi * Real.exp (1267 / 800 : ℝ) =
      -(Real.pi * Real.exp (1267 / 800 : ℝ) - (633 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (633 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (633 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1266_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29995525212279993 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1266_endpointUpper :
    hpThetaJensenKernelEndpointUpper (633 / 800 : ℝ) (1267 / 1600 : ℝ) ≤ (720567 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1267 / 800 : ℝ)) (153095986759049971 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1267 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1266_product_upper
  have hD : (29417972599072457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (633 / 400 : ℝ) - (1267 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1266_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1266_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (633 / 400 : ℝ) - (1267 / 3200 : ℝ)) ≤
      (1 / (29417972599072457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29417972599072457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1267 / 3200 : ℝ) - Real.pi * Real.exp (633 / 400 : ℝ)) ≤
      (2 / (29417972599072457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1267 / 3200 : ℝ) - Real.pi * Real.exp (633 / 400 : ℝ) =
      -(Real.pi * Real.exp (633 / 400 : ℝ) - (1267 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (153095986759049971 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (153095986759049971 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1266_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (633 / 800 : ℝ) (1267 / 1600 : ℝ)) :
    (1124769 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (720567 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1266_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1266_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1267_leftExp :
    (9746392149 / 2000000000 : ℝ) ≤ Real.exp (1267 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1267 / 800 : ℝ) (8208885807 / 7812500000 : ℝ)
    (9746392149 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1267_rightExp :
    Real.exp (317 / 200 : ℝ) ≤ (24396456893 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (317 / 200 : ℝ) (65673651783 / 62500000000 : ℝ)
    (24396456893 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1267_denomUpper :
    Real.exp (74664050699850549 / 5000000000000000 : ℝ) ≤ (15282944903378071 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (74664050699850549 / 5000000000000000 : ℝ) (797321842961
    / 500000000000 : ℝ) (15282944903378071 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1267_denomLower :
    (14988318882009877 / 5000000000 : ℝ) ≤ Real.exp (3728335950520151 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3728335950520151 / 250000000000000 : ℝ) (159367392239 /
    100000000000 : ℝ) (14988318882009877 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1267_product_lower :
    (3827398450520151 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1267 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1267_leftExp
    (by norm_num : (0 : ℝ) ≤ (9746392149 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1267_product_upper :
    Real.pi * Real.exp (317 / 200 : ℝ) ≤ (76643738199850549 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1267_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1267_endpointLower :
    (5533469 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1267 / 1600 : ℝ) (317 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3827398450520151 / 250000000000000 : ℝ) (Real.pi * Real.exp (1267 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1267_product_lower
  have hD : Real.exp (Real.pi * Real.exp (317 / 200 : ℝ) - (1267 / 3200 : ℝ)) ≤
      (15282944903378071 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1267_denomUpper
    linarith [hpThetaJensenCell1267_product_upper]
  have hi : (1 / (15282944903378071 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (317 / 200 : ℝ) - (1267 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15282944903378071 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15282944903378071 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1267 / 3200 : ℝ) - Real.pi * Real.exp (317 / 200 : ℝ)) := by
    rw [show (1267 / 3200 : ℝ) - Real.pi * Real.exp (317 / 200 : ℝ) =
      -(Real.pi * Real.exp (317 / 200 : ℝ) - (1267 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1267 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1267 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1267_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15282944903378071 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1267_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1267 / 1600 : ℝ) (317 / 400 : ℝ) ≤ (2836017 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (317 / 200 : ℝ)) (76643738199850549 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (317 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1267_product_upper
  have hD : (14988318882009877 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1267 / 800 : ℝ) - (317 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1267_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1267_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1267 / 800 : ℝ) - (317 / 800 : ℝ)) ≤
      (1 / (14988318882009877 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14988318882009877 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((317 / 800 : ℝ) - Real.pi * Real.exp (1267 / 800 : ℝ)) ≤
      (2 / (14988318882009877 / 5000000000 : ℝ) : ℝ) := by
    rw [show (317 / 800 : ℝ) - Real.pi * Real.exp (1267 / 800 : ℝ) =
      -(Real.pi * Real.exp (1267 / 800 : ℝ) - (317 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (76643738199850549 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (76643738199850549 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1267_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1267 / 1600 : ℝ) (317 / 400 : ℝ)) :
    (5533469 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2836017 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1267_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1267_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1268_leftExp :
    (6099114223 / 1250000000 : ℝ) ≤ Real.exp (317 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (317 / 200 : ℝ) (1050778428527 / 1000000000000 : ℝ)
    (6099114223 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1268_rightExp :
    Real.exp (1269 / 800 : ℝ) ≤ (6106742883 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1269 / 800 : ℝ) (525409737681 / 500000000000 : ℝ)
    (6106742883 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1268_denomUpper :
    Real.exp (18689588194032619 / 1250000000000000 : ℝ) ≤ (15573922948478061 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (18689588194032619 / 1250000000000000 : ℝ) (398895956691
    / 250000000000 : ℝ) (15573922948478061 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1268_denomLower :
    (30546643027977017 / 10000000000 : ℝ) ≤ Real.exp (2333153165632877 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2333153165632877 / 156250000000000 : ℝ) (797306148833 /
    500000000000 : ℝ) (30546643027977017 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1268_product_lower :
    (2395116056257877 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (317 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1268_leftExp
    (by norm_num : (0 : ℝ) ≤ (6099114223 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1268_product_upper :
    Real.pi * Real.exp (1269 / 800 : ℝ) ≤ (19184900694032619 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1268_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1268_endpointLower :
    (2722207 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (317 / 400 : ℝ) (1269 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2395116056257877 / 156250000000000 : ℝ) (Real.pi * Real.exp (317 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1268_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1269 / 800 : ℝ) - (317 / 800 : ℝ)) ≤
      (15573922948478061 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1268_denomUpper
    linarith [hpThetaJensenCell1268_product_upper]
  have hi : (1 / (15573922948478061 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1269 / 800 : ℝ) - (317 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15573922948478061 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15573922948478061 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((317 / 800 : ℝ) - Real.pi * Real.exp (1269 / 800 : ℝ)) := by
    rw [show (317 / 800 : ℝ) - Real.pi * Real.exp (1269 / 800 : ℝ) =
      -(Real.pi * Real.exp (1269 / 800 : ℝ) - (317 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (317 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (317 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1268_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15573922948478061 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1268_endpointUpper :
    hpThetaJensenKernelEndpointUpper (317 / 400 : ℝ) (1269 / 1600 : ℝ) ≤ (2790441 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1269 / 800 : ℝ)) (19184900694032619 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1269 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1268_product_upper
  have hD : (30546643027977017 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (317 / 200 : ℝ) - (1269 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1268_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1268_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (317 / 200 : ℝ) - (1269 / 3200 : ℝ)) ≤
      (1 / (30546643027977017 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (30546643027977017 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1269 / 3200 : ℝ) - Real.pi * Real.exp (317 / 200 : ℝ)) ≤
      (2 / (30546643027977017 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1269 / 3200 : ℝ) - Real.pi * Real.exp (317 / 200 : ℝ) =
      -(Real.pi * Real.exp (317 / 200 : ℝ) - (1269 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19184900694032619 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (19184900694032619 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1268_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (317 / 400 : ℝ) (1269 / 1600 : ℝ)) :
    (2722207 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2790441 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1268_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1268_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1269_leftExp :
    (48853943061 / 10000000000 : ℝ) ≤ Real.exp (1269 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1269 / 800 : ℝ) (1050819475361 / 1000000000000 : ℝ)
    (48853943061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1269_rightExp :
    Real.exp (127 / 80 : ℝ) ≤ (12228762169 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (127 / 80 : ℝ) (5254302619 / 5000000000 : ℝ)
    (12228762169 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1269_denomUpper :
    Real.exp (37426387378795217 / 2500000000000000 : ℝ) ≤ (7935410817243327 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (37426387378795217 / 2500000000000000 : ℝ) (798262859163
    / 500000000000 : ℝ) (7935410817243327 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1269_denomLower :
    (15564116235773747 / 5000000000 : ℝ) ≤ Real.exp (18688800836111639 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (18688800836111639 / 1250000000000000 : ℝ) (1595552419683
    / 1000000000000 : ℝ) (15564116235773747 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1269_product_lower :
    (19184894586111639 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1269 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1269_leftExp
    (by norm_num : (0 : ℝ) ≤ (48853943061 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1269_product_upper :
    Real.pi * Real.exp (127 / 80 : ℝ) ≤ (38417793628795217 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1269_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1269_endpointLower :
    (5356663 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1269 / 1600 : ℝ) (127 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (19184894586111639 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1269 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1269_product_lower
  have hD : Real.exp (Real.pi * Real.exp (127 / 80 : ℝ) - (1269 / 3200 : ℝ)) ≤
      (7935410817243327 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1269_denomUpper
    linarith [hpThetaJensenCell1269_product_upper]
  have hi : (1 / (7935410817243327 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (127 / 80 : ℝ) - (1269 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7935410817243327 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7935410817243327 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1269 / 3200 : ℝ) - Real.pi * Real.exp (127 / 80 : ℝ)) := by
    rw [show (1269 / 3200 : ℝ) - Real.pi * Real.exp (127 / 80 : ℝ) =
      -(Real.pi * Real.exp (127 / 80 : ℝ) - (1269 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1269 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1269 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1269_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7935410817243327 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1269_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1269 / 1600 : ℝ) (127 / 160 : ℝ) ≤ (5491063 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (127 / 80 : ℝ)) (38417793628795217 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (127 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1269_product_upper
  have hD : (15564116235773747 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1269 / 800 : ℝ) - (127 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1269_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1269_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1269 / 800 : ℝ) - (127 / 320 : ℝ)) ≤
      (1 / (15564116235773747 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15564116235773747 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((127 / 320 : ℝ) - Real.pi * Real.exp (1269 / 800 : ℝ)) ≤
      (2 / (15564116235773747 / 5000000000 : ℝ) : ℝ) := by
    rw [show (127 / 320 : ℝ) - Real.pi * Real.exp (1269 / 800 : ℝ) =
      -(Real.pi * Real.exp (1269 / 800 : ℝ) - (127 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38417793628795217 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (38417793628795217 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1269_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1269 / 1600 : ℝ) (127 / 160 : ℝ)) :
    (5356663 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5491063 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1269_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1269_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1270_leftExp :
    (24457524337 / 5000000000 : ℝ) ≤ Real.exp (127 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (127 / 80 : ℝ) (1050860523799 / 1000000000000 : ℝ)
    (24457524337 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1270_rightExp :
    Real.exp (1271 / 800 : ℝ) ≤ (24488115359 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1271 / 800 : ℝ) (1050901573841 / 1000000000000 : ℝ)
    (24488115359 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1270_denomUpper :
    Real.exp (74947316795026887 / 5000000000000000 : ℝ) ≤ (6469507477759213 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (74947316795026887 / 5000000000000000 : ℝ) (1597469364557
    / 1000000000000 : ℝ) (6469507477759213 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1270_denomLower :
    (31721655752059891 / 10000000000 : ℝ) ≤ Real.exp (9356203162115563 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9356203162115563 / 625000000000000 : ℝ) (319298858483 /
    200000000000 : ℝ) (31721655752059891 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1270_product_lower :
    (9604445349615563 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (127 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1270_leftExp
    (by norm_num : (0 : ℝ) ≤ (24457524337 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1270_product_upper :
    Real.pi * Real.exp (1271 / 800 : ℝ) ≤ (76931691795026887 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1270_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1270_endpointLower :
    (5270199 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (127 / 160 : ℝ) (1271 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9604445349615563 / 625000000000000 : ℝ) (Real.pi * Real.exp (127 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1270_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1271 / 800 : ℝ) - (127 / 320 : ℝ)) ≤
      (6469507477759213 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1270_denomUpper
    linarith [hpThetaJensenCell1270_product_upper]
  have hi : (1 / (6469507477759213 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1271 / 800 : ℝ) - (127 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6469507477759213 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6469507477759213 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((127 / 320 : ℝ) - Real.pi * Real.exp (1271 / 800 : ℝ)) := by
    rw [show (127 / 320 : ℝ) - Real.pi * Real.exp (1271 / 800 : ℝ) =
      -(Real.pi * Real.exp (1271 / 800 : ℝ) - (127 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (127 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (127 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1270_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6469507477759213 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1270_endpointUpper :
    hpThetaJensenKernelEndpointUpper (127 / 160 : ℝ) (1271 / 1600 : ℝ) ≤ (2701279 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1271 / 800 : ℝ)) (76931691795026887 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1271 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1270_product_upper
  have hD : (31721655752059891 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (127 / 80 : ℝ) - (1271 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1270_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1270_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (127 / 80 : ℝ) - (1271 / 3200 : ℝ)) ≤
      (1 / (31721655752059891 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31721655752059891 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1271 / 3200 : ℝ) - Real.pi * Real.exp (127 / 80 : ℝ)) ≤
      (2 / (31721655752059891 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1271 / 3200 : ℝ) - Real.pi * Real.exp (127 / 80 : ℝ) =
      -(Real.pi * Real.exp (127 / 80 : ℝ) - (1271 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (76931691795026887 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (76931691795026887 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1270_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (127 / 160 : ℝ) (1271 / 1600 : ℝ)) :
    (5270199 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2701279 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1270_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1270_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1271_leftExp :
    (12244057679 / 2500000000 : ℝ) ≤ Real.exp (1271 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1271 / 800 : ℝ) (13136269673 / 12500000000 : ℝ)
    (12244057679 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1271_rightExp :
    Real.exp (159 / 100 : ℝ) ≤ (12259372321 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (159 / 100 : ℝ) (210188525097 / 200000000000 : ℝ)
    (12259372321 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1271_denomUpper :
    Real.exp (37520989518047353 / 2500000000000000 : ℝ) ≤ (32965789511008557 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (37520989518047353 / 2500000000000000 : ℝ) (799207384693
    / 500000000000 : ℝ) (32965789511008557 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1271_denomLower :
    (1616358407318493 / 500000000 : ℝ) ≤ Real.exp (4684010456485621 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4684010456485621 / 312500000000000 : ℝ) (798718959883 /
    500000000000 : ℝ) (1616358407318493 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1271_product_lower :
    (4808229206485621 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1271 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1271_leftExp
    (by norm_num : (0 : ℝ) ≤ (12244057679 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1271_product_upper :
    Real.pi * Real.exp (159 / 100 : ℝ) ≤ (38513958268047353 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1271_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1271_endpointLower :
    (1037001 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1271 / 1600 : ℝ) (159 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4808229206485621 / 312500000000000 : ℝ) (Real.pi * Real.exp (1271 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1271_product_lower
  have hD : Real.exp (Real.pi * Real.exp (159 / 100 : ℝ) - (1271 / 3200 : ℝ)) ≤
      (32965789511008557 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1271_denomUpper
    linarith [hpThetaJensenCell1271_product_upper]
  have hi : (1 / (32965789511008557 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (159 / 100 : ℝ) - (1271 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32965789511008557 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32965789511008557 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1271 / 3200 : ℝ) - Real.pi * Real.exp (159 / 100 : ℝ)) := by
    rw [show (1271 / 3200 : ℝ) - Real.pi * Real.exp (159 / 100 : ℝ) =
      -(Real.pi * Real.exp (159 / 100 : ℝ) - (1271 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1271 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1271 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1271_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32965789511008557 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1271_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1271 / 1600 : ℝ) (159 / 200 : ℝ) ≤ (5315351 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (159 / 100 : ℝ)) (38513958268047353 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (159 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1271_product_upper
  have hD : (1616358407318493 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1271 / 800 : ℝ) - (159 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1271_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1271_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1271 / 800 : ℝ) - (159 / 400 : ℝ)) ≤
      (1 / (1616358407318493 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1616358407318493 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((159 / 400 : ℝ) - Real.pi * Real.exp (1271 / 800 : ℝ)) ≤
      (2 / (1616358407318493 / 500000000 : ℝ) : ℝ) := by
    rw [show (159 / 400 : ℝ) - Real.pi * Real.exp (1271 / 800 : ℝ) =
      -(Real.pi * Real.exp (1271 / 800 : ℝ) - (159 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38513958268047353 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (38513958268047353 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1271_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1271 / 1600 : ℝ) (159 / 200 : ℝ)) :
    (1037001 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5315351 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1271_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1271_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1272_leftExp :
    (24518744641 / 5000000000 : ℝ) ≤ Real.exp (159 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (159 / 100 : ℝ) (262735656371 / 250000000000 : ℝ)
    (24518744641 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1272_rightExp :
    Real.exp (1273 / 800 : ℝ) ≤ (6137353059 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1273 / 800 : ℝ) (1050983678733 / 1000000000000 : ℝ)
    (6137353059 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1272_denomUpper :
    Real.exp (18784190408682987 / 1250000000000000 : ℝ) ≤ (839916671948917 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18784190408682987 / 1250000000000000 : ℝ) (319872387363
    / 200000000000 : ℝ) (839916671948917 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1272_denomLower :
    (32945030753738767 / 10000000000 : ℝ) ≤ Real.exp (9379853689276059 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (9379853689276059 / 625000000000000 : ℝ) (19979791321 /
    12500000000 : ℝ) (32945030753738767 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1272_product_lower :
    (9628486501776059 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (159 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1272_leftExp
    (by norm_num : (0 : ℝ) ≤ (24518744641 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1272_product_upper :
    Real.pi * Real.exp (1273 / 800 : ℝ) ≤ (19281065408682987 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1272_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1272_endpointLower :
    (1020213 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (159 / 200 : ℝ) (1273 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9628486501776059 / 625000000000000 : ℝ) (Real.pi * Real.exp (159 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1272_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1273 / 800 : ℝ) - (159 / 400 : ℝ)) ≤
      (839916671948917 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1272_denomUpper
    linarith [hpThetaJensenCell1272_product_upper]
  have hi : (1 / (839916671948917 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1273 / 800 : ℝ) - (159 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (839916671948917 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (839916671948917 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((159 / 400 : ℝ) - Real.pi * Real.exp (1273 / 800 : ℝ)) := by
    rw [show (159 / 400 : ℝ) - Real.pi * Real.exp (1273 / 800 : ℝ) =
      -(Real.pi * Real.exp (1273 / 800 : ℝ) - (159 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (159 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (159 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1272_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (839916671948917 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1272_endpointUpper :
    hpThetaJensenKernelEndpointUpper (159 / 200 : ℝ) (1273 / 1600 : ℝ) ≤ (209177 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1273 / 800 : ℝ)) (19281065408682987 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1273 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1272_product_upper
  have hD : (32945030753738767 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (159 / 100 : ℝ) - (1273 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1272_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1272_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (159 / 100 : ℝ) - (1273 / 3200 : ℝ)) ≤
      (1 / (32945030753738767 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (32945030753738767 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1273 / 3200 : ℝ) - Real.pi * Real.exp (159 / 100 : ℝ)) ≤
      (2 / (32945030753738767 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1273 / 3200 : ℝ) - Real.pi * Real.exp (159 / 100 : ℝ) =
      -(Real.pi * Real.exp (159 / 100 : ℝ) - (1273 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19281065408682987 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (19281065408682987 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1272_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (159 / 200 : ℝ) (1273 / 1600 : ℝ)) :
    (1020213 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (209177 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1272_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1272_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1273_leftExp :
    (4909882447 / 1000000000 : ℝ) ≤ Real.exp (1273 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1273 / 800 : ℝ) (262745919683 / 250000000000 : ℝ)
    (4909882447 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1273_rightExp :
    Real.exp (637 / 400 : ℝ) ≤ (24580118189 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (637 / 400 : ℝ) (210204946717 / 200000000000 : ℝ)
    (24580118189 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1273_denomUpper :
    Real.exp (75231664741735077 / 5000000000000000 : ℝ) ≤ (34240442798440419 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (75231664741735077 / 5000000000000000 : ℝ) (1600310870821
    / 1000000000000 : ℝ) (34240442798440419 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1273_denomLower :
    (33575510647381121 / 10000000000 : ℝ) ≤ Real.exp (1878340302054453 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1878340302054453 / 125000000000000 : ℝ) (799665227079 /
    500000000000 : ℝ) (33575510647381121 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1273_product_lower :
    (1928105927054453 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1273 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1273_leftExp
    (by norm_num : (0 : ℝ) ≤ (4909882447 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1273_product_upper :
    Real.pi * Real.exp (637 / 400 : ℝ) ≤ (77220727241735077 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1273_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1273_endpointLower :
    (5018361 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1273 / 1600 : ℝ) (637 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1928105927054453 / 125000000000000 : ℝ) (Real.pi * Real.exp (1273 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1273_product_lower
  have hD : Real.exp (Real.pi * Real.exp (637 / 400 : ℝ) - (1273 / 3200 : ℝ)) ≤
      (34240442798440419 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1273_denomUpper
    linarith [hpThetaJensenCell1273_product_upper]
  have hi : (1 / (34240442798440419 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (637 / 400 : ℝ) - (1273 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (34240442798440419 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (34240442798440419 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1273 / 3200 : ℝ) - Real.pi * Real.exp (637 / 400 : ℝ)) := by
    rw [show (1273 / 3200 : ℝ) - Real.pi * Real.exp (637 / 400 : ℝ) =
      -(Real.pi * Real.exp (637 / 400 : ℝ) - (1273 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1273 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1273 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1273_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (34240442798440419 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1273_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1273 / 1600 : ℝ) (637 / 800 : ℝ) ≤ (5144763 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (637 / 400 : ℝ)) (77220727241735077 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (637 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1273_product_upper
  have hD : (33575510647381121 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1273 / 800 : ℝ) - (637 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1273_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1273_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1273 / 800 : ℝ) - (637 / 1600 : ℝ)) ≤
      (1 / (33575510647381121 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (33575510647381121 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((637 / 1600 : ℝ) - Real.pi * Real.exp (1273 / 800 : ℝ)) ≤
      (2 / (33575510647381121 / 10000000000 : ℝ) : ℝ) := by
    rw [show (637 / 1600 : ℝ) - Real.pi * Real.exp (1273 / 800 : ℝ) =
      -(Real.pi * Real.exp (1273 / 800 : ℝ) - (637 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77220727241735077 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (77220727241735077 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1273_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1273 / 1600 : ℝ) (637 / 800 : ℝ)) :
    (5018361 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5144763 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1273_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1273_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1274_leftExp :
    (393281891 / 80000000 : ℝ) ≤ Real.exp (637 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (637 / 400 : ℝ) (65689045849 / 62500000000 : ℝ)
    (393281891 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1274_rightExp :
    Real.exp (51 / 32 : ℝ) ≤ (6152715637 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 32 : ℝ) (1051065790041 / 1000000000000 : ℝ)
    (6152715637 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1274_denomUpper :
    Real.exp (18831672126189741 / 1250000000000000 : ℝ) ≤ (34897396793828543 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (18831672126189741 / 1250000000000000 : ℝ) (5003942423 /
    3125000000 : ℝ) (34897396793828543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1274_denomLower :
    (34218880953512959 / 10000000000 : ℝ) ≤ Real.exp (150457030313809 / 10000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (150457030313809 / 10000000000000 : ℝ) (800139684581 /
    500000000000 : ℝ) (34218880953512959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1274_product_lower :
    (154441405313809 / 10000000000000 : ℝ) ≤ Real.pi * Real.exp (637 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1274_leftExp
    (by norm_num : (0 : ℝ) ≤ (393281891 / 80000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1274_product_upper :
    Real.pi * Real.exp (51 / 32 : ℝ) ≤ (19329328376189741 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1274_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1274_endpointLower :
    (2468439 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (637 / 800 : ℝ) (51 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (154441405313809 / 10000000000000 : ℝ) (Real.pi * Real.exp (637 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1274_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 32 : ℝ) - (637 / 1600 : ℝ)) ≤
      (34897396793828543 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1274_denomUpper
    linarith [hpThetaJensenCell1274_product_upper]
  have hi : (1 / (34897396793828543 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 32 : ℝ) - (637 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (34897396793828543 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (34897396793828543 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((637 / 1600 : ℝ) - Real.pi * Real.exp (51 / 32 : ℝ)) := by
    rw [show (637 / 1600 : ℝ) - Real.pi * Real.exp (51 / 32 : ℝ) =
      -(Real.pi * Real.exp (51 / 32 : ℝ) - (637 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (637 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (637 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1274_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (34897396793828543 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1274_endpointUpper :
    hpThetaJensenKernelEndpointUpper (637 / 800 : ℝ) (51 / 64 : ℝ) ≤ (101227 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 32 : ℝ)) (19329328376189741 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1274_product_upper
  have hD : (34218880953512959 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (637 / 400 : ℝ) - (51 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1274_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1274_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (637 / 400 : ℝ) - (51 / 128 : ℝ)) ≤
      (1 / (34218880953512959 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (34218880953512959 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 128 : ℝ) - Real.pi * Real.exp (637 / 400 : ℝ)) ≤
      (2 / (34218880953512959 / 10000000000 : ℝ) : ℝ) := by
    rw [show (51 / 128 : ℝ) - Real.pi * Real.exp (637 / 400 : ℝ) =
      -(Real.pi * Real.exp (637 / 400 : ℝ) - (51 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19329328376189741 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (19329328376189741 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1274_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (637 / 800 : ℝ) (51 / 64 : ℝ)) :
    (2468439 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (101227 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1274_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1274_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1275_leftExp :
    (24610862547 / 5000000000 : ℝ) ≤ Real.exp (51 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 32 : ℝ) (26276644751 / 25000000000 : ℝ)
    (24610862547 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1275_rightExp :
    Real.exp (319 / 200 : ℝ) ≤ (49283290723 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (319 / 200 : ℝ) (10511068481 / 10000000000 : ℝ)
    (49283290723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1275_denomUpper :
    Real.exp (150843666152341739 / 10000000000000000 : ℝ) ≤ (8891953699960389 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (150843666152341739 / 10000000000000000 : ℝ)
    (400553513611 / 250000000000 : ℝ) (8891953699960389 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1275_denomLower :
    (4359427631181499 / 1250000000 : ℝ) ≤ Real.exp (9415442361344353 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9415442361344353 / 625000000000000 : ℝ) (320246010939 /
    200000000000 : ℝ) (4359427631181499 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1275_product_lower :
    (9664661111344353 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1275_leftExp
    (by norm_num : (0 : ℝ) ≤ (24610862547 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1275_product_upper :
    Real.pi * Real.exp (319 / 200 : ℝ) ≤ (154828041152341739 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1275_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1275_endpointLower :
    (24283 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 64 : ℝ) (319 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9664661111344353 / 625000000000000 : ℝ) (Real.pi * Real.exp (51 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1275_product_lower
  have hD : Real.exp (Real.pi * Real.exp (319 / 200 : ℝ) - (51 / 128 : ℝ)) ≤
      (8891953699960389 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1275_denomUpper
    linarith [hpThetaJensenCell1275_product_upper]
  have hi : (1 / (8891953699960389 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (319 / 200 : ℝ) - (51 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8891953699960389 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8891953699960389 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 128 : ℝ) - Real.pi * Real.exp (319 / 200 : ℝ)) := by
    rw [show (51 / 128 : ℝ) - Real.pi * Real.exp (319 / 200 : ℝ) =
      -(Real.pi * Real.exp (319 / 200 : ℝ) - (51 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1275_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8891953699960389 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1275_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 64 : ℝ) (319 / 400 : ℝ) ≤ (4979167 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (319 / 200 : ℝ)) (154828041152341739 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (319 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1275_product_upper
  have hD : (4359427631181499 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 32 : ℝ) - (319 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1275_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1275_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 32 : ℝ) - (319 / 800 : ℝ)) ≤
      (1 / (4359427631181499 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4359427631181499 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((319 / 800 : ℝ) - Real.pi * Real.exp (51 / 32 : ℝ)) ≤
      (2 / (4359427631181499 / 1250000000 : ℝ) : ℝ) := by
    rw [show (319 / 800 : ℝ) - Real.pi * Real.exp (51 / 32 : ℝ) =
      -(Real.pi * Real.exp (51 / 32 : ℝ) - (319 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (154828041152341739 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (154828041152341739 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1275_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 64 : ℝ) (319 / 400 : ℝ)) :
    (24283 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4979167 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1275_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1275_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1276_leftExp :
    (308020567 / 62500000 : ℝ) ≤ Real.exp (319 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (319 / 200 : ℝ) (1051106848099 / 1000000000000 : ℝ)
    (308020567 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1276_rightExp :
    Real.exp (1277 / 800 : ℝ) ≤ (24672466677 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1277 / 800 : ℝ) (1051147907763 / 1000000000000 : ℝ)
    (24672466677 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1276_denomUpper :
    Real.exp (75517098605196461 / 5000000000000000 : ℝ) ≤ (36251989265168779 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (75517098605196461 / 5000000000000000 : ℝ) (801584156031
    / 500000000000 : ℝ) (36251989265168779 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1276_denomLower :
    (35545416646436833 / 10000000000 : ℝ) ≤ Real.exp (117841692859083 / 7812500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (117841692859083 / 7812500000000 : ℝ) (320436502941 /
    200000000000 : ℝ) (35545416646436833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1276_product_lower :
    (120959368640333 / 7812500000000 : ℝ) ≤ Real.pi * Real.exp (319 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1276_leftExp
    (by norm_num : (0 : ℝ) ≤ (308020567 / 62500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1276_product_upper :
    Real.pi * Real.exp (1277 / 800 : ℝ) ≤ (77510848605196461 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1276_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1276_endpointLower :
    (4777511 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (319 / 400 : ℝ) (1277 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (120959368640333 / 7812500000000 : ℝ) (Real.pi * Real.exp (319 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1276_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1277 / 800 : ℝ) - (319 / 800 : ℝ)) ≤
      (36251989265168779 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1276_denomUpper
    linarith [hpThetaJensenCell1276_product_upper]
  have hi : (1 / (36251989265168779 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1277 / 800 : ℝ) - (319 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (36251989265168779 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (36251989265168779 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((319 / 800 : ℝ) - Real.pi * Real.exp (1277 / 800 : ℝ)) := by
    rw [show (319 / 800 : ℝ) - Real.pi * Real.exp (1277 / 800 : ℝ) =
      -(Real.pi * Real.exp (1277 / 800 : ℝ) - (319 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (319 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (319 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1276_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (36251989265168779 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1276_endpointUpper :
    hpThetaJensenKernelEndpointUpper (319 / 400 : ℝ) (1277 / 1600 : ℝ) ≤ (24491 / 50000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1277 / 800 : ℝ)) (77510848605196461 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1277 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1276_product_upper
  have hD : (35545416646436833 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (319 / 200 : ℝ) - (1277 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1276_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1276_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (319 / 200 : ℝ) - (1277 / 3200 : ℝ)) ≤
      (1 / (35545416646436833 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35545416646436833 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1277 / 3200 : ℝ) - Real.pi * Real.exp (319 / 200 : ℝ)) ≤
      (2 / (35545416646436833 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1277 / 3200 : ℝ) - Real.pi * Real.exp (319 / 200 : ℝ) =
      -(Real.pi * Real.exp (319 / 200 : ℝ) - (1277 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77510848605196461 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (77510848605196461 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1276_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (319 / 400 : ℝ) (1277 / 1600 : ℝ)) :
    (4777511 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (24491 / 50000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1276_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1276_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1277_leftExp :
    (6168116669 / 1250000000 : ℝ) ≤ Real.exp (1277 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1277 / 800 : ℝ) (525573953881 / 500000000000 : ℝ)
    (6168116669 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1277_rightExp :
    Real.exp (639 / 400 : ℝ) ≤ (1543957909 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (639 / 400 : ℝ) (105118896903 / 100000000000 : ℝ)
    (1543957909 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1277_denomUpper :
    Real.exp (4725780327959037 / 312500000000000 : ℝ) ≤ (7390043875335861 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4725780327959037 / 312500000000000 : ℝ) (401031088069 /
    250000000000 : ℝ) (7390043875335861 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1277_denomLower :
    (18114580027260491 / 5000000000 : ℝ) ≤ Real.exp (2359810904049631 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2359810904049631 / 156250000000000 : ℝ) (801568376623 /
    500000000000 : ℝ) (18114580027260491 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1277_product_lower :
    (2422213247799631 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1277 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1277_leftExp
    (by norm_num : (0 : ℝ) ≤ (6168116669 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1277_product_upper :
    Real.pi * Real.exp (639 / 400 : ℝ) ≤ (4850487359209037 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1277_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1277_endpointLower :
    (939919 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1277 / 1600 : ℝ) (639 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2422213247799631 / 156250000000000 : ℝ) (Real.pi * Real.exp (1277 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1277_product_lower
  have hD : Real.exp (Real.pi * Real.exp (639 / 400 : ℝ) - (1277 / 3200 : ℝ)) ≤
      (7390043875335861 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1277_denomUpper
    linarith [hpThetaJensenCell1277_product_upper]
  have hi : (1 / (7390043875335861 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (639 / 400 : ℝ) - (1277 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7390043875335861 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7390043875335861 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1277 / 3200 : ℝ) - Real.pi * Real.exp (639 / 400 : ℝ)) := by
    rw [show (1277 / 3200 : ℝ) - Real.pi * Real.exp (639 / 400 : ℝ) =
      -(Real.pi * Real.exp (639 / 400 : ℝ) - (1277 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1277 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1277 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1277_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7390043875335861 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1277_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1277 / 1600 : ℝ) (639 / 800 : ℝ) ≤ (4818431 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (639 / 400 : ℝ)) (4850487359209037 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (639 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1277_product_upper
  have hD : (18114580027260491 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1277 / 800 : ℝ) - (639 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1277_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1277_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1277 / 800 : ℝ) - (639 / 1600 : ℝ)) ≤
      (1 / (18114580027260491 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18114580027260491 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((639 / 1600 : ℝ) - Real.pi * Real.exp (1277 / 800 : ℝ)) ≤
      (2 / (18114580027260491 / 5000000000 : ℝ) : ℝ) := by
    rw [show (639 / 1600 : ℝ) - Real.pi * Real.exp (1277 / 800 : ℝ) =
      -(Real.pi * Real.exp (1277 / 800 : ℝ) - (639 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4850487359209037 / 312500000000000 : ℝ) ^ 2 - 6 *
      (4850487359209037 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1277_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1277 / 1600 : ℝ) (639 / 800 : ℝ)) :
    (939919 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4818431 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1277_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1277_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1278_leftExp :
    (9881330617 / 2000000000 : ℝ) ≤ Real.exp (639 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (639 / 400 : ℝ) (1051188969029 / 1000000000000 : ℝ)
    (9881330617 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1278_rightExp :
    Real.exp (1279 / 800 : ℝ) ≤ (49468450019 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1279 / 800 : ℝ) (1051230031901 / 1000000000000 : ℝ)
    (49468450019 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1278_denomUpper :
    Real.exp (151415986300540267 / 10000000000000000 : ℝ) ≤ (37662811117642651 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (151415986300540267 / 10000000000000000 : ℝ)
    (1605082179079 / 1000000000000 : ℝ) (37662811117642651 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1278_denomLower :
    (36926950225383251 / 10000000000 : ℝ) ≤ Real.exp (3780466776965283 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3780466776965283 / 250000000000000 : ℝ) (320818554863 /
    200000000000 : ℝ) (36926950225383251 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1278_product_lower :
    (3880388651965283 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (639 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1278_leftExp
    (by norm_num : (0 : ℝ) ≤ (9881330617 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1278_product_upper :
    Real.pi * Real.exp (1279 / 800 : ℝ) ≤ (155409736300540267 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1278_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1278_endpointLower :
    (4622837 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (639 / 800 : ℝ) (1279 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3880388651965283 / 250000000000000 : ℝ) (Real.pi * Real.exp (639 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1278_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1279 / 800 : ℝ) - (639 / 1600 : ℝ)) ≤
      (37662811117642651 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1278_denomUpper
    linarith [hpThetaJensenCell1278_product_upper]
  have hi : (1 / (37662811117642651 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1279 / 800 : ℝ) - (639 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (37662811117642651 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (37662811117642651 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((639 / 1600 : ℝ) - Real.pi * Real.exp (1279 / 800 : ℝ)) := by
    rw [show (639 / 1600 : ℝ) - Real.pi * Real.exp (1279 / 800 : ℝ) =
      -(Real.pi * Real.exp (1279 / 800 : ℝ) - (639 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (639 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (639 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1278_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (37662811117642651 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1278_endpointUpper :
    hpThetaJensenKernelEndpointUpper (639 / 800 : ℝ) (1279 / 1600 : ℝ) ≤ (2369923 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1279 / 800 : ℝ)) (155409736300540267 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1279 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1278_product_upper
  have hD : (36926950225383251 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (639 / 400 : ℝ) - (1279 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1278_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1278_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (639 / 400 : ℝ) - (1279 / 3200 : ℝ)) ≤
      (1 / (36926950225383251 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (36926950225383251 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1279 / 3200 : ℝ) - Real.pi * Real.exp (639 / 400 : ℝ)) ≤
      (2 / (36926950225383251 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1279 / 3200 : ℝ) - Real.pi * Real.exp (639 / 400 : ℝ) =
      -(Real.pi * Real.exp (639 / 400 : ℝ) - (1279 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (155409736300540267 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (155409736300540267 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1278_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (639 / 800 : ℝ) (1279 / 1600 : ℝ)) :
    (4622837 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2369923 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1278_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1278_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1279_leftExp :
    (1545889063 / 312500000 : ℝ) ≤ Real.exp (1279 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1279 / 800 : ℝ) (10512300319 / 10000000000 : ℝ)
    (1545889063 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1279_rightExp :
    Real.exp (8 / 5 : ℝ) ≤ (24765162123 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8 / 5 : ℝ) (1051271096377 / 1000000000000 : ℝ)
    (24765162123 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1279_denomUpper :
    Real.exp (75803622469481939 / 5000000000000000 : ℝ) ≤ (38390077544678931 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (75803622469481939 / 5000000000000000 : ℝ) (1606041796549
    / 1000000000000 : ℝ) (38390077544678931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1279_denomLower :
    (18819546491669971 / 5000000000 : ℝ) ≤ Real.exp (591444089151037 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (591444089151037 / 39062500000000 : ℝ) (25078915343 /
    15625000000 : ℝ) (18819546491669971 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1279_product_lower :
    (607069089151037 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (1279 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1279_leftExp
    (by norm_num : (0 : ℝ) ≤ (1545889063 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1279_product_upper :
    Real.pi * Real.exp (8 / 5 : ℝ) ≤ (77802059969481939 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1279_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1279_endpointLower :
    (4547221 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1279 / 1600 : ℝ) (4 / 5 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (607069089151037 / 39062500000000 : ℝ) (Real.pi * Real.exp (1279 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1279_product_lower
  have hD : Real.exp (Real.pi * Real.exp (8 / 5 : ℝ) - (1279 / 3200 : ℝ)) ≤
      (38390077544678931 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1279_denomUpper
    linarith [hpThetaJensenCell1279_product_upper]
  have hi : (1 / (38390077544678931 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (8 / 5 : ℝ) - (1279 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38390077544678931 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38390077544678931 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1279 / 3200 : ℝ) - Real.pi * Real.exp (8 / 5 : ℝ)) := by
    rw [show (1279 / 3200 : ℝ) - Real.pi * Real.exp (8 / 5 : ℝ) =
      -(Real.pi * Real.exp (8 / 5 : ℝ) - (1279 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1279 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1279 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1279_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38390077544678931 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1279_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1279 / 1600 : ℝ) (4 / 5 : ℝ) ≤ (4662429 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (8 / 5 : ℝ)) (77802059969481939 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (4 / 5 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1279_product_upper
  have hD : (18819546491669971 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1279 / 800 : ℝ) - (2 / 5 : ℝ)) := by
    apply le_trans hpThetaJensenCell1279_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1279_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1279 / 800 : ℝ) - (2 / 5 : ℝ)) ≤
      (1 / (18819546491669971 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18819546491669971 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((2 / 5 : ℝ) - Real.pi * Real.exp (1279 / 800 : ℝ)) ≤
      (2 / (18819546491669971 / 5000000000 : ℝ) : ℝ) := by
    rw [show (2 / 5 : ℝ) - Real.pi * Real.exp (1279 / 800 : ℝ) =
      -(Real.pi * Real.exp (1279 / 800 : ℝ) - (2 / 5 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77802059969481939 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (77802059969481939 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1279_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1279 / 1600 : ℝ) (4 / 5 : ℝ)) :
    (4547221 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4662429 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1279_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1279_endpointUpper

def hpThetaJensenCellsBatch063Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3097411 / 5000000000 : ℝ)
  | 1 => (121923 / 200000000 : ℝ)
  | 2 => (2999453 / 5000000000 : ℝ)
  | 3 => (5903071 / 10000000000 : ℝ)
  | 4 => (1452157 / 2500000000 : ℝ)
  | 5 => (2857779 / 5000000000 : ℝ)
  | 6 => (1124769 / 2000000000 : ℝ)
  | 7 => (5533469 / 10000000000 : ℝ)
  | 8 => (2722207 / 5000000000 : ℝ)
  | 9 => (5356663 / 10000000000 : ℝ)
  | 10 => (5270199 / 10000000000 : ℝ)
  | 11 => (1037001 / 2000000000 : ℝ)
  | 12 => (1020213 / 2000000000 : ℝ)
  | 13 => (5018361 / 10000000000 : ℝ)
  | 14 => (2468439 / 5000000000 : ℝ)
  | 15 => (24283 / 50000000 : ℝ)
  | 16 => (4777511 / 10000000000 : ℝ)
  | 17 => (939919 / 2000000000 : ℝ)
  | 18 => (4622837 / 10000000000 : ℝ)
  | 19 => (4547221 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch063Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3174449 / 5000000000 : ℝ)
  | 1 => (6247919 / 10000000000 : ℝ)
  | 2 => (3074199 / 5000000000 : ℝ)
  | 3 => (3025159 / 5000000000 : ℝ)
  | 4 => (297683 / 500000000 : ℝ)
  | 5 => (2929203 / 5000000000 : ℝ)
  | 6 => (720567 / 1250000000 : ℝ)
  | 7 => (2836017 / 5000000000 : ℝ)
  | 8 => (2790441 / 5000000000 : ℝ)
  | 9 => (5491063 / 10000000000 : ℝ)
  | 10 => (2701279 / 5000000000 : ℝ)
  | 11 => (5315351 / 10000000000 : ℝ)
  | 12 => (209177 / 400000000 : ℝ)
  | 13 => (5144763 / 10000000000 : ℝ)
  | 14 => (101227 / 200000000 : ℝ)
  | 15 => (4979167 / 10000000000 : ℝ)
  | 16 => (24491 / 50000000 : ℝ)
  | 17 => (4818431 / 10000000000 : ℝ)
  | 18 => (2369923 / 5000000000 : ℝ)
  | 19 => (4662429 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch063_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch063Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch063Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1260_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1261_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1262_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1263_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1264_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1265_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1266_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1267_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1268_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1269_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1270_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1271_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1272_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1273_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1274_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1275_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1276_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1277_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1278_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1279_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper] at h ⊢
    exact h

end HodgeProofHP
