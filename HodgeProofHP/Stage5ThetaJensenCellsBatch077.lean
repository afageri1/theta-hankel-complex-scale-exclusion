import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1540_leftExp :
    (34275743329 / 5000000000 : ℝ) ≤ Real.exp (77 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 40 : ℝ) (265500617867 / 250000000000 : ℝ)
    (34275743329 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1540_rightExp :
    Real.exp (1541 / 800 : ℝ) ≤ (34318614799 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1541 / 800 : ℝ) (1062043956751 / 1000000000000 : ℝ)
    (34318614799 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1540_denomUpper :
    Real.exp (105408870022234807 / 5000000000000000 : ℝ) ≤ (7155963606896660633 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (105408870022234807 / 5000000000000000 : ℝ)
    (1932482484209 / 1000000000000 : ℝ) (7155963606896660633 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1540_denomLower :
    (2785421060514701873 / 2000000000 : ℝ) ≤ Real.exp (13159073567054971 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13159073567054971 / 625000000000000 : ℝ) (965418587547 /
    500000000000 : ℝ) (2785421060514701873 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1540_product_lower :
    (13460050129554971 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1540_leftExp
    (by norm_num : (0 : ℝ) ≤ (34275743329 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1540_product_upper :
    Real.pi * Real.exp (1541 / 800 : ℝ) ≤ (107815120022234807 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1540_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1540_endpointLower :
    (24119 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 80 : ℝ) (1541 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13460050129554971 / 625000000000000 : ℝ) (Real.pi * Real.exp (77 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1540_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1541 / 800 : ℝ) - (77 / 160 : ℝ)) ≤
      (7155963606896660633 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1540_denomUpper
    linarith [hpThetaJensenCell1540_product_upper]
  have hi : (1 / (7155963606896660633 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1541 / 800 : ℝ) - (77 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7155963606896660633 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7155963606896660633 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 160 : ℝ) - Real.pi * Real.exp (1541 / 800 : ℝ)) := by
    rw [show (77 / 160 : ℝ) - Real.pi * Real.exp (1541 / 800 : ℝ) =
      -(Real.pi * Real.exp (1541 / 800 : ℝ) - (77 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1540_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7155963606896660633 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1540_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 80 : ℝ) (1541 / 1600 : ℝ) ≤ (6229 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1541 / 800 : ℝ)) (107815120022234807 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1541 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1540_product_upper
  have hD : (2785421060514701873 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 40 : ℝ) - (1541 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1540_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1540_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 40 : ℝ) - (1541 / 3200 : ℝ)) ≤
      (1 / (2785421060514701873 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2785421060514701873 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1541 / 3200 : ℝ) - Real.pi * Real.exp (77 / 40 : ℝ)) ≤
      (2 / (2785421060514701873 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1541 / 3200 : ℝ) - Real.pi * Real.exp (77 / 40 : ℝ) =
      -(Real.pi * Real.exp (77 / 40 : ℝ) - (1541 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (107815120022234807 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (107815120022234807 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1540_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 80 : ℝ) (1541 / 1600 : ℝ)) :
    (24119 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6229 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1540_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1540_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1541_leftExp :
    (13727445919 / 2000000000 : ℝ) ≤ Real.exp (1541 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1541 / 800 : ℝ) (4248175827 / 4000000000 : ℝ)
    (13727445919 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1541_rightExp :
    Real.exp (771 / 400 : ℝ) ≤ (68723079779 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (771 / 400 : ℝ) (1062085443653 / 1000000000000 : ℝ)
    (68723079779 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1541_denomUpper :
    Real.exp (211084321372147947 / 10000000000000000 : ℝ) ≤ (7349293695253433251 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (211084321372147947 / 10000000000000000 : ℝ)
    (967046520837 / 500000000000 : ℝ) (7349293695253433251 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1541_denomLower :
    (7151443432607489609 / 5000000000 : ℝ) ≤ Real.exp (5270285534945381 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5270285534945381 / 250000000000000 : ℝ) (1932444326213 /
    1000000000000 : ℝ) (7151443432607489609 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1541_product_lower :
    (5390754284945381 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1541 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1541_leftExp
    (by norm_num : (0 : ℝ) ≤ (13727445919 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1541_product_upper :
    Real.pi * Real.exp (771 / 400 : ℝ) ≤ (215899946372147947 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1541_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1541_endpointLower :
    (11773 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1541 / 1600 : ℝ) (771 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5390754284945381 / 250000000000000 : ℝ) (Real.pi * Real.exp (1541 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1541_product_lower
  have hD : Real.exp (Real.pi * Real.exp (771 / 400 : ℝ) - (1541 / 3200 : ℝ)) ≤
      (7349293695253433251 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1541_denomUpper
    linarith [hpThetaJensenCell1541_product_upper]
  have hi : (1 / (7349293695253433251 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (771 / 400 : ℝ) - (1541 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7349293695253433251 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7349293695253433251 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1541 / 3200 : ℝ) - Real.pi * Real.exp (771 / 400 : ℝ)) := by
    rw [show (1541 / 3200 : ℝ) - Real.pi * Real.exp (771 / 400 : ℝ) =
      -(Real.pi * Real.exp (771 / 400 : ℝ) - (1541 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1541 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1541 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1541_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7349293695253433251 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1541_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1541 / 1600 : ℝ) (771 / 800 : ℝ) ≤ (973 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (771 / 400 : ℝ)) (215899946372147947 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (771 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1541_product_upper
  have hD : (7151443432607489609 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1541 / 800 : ℝ) - (771 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1541_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1541_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1541 / 800 : ℝ) - (771 / 1600 : ℝ)) ≤
      (1 / (7151443432607489609 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7151443432607489609 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((771 / 1600 : ℝ) - Real.pi * Real.exp (1541 / 800 : ℝ)) ≤
      (2 / (7151443432607489609 / 5000000000 : ℝ) : ℝ) := by
    rw [show (771 / 1600 : ℝ) - Real.pi * Real.exp (1541 / 800 : ℝ) =
      -(Real.pi * Real.exp (1541 / 800 : ℝ) - (771 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (215899946372147947 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (215899946372147947 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1541_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1541 / 1600 : ℝ) (771 / 800 : ℝ)) :
    (11773 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (973 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1541_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1541_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1542_leftExp :
    (2147596243 / 312500000 : ℝ) ≤ Real.exp (771 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (771 / 400 : ℝ) (265521360913 / 250000000000 : ℝ)
    (2147596243 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1542_rightExp :
    Real.exp (1543 / 800 : ℝ) ≤ (68809037341 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1543 / 800 : ℝ) (66382933261 / 62500000000 : ℝ)
    (68809037341 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1542_denomUpper :
    Real.exp (211351240047224213 / 10000000000000000 : ℝ) ≤ (7548101541776398479 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (211351240047224213 / 10000000000000000 : ℝ)
    (1935706982041 / 1000000000000 : ℝ) (7548101541776398479 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1542_denomLower :
    (587572107041944543 / 400000000 : ℝ) ≤ Real.exp (824523447811107 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (824523447811107 / 39062500000000 : ℝ) (967027425679 /
    500000000000 : ℝ) (587572107041944543 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1542_product_lower :
    (843358897029857 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (771 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1542_leftExp
    (by norm_num : (0 : ℝ) ≤ (2147596243 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1542_product_upper :
    Real.pi * Real.exp (1543 / 800 : ℝ) ≤ (216169990047224213 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1542_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1542_endpointLower :
    (4597 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (771 / 800 : ℝ) (1543 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (843358897029857 / 39062500000000 : ℝ) (Real.pi * Real.exp (771 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1542_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1543 / 800 : ℝ) - (771 / 1600 : ℝ)) ≤
      (7548101541776398479 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1542_denomUpper
    linarith [hpThetaJensenCell1542_product_upper]
  have hi : (1 / (7548101541776398479 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1543 / 800 : ℝ) - (771 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7548101541776398479 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7548101541776398479 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((771 / 1600 : ℝ) - Real.pi * Real.exp (1543 / 800 : ℝ)) := by
    rw [show (771 / 1600 : ℝ) - Real.pi * Real.exp (1543 / 800 : ℝ) =
      -(Real.pi * Real.exp (1543 / 800 : ℝ) - (771 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (771 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (771 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1542_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7548101541776398479 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1542_endpointUpper :
    hpThetaJensenKernelEndpointUpper (771 / 800 : ℝ) (1543 / 1600 : ℝ) ≤ (11873 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1543 / 800 : ℝ)) (216169990047224213 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1543 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1542_product_upper
  have hD : (587572107041944543 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (771 / 400 : ℝ) - (1543 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1542_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1542_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (771 / 400 : ℝ) - (1543 / 3200 : ℝ)) ≤
      (1 / (587572107041944543 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (587572107041944543 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1543 / 3200 : ℝ) - Real.pi * Real.exp (771 / 400 : ℝ)) ≤
      (2 / (587572107041944543 / 400000000 : ℝ) : ℝ) := by
    rw [show (1543 / 3200 : ℝ) - Real.pi * Real.exp (771 / 400 : ℝ) =
      -(Real.pi * Real.exp (771 / 400 : ℝ) - (1543 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (216169990047224213 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (216169990047224213 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1542_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (771 / 800 : ℝ) (1543 / 1600 : ℝ)) :
    (4597 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11873 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1542_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1542_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1543_leftExp :
    (34404518669 / 5000000000 : ℝ) ≤ Real.exp (1543 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1543 / 800 : ℝ) (42485077287 / 40000000000 : ℝ)
    (34404518669 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1543_rightExp :
    Real.exp (193 / 100 : ℝ) ≤ (34447551209 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (193 / 100 : ℝ) (13277105279 / 12500000000 : ℝ)
    (34447551209 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1543_denomUpper :
    Real.exp (105809248245335937 / 5000000000000000 : ℝ) ≤ (7752549248492237623 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (105809248245335937 / 5000000000000000 : ℝ)
    (1937324314087 / 1000000000000 : ℝ) (7752549248492237623 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1543_denomLower :
    (15086667075841826601 / 10000000000 : ℝ) ≤ Real.exp (13209057576797631 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (13209057576797631 / 625000000000000 : ℝ) (241958594917 /
    125000000000 : ℝ) (15086667075841826601 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1543_product_lower :
    (13510620076797631 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1543 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1543_leftExp
    (by norm_num : (0 : ℝ) ≤ (34404518669 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1543_product_upper :
    Real.pi * Real.exp (193 / 100 : ℝ) ≤ (108220185745335937 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1543_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1543_endpointLower :
    (22437 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1543 / 1600 : ℝ) (193 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13510620076797631 / 625000000000000 : ℝ) (Real.pi * Real.exp (1543 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1543_product_lower
  have hD : Real.exp (Real.pi * Real.exp (193 / 100 : ℝ) - (1543 / 3200 : ℝ)) ≤
      (7752549248492237623 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1543_denomUpper
    linarith [hpThetaJensenCell1543_product_upper]
  have hi : (1 / (7752549248492237623 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (193 / 100 : ℝ) - (1543 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7752549248492237623 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7752549248492237623 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1543 / 3200 : ℝ) - Real.pi * Real.exp (193 / 100 : ℝ)) := by
    rw [show (1543 / 3200 : ℝ) - Real.pi * Real.exp (193 / 100 : ℝ) =
      -(Real.pi * Real.exp (193 / 100 : ℝ) - (1543 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1543 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1543 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1543_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7752549248492237623 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1543_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1543 / 1600 : ℝ) (193 / 200 : ℝ) ≤ (23181 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (193 / 100 : ℝ)) (108220185745335937 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (193 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1543_product_upper
  have hD : (15086667075841826601 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1543 / 800 : ℝ) - (193 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1543_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1543_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1543 / 800 : ℝ) - (193 / 400 : ℝ)) ≤
      (1 / (15086667075841826601 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15086667075841826601 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((193 / 400 : ℝ) - Real.pi * Real.exp (1543 / 800 : ℝ)) ≤
      (2 / (15086667075841826601 / 10000000000 : ℝ) : ℝ) := by
    rw [show (193 / 400 : ℝ) - Real.pi * Real.exp (1543 / 800 : ℝ) =
      -(Real.pi * Real.exp (1543 / 800 : ℝ) - (193 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (108220185745335937 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (108220185745335937 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1543_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1543 / 1600 : ℝ) (193 / 200 : ℝ)) :
    (22437 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (23181 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1543_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1543_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1544_leftExp :
    (13779020483 / 2000000000 : ℝ) ≤ Real.exp (193 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (193 / 100 : ℝ) (1062168422319 / 1000000000000 : ℝ)
    (13779020483 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1544_rightExp :
    Real.exp (309 / 160 : ℝ) ≤ (34490637571 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (309 / 160 : ℝ) (265552478521 / 250000000000 : ℝ)
    (34490637571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1544_denomUpper :
    Real.exp (105943045558590603 / 5000000000000000 : ℝ) ≤ (15925607810370250707 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (105943045558590603 / 5000000000000000 : ℝ) (969472523287
    / 500000000000 : ℝ) (15925607810370250707 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1544_denomLower :
    (15495304063844103929 / 10000000000 : ℝ) ≤ Real.exp (5290304439653617 / 250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (5290304439653617 / 250000000000000 : ℝ) (77491442357 /
    40000000000 : ℝ) (15495304063844103929 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1544_product_lower :
    (5411007564653617 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (193 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1544_leftExp
    (by norm_num : (0 : ℝ) ≤ (13779020483 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1544_product_upper :
    Real.pi * Real.exp (309 / 160 : ℝ) ≤ (108355545558590603 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1544_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1544_endpointLower :
    (21901 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (193 / 200 : ℝ) (309 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5411007564653617 / 250000000000000 : ℝ) (Real.pi * Real.exp (193 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1544_product_lower
  have hD : Real.exp (Real.pi * Real.exp (309 / 160 : ℝ) - (193 / 400 : ℝ)) ≤
      (15925607810370250707 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1544_denomUpper
    linarith [hpThetaJensenCell1544_product_upper]
  have hi : (1 / (15925607810370250707 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (309 / 160 : ℝ) - (193 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15925607810370250707 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15925607810370250707 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((193 / 400 : ℝ) - Real.pi * Real.exp (309 / 160 : ℝ)) := by
    rw [show (193 / 400 : ℝ) - Real.pi * Real.exp (309 / 160 : ℝ) =
      -(Real.pi * Real.exp (309 / 160 : ℝ) - (193 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (193 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (193 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1544_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15925607810370250707 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1544_endpointUpper :
    hpThetaJensenKernelEndpointUpper (193 / 200 : ℝ) (309 / 320 : ℝ) ≤ (5657 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (309 / 160 : ℝ)) (108355545558590603 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (309 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1544_product_upper
  have hD : (15495304063844103929 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (193 / 100 : ℝ) - (309 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1544_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1544_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (193 / 100 : ℝ) - (309 / 640 : ℝ)) ≤
      (1 / (15495304063844103929 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15495304063844103929 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((309 / 640 : ℝ) - Real.pi * Real.exp (193 / 100 : ℝ)) ≤
      (2 / (15495304063844103929 / 10000000000 : ℝ) : ℝ) := by
    rw [show (309 / 640 : ℝ) - Real.pi * Real.exp (193 / 100 : ℝ) =
      -(Real.pi * Real.exp (193 / 100 : ℝ) - (309 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (108355545558590603 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (108355545558590603 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1544_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (193 / 200 : ℝ) (309 / 320 : ℝ)) :
    (21901 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5657 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1544_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1544_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1545_leftExp :
    (68981275139 / 10000000000 : ℝ) ≤ Real.exp (309 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (309 / 160 : ℝ) (1062209914083 / 1000000000000 : ℝ)
    (68981275139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1545_rightExp :
    Real.exp (773 / 400 : ℝ) ≤ (1381351113 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (773 / 400 : ℝ) (1062251407469 / 1000000000000 : ℝ)
    (1381351113 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1545_denomUpper :
    Real.exp (4243080487143009 / 200000000000000 : ℝ) ≤ (8179037766377850999 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (4243080487143009 / 200000000000000 : ℝ) (1940569188383 /
    1000000000000 : ℝ) (8179037766377850999 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1545_denomLower :
    (15915547608012022637 / 10000000000 : ℝ) ≤ Real.exp (26484971515810161 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26484971515810161 / 1250000000000000 : ℝ) (969453379443
    / 500000000000 : ℝ) (15915547608012022637 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1545_product_lower :
    (27088877765810161 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (309 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1545_leftExp
    (by norm_num : (0 : ℝ) ≤ (68981275139 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1545_product_upper :
    Real.pi * Real.exp (773 / 400 : ℝ) ≤ (4339642987143009 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1545_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1545_endpointLower :
    (10689 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (309 / 320 : ℝ) (773 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27088877765810161 / 1250000000000000 : ℝ) (Real.pi * Real.exp (309 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1545_product_lower
  have hD : Real.exp (Real.pi * Real.exp (773 / 400 : ℝ) - (309 / 640 : ℝ)) ≤
      (8179037766377850999 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1545_denomUpper
    linarith [hpThetaJensenCell1545_product_upper]
  have hi : (1 / (8179037766377850999 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (773 / 400 : ℝ) - (309 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8179037766377850999 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8179037766377850999 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((309 / 640 : ℝ) - Real.pi * Real.exp (773 / 400 : ℝ)) := by
    rw [show (309 / 640 : ℝ) - Real.pi * Real.exp (773 / 400 : ℝ) =
      -(Real.pi * Real.exp (773 / 400 : ℝ) - (309 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (309 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (309 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1545_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8179037766377850999 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1545_endpointUpper :
    hpThetaJensenKernelEndpointUpper (309 / 320 : ℝ) (773 / 800 : ℝ) ≤ (2761 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (773 / 400 : ℝ)) (4339642987143009 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (773 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1545_product_upper
  have hD : (15915547608012022637 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (309 / 160 : ℝ) - (773 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1545_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1545_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (309 / 160 : ℝ) - (773 / 1600 : ℝ)) ≤
      (1 / (15915547608012022637 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15915547608012022637 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((773 / 1600 : ℝ) - Real.pi * Real.exp (309 / 160 : ℝ)) ≤
      (2 / (15915547608012022637 / 10000000000 : ℝ) : ℝ) := by
    rw [show (773 / 1600 : ℝ) - Real.pi * Real.exp (309 / 160 : ℝ) =
      -(Real.pi * Real.exp (309 / 160 : ℝ) - (773 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4339642987143009 / 200000000000000 : ℝ) ^ 2 - 6 *
      (4339642987143009 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1545_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (309 / 320 : ℝ) (773 / 800 : ℝ)) :
    (10689 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2761 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1545_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1545_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1546_leftExp :
    (69067555647 / 10000000000 : ℝ) ≤ Real.exp (773 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (773 / 400 : ℝ) (265562851867 / 250000000000 : ℝ)
    (69067555647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1546_rightExp :
    Real.exp (1547 / 800 : ℝ) ≤ (17288486019 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1547 / 800 : ℝ) (42491716099 / 40000000000 : ℝ)
    (17288486019 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1546_denomUpper :
    Real.exp (53105574157888267 / 2500000000000000 : ℝ) ≤ (2100357099269682877 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (53105574157888267 / 2500000000000000 : ℝ) (485549187091
    / 250000000000 : ℝ) (2100357099269682877 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1546_denomLower :
    (4086935499872486647 / 2500000000 : ℝ) ≤ Real.exp (26518463160021253 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26518463160021253 / 1250000000000000 : ℝ) (19405308681 /
    10000000000 : ℝ) (4086935499872486647 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1546_product_lower :
    (27122760035021253 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (773 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1546_leftExp
    (by norm_num : (0 : ℝ) ≤ (69067555647 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1546_product_upper :
    Real.pi * Real.exp (1547 / 800 : ℝ) ≤ (54313386657888267 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1546_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1546_endpointLower :
    (10433 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (773 / 800 : ℝ) (1547 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27122760035021253 / 1250000000000000 : ℝ) (Real.pi * Real.exp (773 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1546_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1547 / 800 : ℝ) - (773 / 1600 : ℝ)) ≤
      (2100357099269682877 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1546_denomUpper
    linarith [hpThetaJensenCell1546_product_upper]
  have hi : (1 / (2100357099269682877 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1547 / 800 : ℝ) - (773 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2100357099269682877 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2100357099269682877 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((773 / 1600 : ℝ) - Real.pi * Real.exp (1547 / 800 : ℝ)) := by
    rw [show (773 / 1600 : ℝ) - Real.pi * Real.exp (1547 / 800 : ℝ) =
      -(Real.pi * Real.exp (1547 / 800 : ℝ) - (773 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (773 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (773 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1546_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2100357099269682877 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1546_endpointUpper :
    hpThetaJensenKernelEndpointUpper (773 / 800 : ℝ) (1547 / 1600 : ℝ) ≤ (539 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1547 / 800 : ℝ)) (54313386657888267 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1547 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1546_product_upper
  have hD : (4086935499872486647 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (773 / 400 : ℝ) - (1547 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1546_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1546_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (773 / 400 : ℝ) - (1547 / 3200 : ℝ)) ≤
      (1 / (4086935499872486647 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4086935499872486647 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1547 / 3200 : ℝ) - Real.pi * Real.exp (773 / 400 : ℝ)) ≤
      (2 / (4086935499872486647 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1547 / 3200 : ℝ) - Real.pi * Real.exp (773 / 400 : ℝ) =
      -(Real.pi * Real.exp (773 / 400 : ℝ) - (1547 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54313386657888267 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (54313386657888267 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1546_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (773 / 800 : ℝ) (1547 / 1600 : ℝ)) :
    (10433 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (539 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1546_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1546_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1547_leftExp :
    (69153944073 / 10000000000 : ℝ) ≤ Real.exp (1547 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1547 / 800 : ℝ) (531146451237 / 500000000000 : ℝ)
    (69153944073 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1547_rightExp :
    Real.exp (387 / 200 : ℝ) ≤ (13848088111 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (387 / 200 : ℝ) (531167199551 / 500000000000 : ℝ)
    (13848088111 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1547_denomUpper :
    Real.exp (42538181672900823 / 2000000000000000 : ℝ) ≤ (17260317705330577029 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (42538181672900823 / 2000000000000000 : ℝ) (194382773541
    / 100000000000 : ℝ) (17260317705330577029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1547_denomLower :
    (8396121071837881217 / 5000000000 : ℝ) ≤ Real.exp (26551997183523027 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26551997183523027 / 1250000000000000 : ℝ) (1942158395417
    / 1000000000000 : ℝ) (8396121071837881217 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1547_product_lower :
    (27156684683523027 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1547 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1547_leftExp
    (by norm_num : (0 : ℝ) ≤ (69153944073 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1547_product_upper :
    Real.pi * Real.exp (387 / 200 : ℝ) ≤ (43505056672900823 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1547_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1547_endpointLower :
    (4073 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1547 / 1600 : ℝ) (387 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27156684683523027 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1547 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1547_product_lower
  have hD : Real.exp (Real.pi * Real.exp (387 / 200 : ℝ) - (1547 / 3200 : ℝ)) ≤
      (17260317705330577029 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1547_denomUpper
    linarith [hpThetaJensenCell1547_product_upper]
  have hi : (1 / (17260317705330577029 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (387 / 200 : ℝ) - (1547 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17260317705330577029 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17260317705330577029 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1547 / 3200 : ℝ) - Real.pi * Real.exp (387 / 200 : ℝ)) := by
    rw [show (1547 / 3200 : ℝ) - Real.pi * Real.exp (387 / 200 : ℝ) =
      -(Real.pi * Real.exp (387 / 200 : ℝ) - (1547 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1547 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1547 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1547_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17260317705330577029 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1547_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1547 / 1600 : ℝ) (387 / 400 : ℝ) ≤ (5261 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (387 / 200 : ℝ)) (43505056672900823 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (387 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1547_product_upper
  have hD : (8396121071837881217 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1547 / 800 : ℝ) - (387 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1547_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1547_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1547 / 800 : ℝ) - (387 / 800 : ℝ)) ≤
      (1 / (8396121071837881217 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8396121071837881217 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((387 / 800 : ℝ) - Real.pi * Real.exp (1547 / 800 : ℝ)) ≤
      (2 / (8396121071837881217 / 5000000000 : ℝ) : ℝ) := by
    rw [show (387 / 800 : ℝ) - Real.pi * Real.exp (1547 / 800 : ℝ) =
      -(Real.pi * Real.exp (1547 / 800 : ℝ) - (387 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43505056672900823 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (43505056672900823 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1547_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1547 / 1600 : ℝ) (387 / 400 : ℝ)) :
    (4073 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5261 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1547_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1547_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1548_leftExp :
    (8655055069 / 1250000000 : ℝ) ≤ Real.exp (387 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (387 / 200 : ℝ) (1062334399101 / 1000000000000 : ℝ)
    (8655055069 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1548_rightExp :
    Real.exp (1549 / 800 : ℝ) ≤ (34663522611 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1549 / 800 : ℝ) (21247517947 / 20000000000 : ℝ)
    (34663522611 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1548_denomUpper :
    Real.exp (106479929990059323 / 5000000000000000 : ℝ) ≤ (8865417852728666329 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (106479929990059323 / 5000000000000000 : ℝ) (48636553961
    / 25000000000 : ℝ) (8865417852728666329 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1548_denomLower :
    (21561767399701489 / 12500000 : ℝ) ≤ Real.exp (3323196704916231 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3323196704916231 / 156250000000000 : ℝ) (194378934973 /
    100000000000 : ℝ) (21561767399701489 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1548_product_lower :
    (3398831470541231 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (387 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1548_leftExp
    (by norm_num : (0 : ℝ) ≤ (8655055069 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1548_product_upper :
    Real.pi * Real.exp (1549 / 800 : ℝ) ≤ (108898679990059323 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1548_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1548_endpointLower :
    (4969 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (387 / 400 : ℝ) (1549 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3398831470541231 / 156250000000000 : ℝ) (Real.pi * Real.exp (387 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1548_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1549 / 800 : ℝ) - (387 / 800 : ℝ)) ≤
      (8865417852728666329 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1548_denomUpper
    linarith [hpThetaJensenCell1548_product_upper]
  have hi : (1 / (8865417852728666329 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1549 / 800 : ℝ) - (387 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8865417852728666329 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8865417852728666329 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((387 / 800 : ℝ) - Real.pi * Real.exp (1549 / 800 : ℝ)) := by
    rw [show (387 / 800 : ℝ) - Real.pi * Real.exp (1549 / 800 : ℝ) =
      -(Real.pi * Real.exp (1549 / 800 : ℝ) - (387 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (387 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (387 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1548_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8865417852728666329 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1548_endpointUpper :
    hpThetaJensenKernelEndpointUpper (387 / 400 : ℝ) (1549 / 1600 : ℝ) ≤ (20539 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1549 / 800 : ℝ)) (108898679990059323 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1549 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1548_product_upper
  have hD : (21561767399701489 / 12500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (387 / 200 : ℝ) - (1549 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1548_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1548_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (387 / 200 : ℝ) - (1549 / 3200 : ℝ)) ≤
      (1 / (21561767399701489 / 12500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21561767399701489 / 12500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1549 / 3200 : ℝ) - Real.pi * Real.exp (387 / 200 : ℝ)) ≤
      (2 / (21561767399701489 / 12500000 : ℝ) : ℝ) := by
    rw [show (1549 / 3200 : ℝ) - Real.pi * Real.exp (387 / 200 : ℝ) =
      -(Real.pi * Real.exp (387 / 200 : ℝ) - (1549 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (108898679990059323 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (108898679990059323 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1548_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (387 / 400 : ℝ) (1549 / 1600 : ℝ)) :
    (4969 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (20539 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1548_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1548_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1549_leftExp :
    (69327045219 / 10000000000 : ℝ) ≤ Real.exp (1549 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1549 / 800 : ℝ) (1062375897349 / 1000000000000 : ℝ)
    (69327045219 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1549_rightExp :
    Real.exp (31 / 16 : ℝ) ≤ (69413758213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 16 : ℝ) (1062417397219 / 1000000000000 : ℝ)
    (69413758213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1549_denomUpper :
    Real.exp (213229151905653309 / 10000000000000000 : ℝ) ≤ (3642959986133157069 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (213229151905653309 / 10000000000000000 : ℝ)
    (389420005283 / 200000000000 : ℝ) (3642959986133157069 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1549_denomLower :
    (17719634527909283737 / 10000000000 : ℝ) ≤ Real.exp (26619192580456081 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26619192580456081 / 1250000000000000 : ℝ) (1945423739957
    / 1000000000000 : ℝ) (17719634527909283737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1549_product_lower :
    (27224661330456081 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1549 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1549_leftExp
    (by norm_num : (0 : ℝ) ≤ (69327045219 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1549_product_upper :
    Real.pi * Real.exp (31 / 16 : ℝ) ≤ (218069776905653309 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1549_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1549_endpointLower :
    (19399 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1549 / 1600 : ℝ) (31 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27224661330456081 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1549 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1549_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 16 : ℝ) - (1549 / 3200 : ℝ)) ≤
      (3642959986133157069 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1549_denomUpper
    linarith [hpThetaJensenCell1549_product_upper]
  have hi : (1 / (3642959986133157069 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 16 : ℝ) - (1549 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3642959986133157069 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3642959986133157069 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1549 / 3200 : ℝ) - Real.pi * Real.exp (31 / 16 : ℝ)) := by
    rw [show (1549 / 3200 : ℝ) - Real.pi * Real.exp (31 / 16 : ℝ) =
      -(Real.pi * Real.exp (31 / 16 : ℝ) - (1549 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1549 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1549 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1549_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3642959986133157069 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1549_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1549 / 1600 : ℝ) (31 / 32 : ℝ) ≤ (10023 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 16 : ℝ)) (218069776905653309 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1549_product_upper
  have hD : (17719634527909283737 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1549 / 800 : ℝ) - (31 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell1549_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1549_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1549 / 800 : ℝ) - (31 / 64 : ℝ)) ≤
      (1 / (17719634527909283737 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17719634527909283737 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 64 : ℝ) - Real.pi * Real.exp (1549 / 800 : ℝ)) ≤
      (2 / (17719634527909283737 / 10000000000 : ℝ) : ℝ) := by
    rw [show (31 / 64 : ℝ) - Real.pi * Real.exp (1549 / 800 : ℝ) =
      -(Real.pi * Real.exp (1549 / 800 : ℝ) - (31 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (218069776905653309 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (218069776905653309 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1549_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1549 / 1600 : ℝ) (31 / 32 : ℝ)) :
    (19399 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10023 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1549_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1549_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1550_leftExp :
    (6941375821 / 1000000000 : ℝ) ≤ Real.exp (31 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 16 : ℝ) (531208698609 / 500000000000 : ℝ)
    (6941375821 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1550_rightExp :
    Real.exp (1551 / 800 : ℝ) ≤ (69500579663 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1551 / 800 : ℝ) (1062458898709 / 1000000000000 : ℝ)
    (69500579663 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1550_denomUpper :
    Real.exp (213498784565223159 / 10000000000000000 : ℝ) ≤ (4678152895007932941 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (213498784565223159 / 10000000000000000 : ℝ)
    (121796334269 / 62500000000 : ℝ) (4678152895007932941 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1550_denomLower :
    (18203292858399089001 / 10000000000 : ℝ) ≤ Real.exp (2665285406030879 / 125000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (2665285406030879 / 125000000000000 : ℝ) (97353078753 /
    50000000000 : ℝ) (18203292858399089001 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1550_product_lower :
    (2725871343530879 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1550_leftExp
    (by norm_num : (0 : ℝ) ≤ (6941375821 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1550_product_upper :
    Real.pi * Real.exp (1551 / 800 : ℝ) ≤ (218342534565223159 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1550_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1550_endpointLower :
    (18931 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 32 : ℝ) (1551 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2725871343530879 / 125000000000000 : ℝ) (Real.pi * Real.exp (31 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell1550_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1551 / 800 : ℝ) - (31 / 64 : ℝ)) ≤
      (4678152895007932941 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1550_denomUpper
    linarith [hpThetaJensenCell1550_product_upper]
  have hi : (1 / (4678152895007932941 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1551 / 800 : ℝ) - (31 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4678152895007932941 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4678152895007932941 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 64 : ℝ) - Real.pi * Real.exp (1551 / 800 : ℝ)) := by
    rw [show (31 / 64 : ℝ) - Real.pi * Real.exp (1551 / 800 : ℝ) =
      -(Real.pi * Real.exp (1551 / 800 : ℝ) - (31 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 16 : ℝ)) := by
    have h := hpThetaJensenCell1550_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4678152895007932941 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1550_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 32 : ℝ) (1551 / 1600 : ℝ) ≤ (4891 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1551 / 800 : ℝ)) (218342534565223159 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1551 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1550_product_upper
  have hD : (18203292858399089001 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 16 : ℝ) - (1551 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1550_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1550_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 16 : ℝ) - (1551 / 3200 : ℝ)) ≤
      (1 / (18203292858399089001 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18203292858399089001 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1551 / 3200 : ℝ) - Real.pi * Real.exp (31 / 16 : ℝ)) ≤
      (2 / (18203292858399089001 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1551 / 3200 : ℝ) - Real.pi * Real.exp (31 / 16 : ℝ) =
      -(Real.pi * Real.exp (31 / 16 : ℝ) - (1551 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (218342534565223159 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (218342534565223159 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1550_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 32 : ℝ) (1551 / 1600 : ℝ)) :
    (18931 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4891 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1550_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1550_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1551_leftExp :
    (3475028983 / 500000000 : ℝ) ≤ Real.exp (1551 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1551 / 800 : ℝ) (265614724677 / 250000000000 : ℝ)
    (3475028983 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1551_rightExp :
    Real.exp (97 / 50 : ℝ) ≤ (69587509709 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97 / 50 : ℝ) (1062500401821 / 1000000000000 : ℝ)
    (69587509709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1551_denomUpper :
    Real.exp (213768758389226437 / 10000000000000000 : ℝ) ≤ (2403085540028856511 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (213768758389226437 / 10000000000000000 : ℝ)
    (975193066569 / 500000000000 : ℝ) (2403085540028856511 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1551_denomLower :
    (18700789856551854047 / 10000000000 : ℝ) ≤ Real.exp (1334327906595117 / 62500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1334327906595117 / 62500000000000 : ℝ) (243587858001 /
    125000000000 : ℝ) (18700789856551854047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1551_product_lower :
    (1364640406595117 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (1551 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1551_leftExp
    (by norm_num : (0 : ℝ) ≤ (3475028983 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1551_product_upper :
    Real.pi * Real.exp (97 / 50 : ℝ) ≤ (218615633389226437 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1551_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1551_endpointLower :
    (739 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (1551 / 1600 : ℝ) (97 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1364640406595117 / 62500000000000 : ℝ) (Real.pi * Real.exp (1551 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1551_product_lower
  have hD : Real.exp (Real.pi * Real.exp (97 / 50 : ℝ) - (1551 / 3200 : ℝ)) ≤
      (2403085540028856511 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1551_denomUpper
    linarith [hpThetaJensenCell1551_product_upper]
  have hi : (1 / (2403085540028856511 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (97 / 50 : ℝ) - (1551 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2403085540028856511 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2403085540028856511 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1551 / 3200 : ℝ) - Real.pi * Real.exp (97 / 50 : ℝ)) := by
    rw [show (1551 / 3200 : ℝ) - Real.pi * Real.exp (97 / 50 : ℝ) =
      -(Real.pi * Real.exp (97 / 50 : ℝ) - (1551 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1551 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1551 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1551_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2403085540028856511 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1551_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1551 / 1600 : ℝ) (97 / 100 : ℝ) ≤ (19093 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (97 / 50 : ℝ)) (218615633389226437 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (97 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1551_product_upper
  have hD : (18700789856551854047 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1551 / 800 : ℝ) - (97 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1551_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1551_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1551 / 800 : ℝ) - (97 / 200 : ℝ)) ≤
      (1 / (18700789856551854047 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18700789856551854047 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((97 / 200 : ℝ) - Real.pi * Real.exp (1551 / 800 : ℝ)) ≤
      (2 / (18700789856551854047 / 10000000000 : ℝ) : ℝ) := by
    rw [show (97 / 200 : ℝ) - Real.pi * Real.exp (1551 / 800 : ℝ) =
      -(Real.pi * Real.exp (1551 / 800 : ℝ) - (97 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (218615633389226437 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (218615633389226437 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1551_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1551 / 1600 : ℝ) (97 / 100 : ℝ)) :
    (739 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (19093 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1551_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1551_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1552_leftExp :
    (34793754853 / 5000000000 : ℝ) ≤ Real.exp (97 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (97 / 50 : ℝ) (53125020091 / 50000000000 : ℝ)
    (34793754853 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1552_rightExp :
    Real.exp (1553 / 800 : ℝ) ≤ (69674548483 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1553 / 800 : ℝ) (1062541906553 / 1000000000000 : ℝ)
    (69674548483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1552_denomUpper :
    Real.exp (214039073792353419 / 10000000000000000 : ℝ) ≤ (19751444645873290947 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (214039073792353419 / 10000000000000000 : ℝ)
    (1952034389879 / 1000000000000 : ℝ) (19751444645873290947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1552_denomLower :
    (4803134731693486813 / 2500000000 : ℝ) ≤ Real.exp (13360152424518247 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13360152424518247 / 625000000000000 : ℝ) (195034761583 /
    100000000000 : ℝ) (4803134731693486813 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1552_product_lower :
    (13663472737018247 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (97 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1552_leftExp
    (by norm_num : (0 : ℝ) ≤ (34793754853 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1552_product_upper :
    Real.pi * Real.exp (1553 / 800 : ℝ) ≤ (218889073792353419 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1552_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1552_endpointLower :
    (18029 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 100 : ℝ) (1553 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13663472737018247 / 625000000000000 : ℝ) (Real.pi * Real.exp (97 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1552_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1553 / 800 : ℝ) - (97 / 200 : ℝ)) ≤
      (19751444645873290947 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1552_denomUpper
    linarith [hpThetaJensenCell1552_product_upper]
  have hi : (1 / (19751444645873290947 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1553 / 800 : ℝ) - (97 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19751444645873290947 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19751444645873290947 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((97 / 200 : ℝ) - Real.pi * Real.exp (1553 / 800 : ℝ)) := by
    rw [show (97 / 200 : ℝ) - Real.pi * Real.exp (1553 / 800 : ℝ) =
      -(Real.pi * Real.exp (1553 / 800 : ℝ) - (97 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (97 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (97 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1552_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19751444645873290947 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1552_endpointUpper :
    hpThetaJensenKernelEndpointUpper (97 / 100 : ℝ) (1553 / 1600 : ℝ) ≤ (18633 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1553 / 800 : ℝ)) (218889073792353419 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1553 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1552_product_upper
  have hD : (4803134731693486813 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (97 / 50 : ℝ) - (1553 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1552_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1552_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (97 / 50 : ℝ) - (1553 / 3200 : ℝ)) ≤
      (1 / (4803134731693486813 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4803134731693486813 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1553 / 3200 : ℝ) - Real.pi * Real.exp (97 / 50 : ℝ)) ≤
      (2 / (4803134731693486813 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1553 / 3200 : ℝ) - Real.pi * Real.exp (97 / 50 : ℝ) =
      -(Real.pi * Real.exp (97 / 50 : ℝ) - (1553 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (218889073792353419 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (218889073792353419 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1552_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (97 / 100 : ℝ) (1553 / 1600 : ℝ)) :
    (18029 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (18633 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1552_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1552_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1553_leftExp :
    (69674548479 / 10000000000 : ℝ) ≤ Real.exp (1553 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1553 / 800 : ℝ) (132817738319 / 125000000000 : ℝ)
    (69674548479 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1553_rightExp :
    Real.exp (777 / 400 : ℝ) ≤ (17440424031 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (777 / 400 : ℝ) (1062583412907 / 1000000000000 : ℝ)
    (17440424031 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1553_denomUpper :
    Real.exp (53577432802821383 / 2500000000000000 : ℝ) ≤ (317083318212093093 / 156250000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (53577432802821383 / 2500000000000000 : ℝ) (1953686127647
    / 1000000000000 : ℝ) (317083318212093093 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1553_denomLower :
    (19738966288048964873 / 10000000000 : ℝ) ≤ Real.exp (26754094263154821 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26754094263154821 / 1250000000000000 : ℝ) (195199583947
    / 100000000000 : ℝ) (19738966288048964873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1553_product_lower :
    (27361125513154821 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1553 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1553_leftExp
    (by norm_num : (0 : ℝ) ≤ (69674548479 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1553_product_upper :
    Real.pi * Real.exp (777 / 400 : ℝ) ≤ (54790714052821383 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1553_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1553_endpointLower :
    (17593 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1553 / 1600 : ℝ) (777 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27361125513154821 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1553 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1553_product_lower
  have hD : Real.exp (Real.pi * Real.exp (777 / 400 : ℝ) - (1553 / 3200 : ℝ)) ≤
      (317083318212093093 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1553_denomUpper
    linarith [hpThetaJensenCell1553_product_upper]
  have hi : (1 / (317083318212093093 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (777 / 400 : ℝ) - (1553 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (317083318212093093 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (317083318212093093 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1553 / 3200 : ℝ) - Real.pi * Real.exp (777 / 400 : ℝ)) := by
    rw [show (1553 / 3200 : ℝ) - Real.pi * Real.exp (777 / 400 : ℝ) =
      -(Real.pi * Real.exp (777 / 400 : ℝ) - (1553 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1553 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1553 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1553_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (317083318212093093 / 156250000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1553_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1553 / 1600 : ℝ) (777 / 800 : ℝ) ≤ (18183 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (777 / 400 : ℝ)) (54790714052821383 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (777 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1553_product_upper
  have hD : (19738966288048964873 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1553 / 800 : ℝ) - (777 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1553_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1553_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1553 / 800 : ℝ) - (777 / 1600 : ℝ)) ≤
      (1 / (19738966288048964873 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19738966288048964873 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((777 / 1600 : ℝ) - Real.pi * Real.exp (1553 / 800 : ℝ)) ≤
      (2 / (19738966288048964873 / 10000000000 : ℝ) : ℝ) := by
    rw [show (777 / 1600 : ℝ) - Real.pi * Real.exp (1553 / 800 : ℝ) =
      -(Real.pi * Real.exp (1553 / 800 : ℝ) - (777 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (54790714052821383 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (54790714052821383 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1553_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1553 / 1600 : ℝ) (777 / 800 : ℝ)) :
    (17593 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (18183 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1553_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1553_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1554_leftExp :
    (69761696121 / 10000000000 : ℝ) ≤ Real.exp (777 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (777 / 400 : ℝ) (531291706453 / 500000000000 : ℝ)
    (69761696121 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1554_rightExp :
    Real.exp (311 / 160 : ℝ) ≤ (1091389887 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (311 / 160 : ℝ) (531312460441 / 500000000000 : ℝ)
    (1091389887 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1554_denomUpper :
    Real.exp (3352823923019991 / 156250000000000 : ℝ) ≤ (10425400485635108023 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (3352823923019991 / 156250000000000 : ℝ) (195534135553 /
    100000000000 : ℝ) (10425400485635108023 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1554_denomLower :
    (20280511489238869501 / 10000000000 : ℝ) ≤ Real.exp (26787926430020579 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26787926430020579 / 1250000000000000 : ℝ) (390729508821
    / 200000000000 : ℝ) (20280511489238869501 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1554_product_lower :
    (27395348305020579 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (777 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1554_leftExp
    (by norm_num : (0 : ℝ) ≤ (69761696121 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1554_product_upper :
    Real.pi * Real.exp (311 / 160 : ℝ) ≤ (3428702829269991 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1554_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1554_endpointLower :
    (17167 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (777 / 800 : ℝ) (311 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27395348305020579 / 1250000000000000 : ℝ) (Real.pi * Real.exp (777 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1554_product_lower
  have hD : Real.exp (Real.pi * Real.exp (311 / 160 : ℝ) - (777 / 1600 : ℝ)) ≤
      (10425400485635108023 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1554_denomUpper
    linarith [hpThetaJensenCell1554_product_upper]
  have hi : (1 / (10425400485635108023 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (311 / 160 : ℝ) - (777 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10425400485635108023 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10425400485635108023 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((777 / 1600 : ℝ) - Real.pi * Real.exp (311 / 160 : ℝ)) := by
    rw [show (777 / 1600 : ℝ) - Real.pi * Real.exp (311 / 160 : ℝ) =
      -(Real.pi * Real.exp (311 / 160 : ℝ) - (777 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (777 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (777 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1554_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10425400485635108023 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1554_endpointUpper :
    hpThetaJensenKernelEndpointUpper (777 / 800 : ℝ) (311 / 320 : ℝ) ≤ (17743 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (311 / 160 : ℝ)) (3428702829269991 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (311 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1554_product_upper
  have hD : (20280511489238869501 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (777 / 400 : ℝ) - (311 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1554_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1554_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (777 / 400 : ℝ) - (311 / 640 : ℝ)) ≤
      (1 / (20280511489238869501 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20280511489238869501 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((311 / 640 : ℝ) - Real.pi * Real.exp (777 / 400 : ℝ)) ≤
      (2 / (20280511489238869501 / 10000000000 : ℝ) : ℝ) := by
    rw [show (311 / 640 : ℝ) - Real.pi * Real.exp (777 / 400 : ℝ) =
      -(Real.pi * Real.exp (777 / 400 : ℝ) - (311 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3428702829269991 / 156250000000000 : ℝ) ^ 2 - 6 *
      (3428702829269991 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1554_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (777 / 800 : ℝ) (311 / 320 : ℝ)) :
    (17167 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17743 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1554_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1554_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1555_leftExp :
    (13969790553 / 2000000000 : ℝ) ≤ Real.exp (311 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (311 / 160 : ℝ) (1062624920881 / 1000000000000 : ℝ)
    (13969790553 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1555_rightExp :
    Real.exp (389 / 200 : ℝ) ≤ (8742039819 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (389 / 200 : ℝ) (1062666430479 / 1000000000000 : ℝ)
    (8742039819 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1555_denomUpper :
    Real.exp (26856509226091667 / 1250000000000000 : ℝ) ≤ (21424318105506996729 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (26856509226091667 / 1250000000000000 : ℝ) (1957000082661
    / 1000000000000 : ℝ) (21424318105506996729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1555_denomLower :
    (325587933072546909 / 156250000 : ℝ) ≤ Real.exp (5364360280372547 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5364360280372547 / 250000000000000 : ℝ) (391060547753 /
    200000000000 : ℝ) (325587933072546909 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1555_product_lower :
    (5485922780372547 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (311 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1555_leftExp
    (by norm_num : (0 : ℝ) ≤ (13969790553 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1555_product_upper :
    Real.pi * Real.exp (389 / 200 : ℝ) ≤ (27463931101091667 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1555_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1555_endpointLower :
    (16751 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (311 / 320 : ℝ) (389 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5485922780372547 / 250000000000000 : ℝ) (Real.pi * Real.exp (311 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1555_product_lower
  have hD : Real.exp (Real.pi * Real.exp (389 / 200 : ℝ) - (311 / 640 : ℝ)) ≤
      (21424318105506996729 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1555_denomUpper
    linarith [hpThetaJensenCell1555_product_upper]
  have hi : (1 / (21424318105506996729 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (389 / 200 : ℝ) - (311 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (21424318105506996729 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (21424318105506996729 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((311 / 640 : ℝ) - Real.pi * Real.exp (389 / 200 : ℝ)) := by
    rw [show (311 / 640 : ℝ) - Real.pi * Real.exp (389 / 200 : ℝ) =
      -(Real.pi * Real.exp (389 / 200 : ℝ) - (311 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (311 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (311 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1555_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (21424318105506996729 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1555_endpointUpper :
    hpThetaJensenKernelEndpointUpper (311 / 320 : ℝ) (389 / 400 : ℝ) ≤ (8657 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (389 / 200 : ℝ)) (27463931101091667 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (389 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1555_product_upper
  have hD : (325587933072546909 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (311 / 160 : ℝ) - (389 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1555_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1555_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (311 / 160 : ℝ) - (389 / 800 : ℝ)) ≤
      (1 / (325587933072546909 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (325587933072546909 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((389 / 800 : ℝ) - Real.pi * Real.exp (311 / 160 : ℝ)) ≤
      (2 / (325587933072546909 / 156250000 : ℝ) : ℝ) := by
    rw [show (389 / 800 : ℝ) - Real.pi * Real.exp (311 / 160 : ℝ) =
      -(Real.pi * Real.exp (311 / 160 : ℝ) - (389 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27463931101091667 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (27463931101091667 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1555_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (311 / 320 : ℝ) (389 / 400 : ℝ)) :
    (16751 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8657 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1555_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1555_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1556_leftExp :
    (69936318549 / 10000000000 : ℝ) ≤ Real.exp (389 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (389 / 200 : ℝ) (531333215239 / 500000000000 : ℝ)
    (69936318549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1556_rightExp :
    Real.exp (1557 / 800 : ℝ) ≤ (7002379361 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1557 / 800 : ℝ) (1062707941697 / 1000000000000 : ℝ)
    (7002379361 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1556_denomUpper :
    Real.exp (21512375983862073 / 1000000000000000 : ℝ) ≤ (88057463971858317 / 40000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21512375983862073 / 1000000000000000 : ℝ) (1958662318143
    / 1000000000000 : ℝ) (88057463971858317 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1556_denomLower :
    (10705391161737676659 / 5000000000 : ℝ) ≤ Real.exp (26855719232873751 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26855719232873751 / 1250000000000000 : ℝ) (1956961432603
    / 1000000000000 : ℝ) (10705391161737676659 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1556_product_lower :
    (27463922357873751 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (389 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1556_leftExp
    (by norm_num : (0 : ℝ) ≤ (69936318549 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1556_product_upper :
    Real.pi * Real.exp (1557 / 800 : ℝ) ≤ (21998625983862073 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1556_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1556_endpointLower :
    (2043 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (389 / 400 : ℝ) (1557 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27463922357873751 / 1250000000000000 : ℝ) (Real.pi * Real.exp (389 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1556_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1557 / 800 : ℝ) - (389 / 800 : ℝ)) ≤
      (88057463971858317 / 40000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1556_denomUpper
    linarith [hpThetaJensenCell1556_product_upper]
  have hi : (1 / (88057463971858317 / 40000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1557 / 800 : ℝ) - (389 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (88057463971858317 / 40000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (88057463971858317 / 40000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((389 / 800 : ℝ) - Real.pi * Real.exp (1557 / 800 : ℝ)) := by
    rw [show (389 / 800 : ℝ) - Real.pi * Real.exp (1557 / 800 : ℝ) =
      -(Real.pi * Real.exp (1557 / 800 : ℝ) - (389 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (389 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (389 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1556_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (88057463971858317 / 40000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1556_endpointUpper :
    hpThetaJensenKernelEndpointUpper (389 / 400 : ℝ) (1557 / 1600 : ℝ) ≤ (8447 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1557 / 800 : ℝ)) (21998625983862073 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1557 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1556_product_upper
  have hD : (10705391161737676659 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (389 / 200 : ℝ) - (1557 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1556_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1556_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (389 / 200 : ℝ) - (1557 / 3200 : ℝ)) ≤
      (1 / (10705391161737676659 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10705391161737676659 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1557 / 3200 : ℝ) - Real.pi * Real.exp (389 / 200 : ℝ)) ≤
      (2 / (10705391161737676659 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1557 / 3200 : ℝ) - Real.pi * Real.exp (389 / 200 : ℝ) =
      -(Real.pi * Real.exp (389 / 200 : ℝ) - (1557 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21998625983862073 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (21998625983862073 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1556_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (389 / 400 : ℝ) (1557 / 1600 : ℝ)) :
    (2043 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8447 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1556_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1556_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1557_leftExp :
    (70023793607 / 10000000000 : ℝ) ≤ Real.exp (1557 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1557 / 800 : ℝ) (16604811589 / 15625000000 : ℝ)
    (70023793607 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1557_rightExp :
    Real.exp (779 / 400 : ℝ) ≤ (70111378081 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (779 / 400 : ℝ) (1062749454537 / 1000000000000 : ℝ)
    (70111378081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1557_denomUpper :
    Real.exp (215395789599623033 / 10000000000000000 : ℝ) ≤ (22621441965405014169 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (215395789599623033 / 10000000000000000 : ℝ)
    (1960328071197 / 1000000000000 : ℝ) (22621441965405014169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1557_denomLower :
    (11000228614515505129 / 5000000000 : ℝ) ≤ Real.exp (26889679975675293 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26889679975675293 / 1250000000000000 : ℝ) (1958623634721
    / 1000000000000 : ℝ) (11000228614515505129 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1557_product_lower :
    (27498273725675293 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1557 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1557_leftExp
    (by norm_num : (0 : ℝ) ≤ (70023793607 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1557_product_upper :
    Real.pi * Real.exp (779 / 400 : ℝ) ≤ (220261414599623033 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1557_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1557_endpointLower :
    (15947 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1557 / 1600 : ℝ) (779 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27498273725675293 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1557 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1557_product_lower
  have hD : Real.exp (Real.pi * Real.exp (779 / 400 : ℝ) - (1557 / 3200 : ℝ)) ≤
      (22621441965405014169 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1557_denomUpper
    linarith [hpThetaJensenCell1557_product_upper]
  have hi : (1 / (22621441965405014169 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (779 / 400 : ℝ) - (1557 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22621441965405014169 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22621441965405014169 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1557 / 3200 : ℝ) - Real.pi * Real.exp (779 / 400 : ℝ)) := by
    rw [show (1557 / 3200 : ℝ) - Real.pi * Real.exp (779 / 400 : ℝ) =
      -(Real.pi * Real.exp (779 / 400 : ℝ) - (1557 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1557 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1557 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1557_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22621441965405014169 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1557_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1557 / 1600 : ℝ) (779 / 800 : ℝ) ≤ (4121 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (779 / 400 : ℝ)) (220261414599623033 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (779 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1557_product_upper
  have hD : (11000228614515505129 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1557 / 800 : ℝ) - (779 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1557_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1557_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1557 / 800 : ℝ) - (779 / 1600 : ℝ)) ≤
      (1 / (11000228614515505129 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11000228614515505129 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((779 / 1600 : ℝ) - Real.pi * Real.exp (1557 / 800 : ℝ)) ≤
      (2 / (11000228614515505129 / 5000000000 : ℝ) : ℝ) := by
    rw [show (779 / 1600 : ℝ) - Real.pi * Real.exp (1557 / 800 : ℝ) =
      -(Real.pi * Real.exp (1557 / 800 : ℝ) - (779 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (220261414599623033 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (220261414599623033 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1557_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1557 / 1600 : ℝ) (779 / 800 : ℝ)) :
    (15947 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4121 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1557_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1557_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1558_leftExp :
    (35055689039 / 5000000000 : ℝ) ≤ Real.exp (779 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (779 / 400 : ℝ) (132843681817 / 125000000000 : ℝ)
    (35055689039 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1558_rightExp :
    Real.exp (1559 / 800 : ℝ) ≤ (70199072101 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1559 / 800 : ℝ) (531395484499 / 500000000000 : ℝ)
    (70199072101 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1558_denomUpper :
    Real.exp (215668163518996893 / 10000000000000000 : ℝ) ≤ (23246058899544055043 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (215668163518996893 / 10000000000000000 : ℝ)
    (245249668877 / 125000000000 : ℝ) (23246058899544055043 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1558_denomLower :
    (22607149450463691829 / 10000000000 : ℝ) ≤ Real.exp (13461841842426261 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (13461841842426261 / 625000000000000 : ℝ) (98014467717 /
    50000000000 : ℝ) (22607149450463691829 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1558_product_lower :
    (13766334029926261 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (779 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1558_leftExp
    (by norm_num : (0 : ℝ) ≤ (35055689039 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1558_product_upper :
    Real.pi * Real.exp (1559 / 800 : ℝ) ≤ (220536913518996893 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1558_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1558_endpointLower :
    (15559 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (779 / 800 : ℝ) (1559 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13766334029926261 / 625000000000000 : ℝ) (Real.pi * Real.exp (779 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1558_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1559 / 800 : ℝ) - (779 / 1600 : ℝ)) ≤
      (23246058899544055043 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1558_denomUpper
    linarith [hpThetaJensenCell1558_product_upper]
  have hi : (1 / (23246058899544055043 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1559 / 800 : ℝ) - (779 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23246058899544055043 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23246058899544055043 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((779 / 1600 : ℝ) - Real.pi * Real.exp (1559 / 800 : ℝ)) := by
    rw [show (779 / 1600 : ℝ) - Real.pi * Real.exp (1559 / 800 : ℝ) =
      -(Real.pi * Real.exp (1559 / 800 : ℝ) - (779 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (779 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (779 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1558_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23246058899544055043 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1558_endpointUpper :
    hpThetaJensenKernelEndpointUpper (779 / 800 : ℝ) (1559 / 1600 : ℝ) ≤ (16083 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1559 / 800 : ℝ)) (220536913518996893 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1559 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1558_product_upper
  have hD : (22607149450463691829 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (779 / 400 : ℝ) - (1559 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1558_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1558_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (779 / 400 : ℝ) - (1559 / 3200 : ℝ)) ≤
      (1 / (22607149450463691829 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (22607149450463691829 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1559 / 3200 : ℝ) - Real.pi * Real.exp (779 / 400 : ℝ)) ≤
      (2 / (22607149450463691829 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1559 / 3200 : ℝ) - Real.pi * Real.exp (779 / 400 : ℝ) =
      -(Real.pi * Real.exp (779 / 400 : ℝ) - (1559 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (220536913518996893 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (220536913518996893 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1558_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (779 / 800 : ℝ) (1559 / 1600 : ℝ)) :
    (15559 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16083 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1558_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1558_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1559_leftExp :
    (70199072097 / 10000000000 : ℝ) ≤ Real.exp (1559 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1559 / 800 : ℝ) (1062790968997 / 1000000000000 : ℝ)
    (70199072097 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1559_rightExp :
    Real.exp (39 / 20 : ℝ) ≤ (35143437903 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 20 : ℝ) (1062832485081 / 1000000000000 : ℝ)
    (35143437903 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1559_denomUpper :
    Real.exp (107970441011999479 / 5000000000000000 : ℝ) ≤ (1194437286955298767 / 500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (107970441011999479 / 5000000000000000 : ℝ) (392734033363
    / 200000000000 : ℝ) (1194437286955298767 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1559_denomLower :
    (2903921441511315789 / 1250000000 : ℝ) ≤ Real.exp (26957730413419803 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26957730413419803 / 1250000000000000 : ℝ) (245244825079
    / 125000000000 : ℝ) (2903921441511315789 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1559_product_lower :
    (27567105413419803 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1559 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1559_leftExp
    (by norm_num : (0 : ℝ) ≤ (70199072097 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1559_product_upper :
    Real.pi * Real.exp (39 / 20 : ℝ) ≤ (110406378511999479 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1559_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1559_endpointLower :
    (15179 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1559 / 1600 : ℝ) (39 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27567105413419803 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1559 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1559_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 20 : ℝ) - (1559 / 3200 : ℝ)) ≤
      (1194437286955298767 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1559_denomUpper
    linarith [hpThetaJensenCell1559_product_upper]
  have hi : (1 / (1194437286955298767 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 20 : ℝ) - (1559 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1194437286955298767 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1194437286955298767 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1559 / 3200 : ℝ) - Real.pi * Real.exp (39 / 20 : ℝ)) := by
    rw [show (1559 / 3200 : ℝ) - Real.pi * Real.exp (39 / 20 : ℝ) =
      -(Real.pi * Real.exp (39 / 20 : ℝ) - (1559 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1559 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1559 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1559_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1194437286955298767 / 500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1559_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1559 / 1600 : ℝ) (39 / 40 : ℝ) ≤ (3923 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 20 : ℝ)) (110406378511999479 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1559_product_upper
  have hD : (2903921441511315789 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1559 / 800 : ℝ) - (39 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell1559_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1559_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1559 / 800 : ℝ) - (39 / 80 : ℝ)) ≤
      (1 / (2903921441511315789 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2903921441511315789 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 80 : ℝ) - Real.pi * Real.exp (1559 / 800 : ℝ)) ≤
      (2 / (2903921441511315789 / 1250000000 : ℝ) : ℝ) := by
    rw [show (39 / 80 : ℝ) - Real.pi * Real.exp (1559 / 800 : ℝ) =
      -(Real.pi * Real.exp (1559 / 800 : ℝ) - (39 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (110406378511999479 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (110406378511999479 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1559_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1559 / 1600 : ℝ) (39 / 40 : ℝ)) :
    (15179 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3923 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1559_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1559_endpointUpper

def hpThetaJensenCellsBatch077Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (24119 / 10000000000 : ℝ)
  | 1 => (11773 / 5000000000 : ℝ)
  | 2 => (4597 / 2000000000 : ℝ)
  | 3 => (22437 / 10000000000 : ℝ)
  | 4 => (21901 / 10000000000 : ℝ)
  | 5 => (10689 / 5000000000 : ℝ)
  | 6 => (10433 / 5000000000 : ℝ)
  | 7 => (4073 / 2000000000 : ℝ)
  | 8 => (4969 / 2500000000 : ℝ)
  | 9 => (19399 / 10000000000 : ℝ)
  | 10 => (18931 / 10000000000 : ℝ)
  | 11 => (739 / 400000000 : ℝ)
  | 12 => (18029 / 10000000000 : ℝ)
  | 13 => (17593 / 10000000000 : ℝ)
  | 14 => (17167 / 10000000000 : ℝ)
  | 15 => (16751 / 10000000000 : ℝ)
  | 16 => (2043 / 1250000000 : ℝ)
  | 17 => (15947 / 10000000000 : ℝ)
  | 18 => (15559 / 10000000000 : ℝ)
  | 19 => (15179 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch077Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6229 / 2500000000 : ℝ)
  | 1 => (973 / 400000000 : ℝ)
  | 2 => (11873 / 5000000000 : ℝ)
  | 3 => (23181 / 10000000000 : ℝ)
  | 4 => (5657 / 2500000000 : ℝ)
  | 5 => (2761 / 1250000000 : ℝ)
  | 6 => (539 / 250000000 : ℝ)
  | 7 => (5261 / 2500000000 : ℝ)
  | 8 => (20539 / 10000000000 : ℝ)
  | 9 => (10023 / 5000000000 : ℝ)
  | 10 => (4891 / 2500000000 : ℝ)
  | 11 => (19093 / 10000000000 : ℝ)
  | 12 => (18633 / 10000000000 : ℝ)
  | 13 => (18183 / 10000000000 : ℝ)
  | 14 => (17743 / 10000000000 : ℝ)
  | 15 => (8657 / 5000000000 : ℝ)
  | 16 => (8447 / 5000000000 : ℝ)
  | 17 => (4121 / 2500000000 : ℝ)
  | 18 => (16083 / 10000000000 : ℝ)
  | 19 => (3923 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch077_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch077Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch077Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1540_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1541_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1542_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1543_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1544_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1545_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1546_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1547_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1548_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1549_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1550_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1551_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1552_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1553_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1554_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1555_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1556_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1557_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1558_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1559_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper] at h ⊢
    exact h

end HodgeProofHP
