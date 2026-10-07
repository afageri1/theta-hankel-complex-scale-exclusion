import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1120_leftExp :
    (40551999667 / 10000000000 : ℝ) ≤ Real.exp (7 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 5 : ℝ) (16323767843 / 15625000000 : ℝ) (40551999667
    / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1120_rightExp :
    Real.exp (1121 / 800 : ℝ) ≤ (10150680341 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1121 / 800 : ℝ) (104476195217 / 100000000000 : ℝ)
    (10150680341 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1120_denomUpper :
    Real.exp (31014306304523213 / 2500000000000000 : ℝ) ≤ (2441950381886247 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (31014306304523213 / 2500000000000000 : ℝ) (1473556444399
    / 1000000000000 : ℝ) (2441950381886247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1120_denomLower :
    (2402586364071679 / 10000000000 : ℝ) ≤ Real.exp (15486839092231233 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15486839092231233 / 1250000000000000 : ℝ) (1472808286539
    / 1000000000000 : ℝ) (2402586364071679 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1120_product_lower :
    (15924729717231233 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1120_leftExp
    (by norm_num : (0 : ℝ) ≤ (40551999667 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1120_product_upper :
    Real.pi * Real.exp (1121 / 800 : ℝ) ≤ (31889306304523213 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1120_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1120_endpointLower :
    (9382167 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 10 : ℝ) (1121 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15924729717231233 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell1120_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1121 / 800 : ℝ) - (7 / 20 : ℝ)) ≤
      (2441950381886247 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1120_denomUpper
    linarith [hpThetaJensenCell1120_product_upper]
  have hi : (1 / (2441950381886247 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1121 / 800 : ℝ) - (7 / 20 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2441950381886247 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2441950381886247 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 20 : ℝ) - Real.pi * Real.exp (1121 / 800 : ℝ)) := by
    rw [show (7 / 20 : ℝ) - Real.pi * Real.exp (1121 / 800 : ℝ) =
      -(Real.pi * Real.exp (1121 / 800 : ℝ) - (7 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 5 : ℝ)) := by
    have h := hpThetaJensenCell1120_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2441950381886247 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1120_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 10 : ℝ) (1121 / 1600 : ℝ) ≤ (47932673 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1121 / 800 : ℝ)) (31889306304523213 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1121 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1120_product_upper
  have hD : (2402586364071679 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 5 : ℝ) - (1121 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1120_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1120_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 5 : ℝ) - (1121 / 3200 : ℝ)) ≤
      (1 / (2402586364071679 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2402586364071679 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1121 / 3200 : ℝ) - Real.pi * Real.exp (7 / 5 : ℝ)) ≤
      (2 / (2402586364071679 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1121 / 3200 : ℝ) - Real.pi * Real.exp (7 / 5 : ℝ) =
      -(Real.pi * Real.exp (7 / 5 : ℝ) - (1121 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (31889306304523213 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (31889306304523213 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1120_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 10 : ℝ) (1121 / 1600 : ℝ)) :
    (9382167 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (47932673 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1120_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1120_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1121_leftExp :
    (20301360681 / 5000000000 : ℝ) ≤ Real.exp (1121 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1121 / 800 : ℝ) (1044761952169 / 1000000000000 : ℝ)
    (20301360681 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1121_rightExp :
    Real.exp (561 / 400 : ℝ) ≤ (81307013 / 20000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (561 / 400 : ℝ) (1044802763981 / 1000000000000 : ℝ)
    (81307013 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1121_denomUpper :
    Real.exp (248427292891709 / 20000000000000 : ℝ) ≤ (2480447976693007 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (248427292891709 / 20000000000000 : ℝ) (737138459469 /
    500000000000 : ℝ) (2480447976693007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1121_denomLower :
    (2440414729414933 / 10000000000 : ℝ) ≤ Real.exp (7753183413068019 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7753183413068019 / 625000000000000 : ℝ) (294705495457 /
    200000000000 : ℝ) (2440414729414933 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1121_product_lower :
    (7972324038068019 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1121 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1121_leftExp
    (by norm_num : (0 : ℝ) ≤ (20301360681 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1121_product_upper :
    Real.pi * Real.exp (561 / 400 : ℝ) ≤ (255433542891709 / 20000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1121_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1121_endpointLower :
    (46306079 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1121 / 1600 : ℝ) (561 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7972324038068019 / 625000000000000 : ℝ) (Real.pi * Real.exp (1121 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1121_product_lower
  have hD : Real.exp (Real.pi * Real.exp (561 / 400 : ℝ) - (1121 / 3200 : ℝ)) ≤
      (2480447976693007 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1121_denomUpper
    linarith [hpThetaJensenCell1121_product_upper]
  have hi : (1 / (2480447976693007 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (561 / 400 : ℝ) - (1121 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2480447976693007 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2480447976693007 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1121 / 3200 : ℝ) - Real.pi * Real.exp (561 / 400 : ℝ)) := by
    rw [show (1121 / 3200 : ℝ) - Real.pi * Real.exp (561 / 400 : ℝ) =
      -(Real.pi * Real.exp (561 / 400 : ℝ) - (1121 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1121 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1121 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1121_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2480447976693007 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1121_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1121 / 1600 : ℝ) (561 / 800 : ℝ) ≤ (11828919 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (561 / 400 : ℝ)) (255433542891709 / 20000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (561 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1121_product_upper
  have hD : (2440414729414933 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1121 / 800 : ℝ) - (561 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1121_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1121_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1121 / 800 : ℝ) - (561 / 1600 : ℝ)) ≤
      (1 / (2440414729414933 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2440414729414933 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((561 / 1600 : ℝ) - Real.pi * Real.exp (1121 / 800 : ℝ)) ≤
      (2 / (2440414729414933 / 10000000000 : ℝ) : ℝ) := by
    rw [show (561 / 1600 : ℝ) - Real.pi * Real.exp (1121 / 800 : ℝ) =
      -(Real.pi * Real.exp (1121 / 800 : ℝ) - (561 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (255433542891709 / 20000000000000 : ℝ) ^ 2 - 6 *
      (255433542891709 / 20000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1121_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1121 / 1600 : ℝ) (561 / 800 : ℝ)) :
    (46306079 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11828919 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1121_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1121_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1122_leftExp :
    (40653506497 / 10000000000 : ℝ) ≤ Real.exp (561 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (561 / 400 : ℝ) (52240138199 / 50000000000 : ℝ)
    (40653506497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1122_rightExp :
    Real.exp (1123 / 800 : ℝ) ≤ (40704355157 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1123 / 800 : ℝ) (522421788693 / 500000000000 : ℝ)
    (40704355157 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1122_denomUpper :
    Real.exp (124370267230745101 / 10000000000000000 : ℝ) ≤ (629900692481457 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (124370267230745101 / 10000000000000000 : ℝ) (58999946623
    / 40000000000 : ℝ) (629900692481457 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1122_denomLower :
    (1239444050555241 / 5000000000 : ℝ) ≤ Real.exp (15525919472865403 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15525919472865403 / 1250000000000000 : ℝ) (368561984353
    / 250000000000 : ℝ) (1239444050555241 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1122_product_lower :
    (15964591347865403 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (561 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1122_leftExp
    (by norm_num : (0 : ℝ) ≤ (40653506497 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1122_product_upper :
    Real.pi * Real.exp (1123 / 800 : ℝ) ≤ (127876517230745101 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1122_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1122_endpointLower :
    (11427049 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (561 / 800 : ℝ) (1123 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15964591347865403 / 1250000000000000 : ℝ) (Real.pi * Real.exp (561 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1122_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1123 / 800 : ℝ) - (561 / 1600 : ℝ)) ≤
      (629900692481457 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1122_denomUpper
    linarith [hpThetaJensenCell1122_product_upper]
  have hi : (1 / (629900692481457 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1123 / 800 : ℝ) - (561 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (629900692481457 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (629900692481457 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((561 / 1600 : ℝ) - Real.pi * Real.exp (1123 / 800 : ℝ)) := by
    rw [show (561 / 1600 : ℝ) - Real.pi * Real.exp (1123 / 800 : ℝ) =
      -(Real.pi * Real.exp (1123 / 800 : ℝ) - (561 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (561 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (561 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1122_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (629900692481457 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1122_endpointUpper :
    hpThetaJensenKernelEndpointUpper (561 / 800 : ℝ) (1123 / 1600 : ℝ) ≤ (46705679 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1123 / 800 : ℝ)) (127876517230745101 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1123 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1122_product_upper
  have hD : (1239444050555241 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (561 / 400 : ℝ) - (1123 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1122_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1122_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (561 / 400 : ℝ) - (1123 / 3200 : ℝ)) ≤
      (1 / (1239444050555241 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1239444050555241 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1123 / 3200 : ℝ) - Real.pi * Real.exp (561 / 400 : ℝ)) ≤
      (2 / (1239444050555241 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1123 / 3200 : ℝ) - Real.pi * Real.exp (561 / 400 : ℝ) =
      -(Real.pi * Real.exp (561 / 400 : ℝ) - (1123 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (127876517230745101 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (127876517230745101 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1122_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (561 / 800 : ℝ) (1123 / 1600 : ℝ)) :
    (11427049 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (46705679 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1122_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1122_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1123_leftExp :
    (20352177577 / 5000000000 : ℝ) ≤ Real.exp (1123 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1123 / 800 : ℝ) (208968715477 / 200000000000 : ℝ)
    (20352177577 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1123_rightExp :
    Real.exp (281 / 200 : ℝ) ≤ (20377633707 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (281 / 200 : ℝ) (208976878477 / 200000000000 : ℝ)
    (20377633707 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1123_denomUpper :
    Real.exp (62263543910475251 / 5000000000000000 : ℝ) ≤ (2559426774316137 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (62263543910475251 / 5000000000000000 : ℝ) (737860843489
    / 500000000000 : ℝ) (2559426774316137 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1123_denomLower :
    (1259009129149939 / 5000000000 : ℝ) ≤ Real.exp (7772748532310323 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7772748532310323 / 625000000000000 : ℝ) (737484834813 /
    500000000000 : ℝ) (1259009129149939 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1123_product_lower :
    (7992279782310323 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1123 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1123_leftExp
    (by norm_num : (0 : ℝ) ≤ (20352177577 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1123_product_upper :
    Real.pi * Real.exp (281 / 200 : ℝ) ≤ (64018231410475251 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1123_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1123_endpointLower :
    (45117121 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1123 / 1600 : ℝ) (281 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7992279782310323 / 625000000000000 : ℝ) (Real.pi * Real.exp (1123 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1123_product_lower
  have hD : Real.exp (Real.pi * Real.exp (281 / 200 : ℝ) - (1123 / 3200 : ℝ)) ≤
      (2559426774316137 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1123_denomUpper
    linarith [hpThetaJensenCell1123_product_upper]
  have hi : (1 / (2559426774316137 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (281 / 200 : ℝ) - (1123 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2559426774316137 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2559426774316137 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1123 / 3200 : ℝ) - Real.pi * Real.exp (281 / 200 : ℝ)) := by
    rw [show (1123 / 3200 : ℝ) - Real.pi * Real.exp (281 / 200 : ℝ) =
      -(Real.pi * Real.exp (281 / 200 : ℝ) - (1123 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1123 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1123 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1123_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2559426774316137 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1123_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1123 / 1600 : ℝ) (281 / 400 : ℝ) ≤ (5762827 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (281 / 200 : ℝ)) (64018231410475251 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (281 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1123_product_upper
  have hD : (1259009129149939 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1123 / 800 : ℝ) - (281 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1123_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1123_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1123 / 800 : ℝ) - (281 / 800 : ℝ)) ≤
      (1 / (1259009129149939 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1259009129149939 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((281 / 800 : ℝ) - Real.pi * Real.exp (1123 / 800 : ℝ)) ≤
      (2 / (1259009129149939 / 5000000000 : ℝ) : ℝ) := by
    rw [show (281 / 800 : ℝ) - Real.pi * Real.exp (1123 / 800 : ℝ) =
      -(Real.pi * Real.exp (1123 / 800 : ℝ) - (281 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64018231410475251 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (64018231410475251 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1123_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1123 / 1600 : ℝ) (281 / 400 : ℝ)) :
    (45117121 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5762827 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1123_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1123_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1124_leftExp :
    (40755267411 / 10000000000 : ℝ) ≤ Real.exp (281 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (281 / 200 : ℝ) (16326318631 / 15625000000 : ℝ)
    (40755267411 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1124_rightExp :
    Real.exp (45 / 32 : ℝ) ≤ (40806243351 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45 / 32 : ℝ) (1044925208979 / 1000000000000 : ℝ)
    (40806243351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1124_denomUpper :
    Real.exp (124684108467798143 / 10000000000000000 : ℝ) ≤ (2599932236562007 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (124684108467798143 / 10000000000000000 : ℝ)
    (295289197167 / 200000000000 : ℝ) (2599932236562007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1124_denomLower :
    (2557817205411521 / 10000000000 : ℝ) ≤ Real.exp (15565099632032289 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15565099632032289 / 1250000000000000 : ℝ) (1475692676581
    / 1000000000000 : ℝ) (2557817205411521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1124_product_lower :
    (16004552757032289 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (281 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1124_leftExp
    (by norm_num : (0 : ℝ) ≤ (40755267411 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1124_product_upper :
    Real.pi * Real.exp (45 / 32 : ℝ) ≤ (128196608467798143 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1124_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1124_endpointLower :
    (11133197 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (281 / 400 : ℝ) (45 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16004552757032289 / 1250000000000000 : ℝ) (Real.pi * Real.exp (281 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1124_product_lower
  have hD : Real.exp (Real.pi * Real.exp (45 / 32 : ℝ) - (281 / 800 : ℝ)) ≤
      (2599932236562007 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1124_denomUpper
    linarith [hpThetaJensenCell1124_product_upper]
  have hi : (1 / (2599932236562007 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (45 / 32 : ℝ) - (281 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2599932236562007 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2599932236562007 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((281 / 800 : ℝ) - Real.pi * Real.exp (45 / 32 : ℝ)) := by
    rw [show (281 / 800 : ℝ) - Real.pi * Real.exp (45 / 32 : ℝ) =
      -(Real.pi * Real.exp (45 / 32 : ℝ) - (281 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (281 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (281 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1124_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2599932236562007 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1124_endpointUpper :
    hpThetaJensenKernelEndpointUpper (281 / 400 : ℝ) (45 / 64 : ℝ) ≤ (45506419 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (45 / 32 : ℝ)) (128196608467798143 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (45 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1124_product_upper
  have hD : (2557817205411521 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (281 / 200 : ℝ) - (45 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1124_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1124_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (281 / 200 : ℝ) - (45 / 128 : ℝ)) ≤
      (1 / (2557817205411521 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2557817205411521 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((45 / 128 : ℝ) - Real.pi * Real.exp (281 / 200 : ℝ)) ≤
      (2 / (2557817205411521 / 10000000000 : ℝ) : ℝ) := by
    rw [show (45 / 128 : ℝ) - Real.pi * Real.exp (281 / 200 : ℝ) =
      -(Real.pi * Real.exp (281 / 200 : ℝ) - (45 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (128196608467798143 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (128196608467798143 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1124_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (281 / 400 : ℝ) (45 / 64 : ℝ)) :
    (11133197 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (45506419 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1124_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1124_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1125_leftExp :
    (40806243349 / 10000000000 : ℝ) ≤ Real.exp (45 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (45 / 32 : ℝ) (522462604489 / 500000000000 : ℝ)
    (40806243349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1125_rightExp :
    Real.exp (563 / 400 : ℝ) ≤ (5107160381 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (563 / 400 : ℝ) (1044966027167 / 1000000000000 : ℝ)
    (5107160381 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1125_denomUpper :
    Real.exp (15605166177826933 / 1250000000000000 : ℝ) ≤ (1320565820624263 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (15605166177826933 / 1250000000000000 : ℝ) (738585782419
    / 500000000000 : ℝ) (1320565820624263 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1125_denomLower :
    (649574295555921 / 2500000000 : ℝ) ≤ Real.exp (15584727206908951 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15584727206908951 / 1250000000000000 : ℝ) (1476416960979
    / 1000000000000 : ℝ) (649574295555921 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1125_product_lower :
    (16024570956908951 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (45 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1125_leftExp
    (by norm_num : (0 : ℝ) ≤ (40806243349 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1125_product_upper :
    Real.pi * Real.exp (563 / 400 : ℝ) ≤ (16044619302826933 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1125_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1125_endpointLower :
    (10988783 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (45 / 64 : ℝ) (563 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16024570956908951 / 1250000000000000 : ℝ) (Real.pi * Real.exp (45 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1125_product_lower
  have hD : Real.exp (Real.pi * Real.exp (563 / 400 : ℝ) - (45 / 128 : ℝ)) ≤
      (1320565820624263 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1125_denomUpper
    linarith [hpThetaJensenCell1125_product_upper]
  have hi : (1 / (1320565820624263 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (563 / 400 : ℝ) - (45 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1320565820624263 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1320565820624263 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((45 / 128 : ℝ) - Real.pi * Real.exp (563 / 400 : ℝ)) := by
    rw [show (45 / 128 : ℝ) - Real.pi * Real.exp (563 / 400 : ℝ) =
      -(Real.pi * Real.exp (563 / 400 : ℝ) - (45 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (45 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (45 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1125_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1320565820624263 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1125_endpointUpper :
    hpThetaJensenKernelEndpointUpper (45 / 64 : ℝ) (563 / 800 : ℝ) ≤ (44917023 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (563 / 400 : ℝ)) (16044619302826933 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (563 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1125_product_upper
  have hD : (649574295555921 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (45 / 32 : ℝ) - (563 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1125_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1125_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (45 / 32 : ℝ) - (563 / 1600 : ℝ)) ≤
      (1 / (649574295555921 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (649574295555921 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((563 / 1600 : ℝ) - Real.pi * Real.exp (45 / 32 : ℝ)) ≤
      (2 / (649574295555921 / 2500000000 : ℝ) : ℝ) := by
    rw [show (563 / 1600 : ℝ) - Real.pi * Real.exp (45 / 32 : ℝ) =
      -(Real.pi * Real.exp (45 / 32 : ℝ) - (563 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16044619302826933 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (16044619302826933 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1125_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (45 / 64 : ℝ) (563 / 800 : ℝ)) :
    (10988783 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (44917023 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1125_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1125_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1126_leftExp :
    (20428641523 / 5000000000 : ℝ) ≤ Real.exp (563 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (563 / 400 : ℝ) (522483013583 / 500000000000 : ℝ)
    (20428641523 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1126_rightExp :
    Real.exp (1127 / 800 : ℝ) ≤ (20454193293 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1127 / 800 : ℝ) (20900136939 / 20000000000 : ℝ)
    (20454193293 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1126_denomUpper :
    Real.exp (62499375469935749 / 5000000000000000 : ℝ) ≤ (1341518858382309 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (62499375469935749 / 5000000000000000 : ℝ) (1477898426701
    / 1000000000000 : ℝ) (1341518858382309 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1126_denomLower :
    (329933832980209 / 1250000000 : ℝ) ≤ Real.exp (7802189909940577 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7802189909940577 / 625000000000000 : ℝ) (1477142525483 /
    1000000000000 : ℝ) (329933832980209 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1126_product_lower :
    (8022307097440577 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (563 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1126_leftExp
    (by norm_num : (0 : ℝ) ≤ (20428641523 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1126_product_upper :
    Real.pi * Real.exp (1127 / 800 : ℝ) ≤ (64258750469935749 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1126_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1126_endpointLower :
    (43384089 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (563 / 800 : ℝ) (1127 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8022307097440577 / 625000000000000 : ℝ) (Real.pi * Real.exp (563 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1126_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1127 / 800 : ℝ) - (563 / 1600 : ℝ)) ≤
      (1341518858382309 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1126_denomUpper
    linarith [hpThetaJensenCell1126_product_upper]
  have hi : (1 / (1341518858382309 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1127 / 800 : ℝ) - (563 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1341518858382309 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1341518858382309 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((563 / 1600 : ℝ) - Real.pi * Real.exp (1127 / 800 : ℝ)) := by
    rw [show (563 / 1600 : ℝ) - Real.pi * Real.exp (1127 / 800 : ℝ) =
      -(Real.pi * Real.exp (1127 / 800 : ℝ) - (563 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (563 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (563 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1126_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1341518858382309 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1126_endpointUpper :
    hpThetaJensenKernelEndpointUpper (563 / 800 : ℝ) (1127 / 1600 : ℝ) ≤ (44334363 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1127 / 800 : ℝ)) (64258750469935749 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1127 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1126_product_upper
  have hD : (329933832980209 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (563 / 400 : ℝ) - (1127 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1126_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1126_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (563 / 400 : ℝ) - (1127 / 3200 : ℝ)) ≤
      (1 / (329933832980209 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (329933832980209 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1127 / 3200 : ℝ) - Real.pi * Real.exp (563 / 400 : ℝ)) ≤
      (2 / (329933832980209 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1127 / 3200 : ℝ) - Real.pi * Real.exp (563 / 400 : ℝ) =
      -(Real.pi * Real.exp (563 / 400 : ℝ) - (1127 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64258750469935749 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (64258750469935749 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1126_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (563 / 800 : ℝ) (1127 / 1600 : ℝ)) :
    (43384089 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (44334363 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1126_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1126_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1127_leftExp :
    (40908386583 / 10000000000 : ℝ) ≤ Real.exp (1127 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1127 / 800 : ℝ) (1045006846949 / 1000000000000 : ℝ)
    (40908386583 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1127_rightExp :
    Real.exp (141 / 100 : ℝ) ≤ (20479777021 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (141 / 100 : ℝ) (1045047668327 / 1000000000000 : ℝ)
    (20479777021 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1127_denomUpper :
    Real.exp (62578186630734453 / 5000000000000000 : ℝ) ≤ (1362831717938043 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (62578186630734453 / 5000000000000000 : ℝ) (369656643521
    / 250000000000 : ℝ) (1362831717938043 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1127_denomLower :
    (536270074109243 / 2000000000 : ℝ) ≤ Real.exp (15624057502757517 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15624057502757517 / 1250000000000000 : ℝ) (738934686403
    / 500000000000 : ℝ) (536270074109243 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1127_product_lower :
    (16064682502757517 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1127 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1127_leftExp
    (by norm_num : (0 : ℝ) ≤ (40908386583 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1127_product_upper :
    Real.pi * Real.exp (141 / 100 : ℝ) ≤ (64339124130734453 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1127_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1127_endpointLower :
    (8563919 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1127 / 1600 : ℝ) (141 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16064682502757517 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1127 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1127_product_lower
  have hD : Real.exp (Real.pi * Real.exp (141 / 100 : ℝ) - (1127 / 3200 : ℝ)) ≤
      (1362831717938043 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1127_denomUpper
    linarith [hpThetaJensenCell1127_product_upper]
  have hi : (1 / (1362831717938043 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (141 / 100 : ℝ) - (1127 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1362831717938043 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1362831717938043 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1127 / 3200 : ℝ) - Real.pi * Real.exp (141 / 100 : ℝ)) := by
    rw [show (1127 / 3200 : ℝ) - Real.pi * Real.exp (141 / 100 : ℝ) =
      -(Real.pi * Real.exp (141 / 100 : ℝ) - (1127 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1127 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1127 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1127_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1362831717938043 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1127_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1127 / 1600 : ℝ) (141 / 200 : ℝ) ≤ (43758373 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (141 / 100 : ℝ)) (64339124130734453 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (141 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1127_product_upper
  have hD : (536270074109243 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1127 / 800 : ℝ) - (141 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1127_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1127_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1127 / 800 : ℝ) - (141 / 400 : ℝ)) ≤
      (1 / (536270074109243 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (536270074109243 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((141 / 400 : ℝ) - Real.pi * Real.exp (1127 / 800 : ℝ)) ≤
      (2 / (536270074109243 / 2000000000 : ℝ) : ℝ) := by
    rw [show (141 / 400 : ℝ) - Real.pi * Real.exp (1127 / 800 : ℝ) =
      -(Real.pi * Real.exp (1127 / 800 : ℝ) - (141 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64339124130734453 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (64339124130734453 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1127_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1127 / 1600 : ℝ) (141 / 200 : ℝ)) :
    (8563919 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (43758373 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1127_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1127_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1128_leftExp :
    (40959554039 / 10000000000 : ℝ) ≤ Real.exp (141 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (141 / 100 : ℝ) (522523834163 / 500000000000 : ℝ)
    (40959554039 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1128_rightExp :
    Real.exp (1129 / 800 : ℝ) ≤ (41010785497 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1129 / 800 : ℝ) (1045088491299 / 1000000000000 : ℝ)
    (41010785497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1128_denomUpper :
    Real.exp (125314196641876721 / 10000000000000000 : ℝ) ≤ (553804405523033 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (125314196641876721 / 10000000000000000 : ℝ)
    (1479356009711 / 1000000000000 : ℝ) (553804405523033 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1128_denomLower :
    (85123414645743 / 312500000 : ℝ) ≤ Real.exp (15643760286561261 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15643760286561261 / 1250000000000000 : ℝ) (739298752819
    / 500000000000 : ℝ) (85123414645743 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1128_product_lower :
    (16084775911561261 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (141 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1128_leftExp
    (by norm_num : (0 : ℝ) ≤ (40959554039 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1128_product_upper :
    Real.pi * Real.exp (1129 / 800 : ℝ) ≤ (128839196641876721 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1128_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1128_endpointLower :
    (21130793 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (141 / 200 : ℝ) (1129 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16084775911561261 / 1250000000000000 : ℝ) (Real.pi * Real.exp (141 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1128_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1129 / 800 : ℝ) - (141 / 400 : ℝ)) ≤
      (553804405523033 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1128_denomUpper
    linarith [hpThetaJensenCell1128_product_upper]
  have hi : (1 / (553804405523033 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1129 / 800 : ℝ) - (141 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (553804405523033 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (553804405523033 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((141 / 400 : ℝ) - Real.pi * Real.exp (1129 / 800 : ℝ)) := by
    rw [show (141 / 400 : ℝ) - Real.pi * Real.exp (1129 / 800 : ℝ) =
      -(Real.pi * Real.exp (1129 / 800 : ℝ) - (141 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (141 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (141 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1128_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (553804405523033 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1128_endpointUpper :
    hpThetaJensenKernelEndpointUpper (141 / 200 : ℝ) (1129 / 1600 : ℝ) ≤ (10797247 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1129 / 800 : ℝ)) (128839196641876721 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1129 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1128_product_upper
  have hD : (85123414645743 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (141 / 100 : ℝ) - (1129 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1128_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1128_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (141 / 100 : ℝ) - (1129 / 3200 : ℝ)) ≤
      (1 / (85123414645743 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (85123414645743 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1129 / 3200 : ℝ) - Real.pi * Real.exp (141 / 100 : ℝ)) ≤
      (2 / (85123414645743 / 312500000 : ℝ) : ℝ) := by
    rw [show (1129 / 3200 : ℝ) - Real.pi * Real.exp (141 / 100 : ℝ) =
      -(Real.pi * Real.exp (141 / 100 : ℝ) - (1129 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (128839196641876721 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (128839196641876721 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1128_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (141 / 200 : ℝ) (1129 / 1600 : ℝ)) :
    (21130793 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10797247 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1128_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1128_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1129_leftExp :
    (8202157099 / 2000000000 : ℝ) ≤ Real.exp (1129 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1129 / 800 : ℝ) (522544245649 / 500000000000 : ℝ)
    (8202157099 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1129_rightExp :
    Real.exp (113 / 80 : ℝ) ≤ (41062081033 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (113 / 80 : ℝ) (522564657933 / 500000000000 : ℝ)
    (41062081033 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1129_denomUpper :
    Real.exp (125472221338705569 / 10000000000000000 : ℝ) ≤ (562625396001331 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (125472221338705569 / 10000000000000000 : ℝ) (59203469453
    / 40000000000 : ℝ) (562625396001331 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1129_denomLower :
    (553456115775603 / 2000000000 : ℝ) ≤ Real.exp (3132697640620201 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3132697640620201 / 250000000000000 : ℝ) (739663463351 /
    500000000000 : ℝ) (553456115775603 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1129_product_lower :
    (3220978890620201 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1129 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1129_leftExp
    (by norm_num : (0 : ℝ) ≤ (8202157099 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1129_product_upper :
    Real.pi * Real.exp (113 / 80 : ℝ) ≤ (129000346338705569 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1129_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1129_endpointLower :
    (41709999 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1129 / 1600 : ℝ) (113 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3220978890620201 / 250000000000000 : ℝ) (Real.pi * Real.exp (1129 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1129_product_lower
  have hD : Real.exp (Real.pi * Real.exp (113 / 80 : ℝ) - (1129 / 3200 : ℝ)) ≤
      (562625396001331 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1129_denomUpper
    linarith [hpThetaJensenCell1129_product_upper]
  have hi : (1 / (562625396001331 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (113 / 80 : ℝ) - (1129 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (562625396001331 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (562625396001331 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1129 / 3200 : ℝ) - Real.pi * Real.exp (113 / 80 : ℝ)) := by
    rw [show (1129 / 3200 : ℝ) - Real.pi * Real.exp (113 / 80 : ℝ) =
      -(Real.pi * Real.exp (113 / 80 : ℝ) - (1129 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1129 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1129 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1129_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (562625396001331 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1129_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1129 / 1600 : ℝ) (113 / 160 : ℝ) ≤ (21313073 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (113 / 80 : ℝ)) (129000346338705569 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (113 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1129_product_upper
  have hD : (553456115775603 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1129 / 800 : ℝ) - (113 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1129_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1129_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1129 / 800 : ℝ) - (113 / 320 : ℝ)) ≤
      (1 / (553456115775603 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (553456115775603 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((113 / 320 : ℝ) - Real.pi * Real.exp (1129 / 800 : ℝ)) ≤
      (2 / (553456115775603 / 2000000000 : ℝ) : ℝ) := by
    rw [show (113 / 320 : ℝ) - Real.pi * Real.exp (1129 / 800 : ℝ) =
      -(Real.pi * Real.exp (1129 / 800 : ℝ) - (113 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (129000346338705569 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (129000346338705569 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1129_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1129 / 1600 : ℝ) (113 / 160 : ℝ)) :
    (41709999 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (21313073 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1129_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1129_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1130_leftExp :
    (41062081031 / 10000000000 : ℝ) ≤ Real.exp (113 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (113 / 80 : ℝ) (209025863173 / 200000000000 : ℝ)
    (41062081031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1130_rightExp :
    Real.exp (1131 / 800 : ℝ) ≤ (41113440727 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1131 / 800 : ℝ) (1045170142027 / 1000000000000 : ℝ)
    (41113440727 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1130_denomUpper :
    Real.exp (125630447593858111 / 10000000000000000 : ℝ) ≤ (285799204025721 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (125630447593858111 / 10000000000000000 : ℝ)
    (370204689151 / 250000000000 : ℝ) (285799204025721 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1130_denomLower :
    (351419722389933 / 1250000000 : ℝ) ≤ Real.exp (15683241283792669 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15683241283792669 / 1250000000000000 : ℝ) (740028819357
    / 500000000000 : ℝ) (351419722389933 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1130_product_lower :
    (16125038158792669 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (113 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1130_leftExp
    (by norm_num : (0 : ℝ) ≤ (41062081031 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1130_product_upper :
    Real.pi * Real.exp (1131 / 800 : ℝ) ≤ (129161697593858111 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1130_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1130_endpointLower :
    (10291193 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (113 / 160 : ℝ) (1131 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16125038158792669 / 1250000000000000 : ℝ) (Real.pi * Real.exp (113 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1130_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1131 / 800 : ℝ) - (113 / 320 : ℝ)) ≤
      (285799204025721 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1130_denomUpper
    linarith [hpThetaJensenCell1130_product_upper]
  have hi : (1 / (285799204025721 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1131 / 800 : ℝ) - (113 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (285799204025721 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (285799204025721 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((113 / 320 : ℝ) - Real.pi * Real.exp (1131 / 800 : ℝ)) := by
    rw [show (113 / 320 : ℝ) - Real.pi * Real.exp (1131 / 800 : ℝ) =
      -(Real.pi * Real.exp (1131 / 800 : ℝ) - (113 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (113 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (113 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1130_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (285799204025721 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1130_endpointUpper :
    hpThetaJensenKernelEndpointUpper (113 / 160 : ℝ) (1131 / 1600 : ℝ) ≤ (21034891 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1131 / 800 : ℝ)) (129161697593858111 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1131 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1130_product_upper
  have hD : (351419722389933 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (113 / 80 : ℝ) - (1131 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1130_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1130_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (113 / 80 : ℝ) - (1131 / 3200 : ℝ)) ≤
      (1 / (351419722389933 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (351419722389933 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1131 / 3200 : ℝ) - Real.pi * Real.exp (113 / 80 : ℝ)) ≤
      (2 / (351419722389933 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1131 / 3200 : ℝ) - Real.pi * Real.exp (113 / 80 : ℝ) =
      -(Real.pi * Real.exp (113 / 80 : ℝ) - (1131 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (129161697593858111 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (129161697593858111 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1130_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (113 / 160 : ℝ) (1131 / 1600 : ℝ)) :
    (10291193 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (21034891 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1130_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1130_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1131_leftExp :
    (1644537629 / 400000000 : ℝ) ≤ Real.exp (1131 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1131 / 800 : ℝ) (522585071013 / 500000000000 : ℝ)
    (1644537629 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1131_rightExp :
    Real.exp (283 / 200 : ℝ) ≤ (41164864661 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (283 / 200 : ℝ) (1045210969783 / 1000000000000 : ℝ)
    (41164864661 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1131_denomUpper :
    Real.exp (125788875664944973 / 10000000000000000 : ℝ) ≤ (1451815614346049 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (125788875664944973 / 10000000000000000 : ℝ)
    (740776036651 / 500000000000 : ℝ) (1451815614346049 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1131_denomLower :
    (2856194608644393 / 10000000000 : ℝ) ≤ Real.exp (628120782370671 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (628120782370671 / 50000000000000 : ℝ) (370197411091 /
    250000000000 : ℝ) (2856194608644393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1131_product_lower :
    (645808282370671 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1131 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1131_leftExp
    (by norm_num : (0 : ℝ) ≤ (1644537629 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1131_product_upper :
    Real.pi * Real.exp (283 / 200 : ℝ) ≤ (129323250664944973 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1131_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1131_endpointLower :
    (40625843 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1131 / 1600 : ℝ) (283 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (645808282370671 / 50000000000000 : ℝ) (Real.pi * Real.exp (1131 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1131_product_lower
  have hD : Real.exp (Real.pi * Real.exp (283 / 200 : ℝ) - (1131 / 3200 : ℝ)) ≤
      (1451815614346049 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1131_denomUpper
    linarith [hpThetaJensenCell1131_product_upper]
  have hi : (1 / (1451815614346049 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (283 / 200 : ℝ) - (1131 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1451815614346049 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1451815614346049 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1131 / 3200 : ℝ) - Real.pi * Real.exp (283 / 200 : ℝ)) := by
    rw [show (1131 / 3200 : ℝ) - Real.pi * Real.exp (283 / 200 : ℝ) =
      -(Real.pi * Real.exp (283 / 200 : ℝ) - (1131 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1131 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1131 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1131_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1451815614346049 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1131_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1131 / 1600 : ℝ) (283 / 400 : ℝ) ≤ (41519833 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (283 / 200 : ℝ)) (129323250664944973 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (283 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1131_product_upper
  have hD : (2856194608644393 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1131 / 800 : ℝ) - (283 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1131_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1131_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1131 / 800 : ℝ) - (283 / 800 : ℝ)) ≤
      (1 / (2856194608644393 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2856194608644393 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((283 / 800 : ℝ) - Real.pi * Real.exp (1131 / 800 : ℝ)) ≤
      (2 / (2856194608644393 / 10000000000 : ℝ) : ℝ) := by
    rw [show (283 / 800 : ℝ) - Real.pi * Real.exp (1131 / 800 : ℝ) =
      -(Real.pi * Real.exp (1131 / 800 : ℝ) - (283 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (129323250664944973 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (129323250664944973 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1131_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1131 / 1600 : ℝ) (283 / 400 : ℝ)) :
    (40625843 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (41519833 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1131_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1131_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1132_leftExp :
    (41164864659 / 10000000000 : ℝ) ≤ Real.exp (283 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (283 / 200 : ℝ) (522605484891 / 500000000000 : ℝ)
    (41164864659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1132_rightExp :
    Real.exp (1133 / 800 : ℝ) ≤ (8243270583 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1133 / 800 : ℝ) (522625899567 / 500000000000 : ℝ)
    (8243270583 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1132_denomUpper :
    Real.exp (25189501160658719 / 2000000000000000 : ℝ) ≤ (2950058838392953 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (25189501160658719 / 2000000000000000 : ℝ) (1482286689151
    / 1000000000000 : ℝ) (2950058838392953 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1132_denomLower :
    (181362817438191 / 625000000 : ℝ) ≤ Real.exp (15722823061724641 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15722823061724641 / 1250000000000000 : ℝ) (1481522946407
    / 1000000000000 : ℝ) (181362817438191 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1132_product_lower :
    (16165401186724641 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (283 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1132_leftExp
    (by norm_num : (0 : ℝ) ≤ (41164864659 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1132_product_upper :
    Real.pi * Real.exp (1133 / 800 : ℝ) ≤ (25897001160658719 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1132_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1132_endpointLower :
    (40093151 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (283 / 400 : ℝ) (1133 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16165401186724641 / 1250000000000000 : ℝ) (Real.pi * Real.exp (283 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1132_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1133 / 800 : ℝ) - (283 / 800 : ℝ)) ≤
      (2950058838392953 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1132_denomUpper
    linarith [hpThetaJensenCell1132_product_upper]
  have hi : (1 / (2950058838392953 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1133 / 800 : ℝ) - (283 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2950058838392953 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2950058838392953 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((283 / 800 : ℝ) - Real.pi * Real.exp (1133 / 800 : ℝ)) := by
    rw [show (283 / 800 : ℝ) - Real.pi * Real.exp (1133 / 800 : ℝ) =
      -(Real.pi * Real.exp (1133 / 800 : ℝ) - (283 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (283 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (283 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1132_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2950058838392953 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1132_endpointUpper :
    hpThetaJensenKernelEndpointUpper (283 / 400 : ℝ) (1133 / 1600 : ℝ) ≤ (40976237 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1133 / 800 : ℝ)) (25897001160658719 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1133 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1132_product_upper
  have hD : (181362817438191 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (283 / 200 : ℝ) - (1133 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1132_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1132_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (283 / 200 : ℝ) - (1133 / 3200 : ℝ)) ≤
      (1 / (181362817438191 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (181362817438191 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1133 / 3200 : ℝ) - Real.pi * Real.exp (283 / 200 : ℝ)) ≤
      (2 / (181362817438191 / 625000000 : ℝ) : ℝ) := by
    rw [show (1133 / 3200 : ℝ) - Real.pi * Real.exp (283 / 200 : ℝ) =
      -(Real.pi * Real.exp (283 / 200 : ℝ) - (1133 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25897001160658719 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (25897001160658719 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1132_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (283 / 400 : ℝ) (1133 / 1600 : ℝ)) :
    (40093151 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40976237 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1132_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1132_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1133_leftExp :
    (41216352913 / 10000000000 : ℝ) ≤ Real.exp (1133 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1133 / 800 : ℝ) (1045251799133 / 1000000000000 : ℝ)
    (41216352913 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1133_rightExp :
    Real.exp (567 / 400 : ℝ) ≤ (4126790557 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (567 / 400 : ℝ) (3266539469 / 3125000000 : ℝ)
    (4126790557 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1133_denomUpper :
    Real.exp (12610633826337301 / 1000000000000000 : ℝ) ≤ (1498644721690727 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (12610633826337301 / 1000000000000000 : ℝ) (741511303451
    / 500000000000 : ℝ) (1498644721690727 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1133_denomLower :
    (2948203474302537 / 10000000000 : ℝ) ≤ Real.exp (15742651822582187 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15742651822582187 / 1250000000000000 : ℝ) (59290301903 /
    40000000000 : ℝ) (2948203474302537 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1133_product_lower :
    (16185620572582187 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1133 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1133_leftExp
    (by norm_num : (0 : ℝ) ≤ (41216352913 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1133_product_upper :
    Real.pi * Real.exp (567 / 400 : ℝ) ≤ (12964696326337301 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1133_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1133_endpointLower :
    (39566633 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1133 / 1600 : ℝ) (567 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16185620572582187 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1133 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1133_product_lower
  have hD : Real.exp (Real.pi * Real.exp (567 / 400 : ℝ) - (1133 / 3200 : ℝ)) ≤
      (1498644721690727 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1133_denomUpper
    linarith [hpThetaJensenCell1133_product_upper]
  have hi : (1 / (1498644721690727 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (567 / 400 : ℝ) - (1133 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1498644721690727 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1498644721690727 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1133 / 3200 : ℝ) - Real.pi * Real.exp (567 / 400 : ℝ)) := by
    rw [show (1133 / 3200 : ℝ) - Real.pi * Real.exp (567 / 400 : ℝ) =
      -(Real.pi * Real.exp (567 / 400 : ℝ) - (1133 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1133 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1133 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1133_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1498644721690727 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1133_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1133 / 1600 : ℝ) (567 / 800 : ℝ) ≤ (40438931 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (567 / 400 : ℝ)) (12964696326337301 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (567 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1133_product_upper
  have hD : (2948203474302537 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1133 / 800 : ℝ) - (567 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1133_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1133_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1133 / 800 : ℝ) - (567 / 1600 : ℝ)) ≤
      (1 / (2948203474302537 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2948203474302537 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((567 / 1600 : ℝ) - Real.pi * Real.exp (1133 / 800 : ℝ)) ≤
      (2 / (2948203474302537 / 10000000000 : ℝ) : ℝ) := by
    rw [show (567 / 1600 : ℝ) - Real.pi * Real.exp (1133 / 800 : ℝ) =
      -(Real.pi * Real.exp (1133 / 800 : ℝ) - (567 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12964696326337301 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (12964696326337301 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1133_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1133 / 1600 : ℝ) (567 / 800 : ℝ)) :
    (39566633 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40438931 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1133_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1133_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1134_leftExp :
    (1289622049 / 312500000 : ℝ) ≤ Real.exp (567 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (567 / 400 : ℝ) (1045292630079 / 1000000000000 : ℝ)
    (1289622049 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1134_rightExp :
    Real.exp (227 / 160 : ℝ) ≤ (20659761353 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (227 / 160 : ℝ) (1045333462621 / 1000000000000 : ℝ)
    (20659761353 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1134_denomUpper :
    Real.exp (63132686648255329 / 5000000000000000 : ℝ) ≤ (3045337902699807 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (63132686648255329 / 5000000000000000 : ℝ) (741879914649
    / 500000000000 : ℝ) (3045337902699807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1134_denomLower :
    (299540435936519 / 1000000000 : ℝ) ≤ Real.exp (492578308551501 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (492578308551501 / 39062500000000 : ℝ) (1482993450619 /
    1000000000000 : ℝ) (299540435936519 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1134_product_lower :
    (506433289020251 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (567 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1134_leftExp
    (by norm_num : (0 : ℝ) ≤ (1289622049 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1134_product_upper :
    Real.pi * Real.exp (227 / 160 : ℝ) ≤ (64904561648255329 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1134_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1134_endpointLower :
    (3904623 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (567 / 800 : ℝ) (227 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (506433289020251 / 39062500000000 : ℝ) (Real.pi * Real.exp (567 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1134_product_lower
  have hD : Real.exp (Real.pi * Real.exp (227 / 160 : ℝ) - (567 / 1600 : ℝ)) ≤
      (3045337902699807 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1134_denomUpper
    linarith [hpThetaJensenCell1134_product_upper]
  have hi : (1 / (3045337902699807 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (227 / 160 : ℝ) - (567 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3045337902699807 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3045337902699807 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((567 / 1600 : ℝ) - Real.pi * Real.exp (227 / 160 : ℝ)) := by
    rw [show (567 / 1600 : ℝ) - Real.pi * Real.exp (227 / 160 : ℝ) =
      -(Real.pi * Real.exp (227 / 160 : ℝ) - (567 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (567 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (567 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1134_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3045337902699807 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1134_endpointUpper :
    hpThetaJensenKernelEndpointUpper (567 / 800 : ℝ) (227 / 320 : ℝ) ≤ (19953927 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (227 / 160 : ℝ)) (64904561648255329 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (227 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1134_product_upper
  have hD : (299540435936519 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (567 / 400 : ℝ) - (227 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1134_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1134_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (567 / 400 : ℝ) - (227 / 640 : ℝ)) ≤
      (1 / (299540435936519 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (299540435936519 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((227 / 640 : ℝ) - Real.pi * Real.exp (567 / 400 : ℝ)) ≤
      (2 / (299540435936519 / 1000000000 : ℝ) : ℝ) := by
    rw [show (227 / 640 : ℝ) - Real.pi * Real.exp (567 / 400 : ℝ) =
      -(Real.pi * Real.exp (567 / 400 : ℝ) - (227 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64904561648255329 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (64904561648255329 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1134_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (567 / 800 : ℝ) (227 / 320 : ℝ)) :
    (3904623 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (19953927 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1134_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1134_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1135_leftExp :
    (2582470169 / 625000000 : ℝ) ≤ Real.exp (227 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (227 / 160 : ℝ) (52266673131 / 50000000000 : ℝ)
    (2582470169 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1135_rightExp :
    Real.exp (71 / 50 : ℝ) ≤ (10342801101 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 50 : ℝ) (1045374296757 / 1000000000000 : ℝ)
    (10342801101 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1135_denomUpper :
    Real.exp (31606152789293893 / 2500000000000000 : ℝ) ≤ (3094219368056357 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (31606152789293893 / 2500000000000000 : ℝ) (1484498359101
    / 1000000000000 : ℝ) (3094219368056357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1135_denomLower :
    (121736903355461 / 400000000 : ℝ) ≤ Real.exp (986399077896131 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (986399077896131 / 78125000000000 : ℝ) (741865329141 /
    500000000000 : ℝ) (121736903355461 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1135_product_lower :
    (1014133452896131 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (227 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1135_leftExp
    (by norm_num : (0 : ℝ) ≤ (2582470169 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1135_product_upper :
    Real.pi * Real.exp (71 / 50 : ℝ) ≤ (32492871539293893 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1135_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1135_endpointLower :
    (963297 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (227 / 320 : ℝ) (71 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1014133452896131 / 78125000000000 : ℝ) (Real.pi * Real.exp (227 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1135_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 50 : ℝ) - (227 / 640 : ℝ)) ≤
      (3094219368056357 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1135_denomUpper
    linarith [hpThetaJensenCell1135_product_upper]
  have hi : (1 / (3094219368056357 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 50 : ℝ) - (227 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3094219368056357 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3094219368056357 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((227 / 640 : ℝ) - Real.pi * Real.exp (71 / 50 : ℝ)) := by
    rw [show (227 / 640 : ℝ) - Real.pi * Real.exp (71 / 50 : ℝ) =
      -(Real.pi * Real.exp (71 / 50 : ℝ) - (227 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (227 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (227 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1135_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3094219368056357 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1135_endpointUpper :
    hpThetaJensenKernelEndpointUpper (227 / 320 : ℝ) (71 / 100 : ℝ) ≤ (7876589 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 50 : ℝ)) (32492871539293893 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1135_product_upper
  have hD : (121736903355461 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (227 / 160 : ℝ) - (71 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1135_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1135_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (227 / 160 : ℝ) - (71 / 200 : ℝ)) ≤
      (1 / (121736903355461 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (121736903355461 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 200 : ℝ) - Real.pi * Real.exp (227 / 160 : ℝ)) ≤
      (2 / (121736903355461 / 400000000 : ℝ) : ℝ) := by
    rw [show (71 / 200 : ℝ) - Real.pi * Real.exp (227 / 160 : ℝ) =
      -(Real.pi * Real.exp (227 / 160 : ℝ) - (71 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32492871539293893 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (32492871539293893 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1135_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (227 / 320 : ℝ) (71 / 100 : ℝ)) :
    (963297 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7876589 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1135_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1135_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1136_leftExp :
    (20685602201 / 5000000000 : ℝ) ≤ Real.exp (71 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 50 : ℝ) (261343574189 / 250000000000 : ℝ)
    (20685602201 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1136_rightExp :
    Real.exp (1137 / 800 : ℝ) ≤ (5177868843 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1137 / 800 : ℝ) (130676891561 / 125000000000 : ℝ)
    (5177868843 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1136_denomUpper :
    Real.exp (15823006512086899 / 1250000000000000 : ℝ) ≤ (392993661013297 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15823006512086899 / 1250000000000000 : ℝ) (297047639813
    / 200000000000 : ℝ) (392993661013297 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1136_denomLower :
    (1546136645018023 / 5000000000 : ℝ) ≤ Real.exp (7901144986230499 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7901144986230499 / 625000000000000 : ℝ) (742234586663 /
    500000000000 : ℝ) (1546136645018023 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1136_product_lower :
    (8123215298730499 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1136_leftExp
    (by norm_num : (0 : ℝ) ≤ (20685602201 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1136_product_upper :
    Real.pi * Real.exp (1137 / 800 : ℝ) ≤ (16266756512086899 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1136_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1136_endpointLower :
    (19011763 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 100 : ℝ) (1137 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8123215298730499 / 625000000000000 : ℝ) (Real.pi * Real.exp (71 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1136_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1137 / 800 : ℝ) - (71 / 200 : ℝ)) ≤
      (392993661013297 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1136_denomUpper
    linarith [hpThetaJensenCell1136_product_upper]
  have hi : (1 / (392993661013297 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1137 / 800 : ℝ) - (71 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (392993661013297 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (392993661013297 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 200 : ℝ) - Real.pi * Real.exp (1137 / 800 : ℝ)) := by
    rw [show (71 / 200 : ℝ) - Real.pi * Real.exp (1137 / 800 : ℝ) =
      -(Real.pi * Real.exp (1137 / 800 : ℝ) - (71 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1136_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (392993661013297 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1136_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 100 : ℝ) (1137 / 1600 : ℝ) ≤ (19432071 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1137 / 800 : ℝ)) (16266756512086899 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1137 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1136_product_upper
  have hD : (1546136645018023 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 50 : ℝ) - (1137 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1136_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1136_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 50 : ℝ) - (1137 / 3200 : ℝ)) ≤
      (1 / (1546136645018023 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1546136645018023 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1137 / 3200 : ℝ) - Real.pi * Real.exp (71 / 50 : ℝ)) ≤
      (2 / (1546136645018023 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1137 / 3200 : ℝ) - Real.pi * Real.exp (71 / 50 : ℝ) =
      -(Real.pi * Real.exp (71 / 50 : ℝ) - (1137 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16266756512086899 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (16266756512086899 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1136_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 100 : ℝ) (1137 / 1600 : ℝ)) :
    (19011763 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (19432071 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1136_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1136_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1137_leftExp :
    (20711475371 / 5000000000 : ℝ) ≤ Real.exp (1137 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1137 / 800 : ℝ) (1045415132487 / 1000000000000 : ℝ)
    (20711475371 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1137_rightExp :
    Real.exp (569 / 400 : ℝ) ≤ (2592172613 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (569 / 400 : ℝ) (522727984907 / 500000000000 : ℝ)
    (2592172613 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1137_denomUpper :
    Real.exp (7921481023292509 / 625000000000000 : ℝ) ≤ (798635854377997 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7921481023292509 / 625000000000000 : ℝ) (1485979351979 /
    1000000000000 : ℝ) (798635854377997 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1137_denomLower :
    (196373244796457 / 625000000 : ℝ) ≤ Real.exp (7911110041716329 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7911110041716329 / 625000000000000 : ℝ) (297041799701 /
    200000000000 : ℝ) (196373244796457 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1137_product_lower :
    (8133375666716329 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1137 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1137_leftExp
    (by norm_num : (0 : ℝ) ≤ (20711475371 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1137_product_upper :
    Real.pi * Real.exp (569 / 400 : ℝ) ≤ (8143551335792509 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1137_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1137_endpointLower :
    (18760553 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1137 / 1600 : ℝ) (569 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8133375666716329 / 625000000000000 : ℝ) (Real.pi * Real.exp (1137 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1137_product_lower
  have hD : Real.exp (Real.pi * Real.exp (569 / 400 : ℝ) - (1137 / 3200 : ℝ)) ≤
      (798635854377997 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1137_denomUpper
    linarith [hpThetaJensenCell1137_product_upper]
  have hi : (1 / (798635854377997 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (569 / 400 : ℝ) - (1137 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (798635854377997 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (798635854377997 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1137 / 3200 : ℝ) - Real.pi * Real.exp (569 / 400 : ℝ)) := by
    rw [show (1137 / 3200 : ℝ) - Real.pi * Real.exp (569 / 400 : ℝ) =
      -(Real.pi * Real.exp (569 / 400 : ℝ) - (1137 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1137 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1137 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1137_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (798635854377997 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1137_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1137 / 1600 : ℝ) (569 / 800 : ℝ) ≤ (38351387 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (569 / 400 : ℝ)) (8143551335792509 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (569 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1137_product_upper
  have hD : (196373244796457 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1137 / 800 : ℝ) - (569 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1137_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1137_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1137 / 800 : ℝ) - (569 / 1600 : ℝ)) ≤
      (1 / (196373244796457 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (196373244796457 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((569 / 1600 : ℝ) - Real.pi * Real.exp (1137 / 800 : ℝ)) ≤
      (2 / (196373244796457 / 625000000 : ℝ) : ℝ) := by
    rw [show (569 / 1600 : ℝ) - Real.pi * Real.exp (1137 / 800 : ℝ) =
      -(Real.pi * Real.exp (1137 / 800 : ℝ) - (569 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8143551335792509 / 625000000000000 : ℝ) ^ 2 - 6 *
      (8143551335792509 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1137_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1137 / 1600 : ℝ) (569 / 800 : ℝ)) :
    (18760553 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (38351387 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1137_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1137_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1138_leftExp :
    (8294952361 / 2000000000 : ℝ) ≤ Real.exp (569 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (569 / 400 : ℝ) (1045455969813 / 1000000000000 : ℝ)
    (8294952361 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1138_rightExp :
    Real.exp (1139 / 800 : ℝ) ≤ (1661065507 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1139 / 800 : ℝ) (209099361747 / 200000000000 : ℝ)
    (1661065507 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1138_denomUpper :
    Real.exp (5076141769332651 / 400000000000000 : ℝ) ≤ (1623008909117607 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5076141769332651 / 400000000000000 : ℝ) (1486721820593 /
    1000000000000 : ℝ) (1623008909117607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1138_denomLower :
    (1596267103826103 / 5000000000 : ℝ) ≤ Real.exp (3168435122212339 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3168435122212339 / 250000000000000 : ℝ) (92871883537 /
    62500000000 : ℝ) (1596267103826103 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1138_product_lower :
    (3257419497212339 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (569 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1138_leftExp
    (by norm_num : (0 : ℝ) ≤ (8294952361 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1138_product_upper :
    Real.pi * Real.exp (1139 / 800 : ℝ) ≤ (5218391769332651 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1138_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1138_endpointLower :
    (37024563 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (569 / 800 : ℝ) (1139 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3257419497212339 / 250000000000000 : ℝ) (Real.pi * Real.exp (569 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1138_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1139 / 800 : ℝ) - (569 / 1600 : ℝ)) ≤
      (1623008909117607 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1138_denomUpper
    linarith [hpThetaJensenCell1138_product_upper]
  have hi : (1 / (1623008909117607 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1139 / 800 : ℝ) - (569 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1623008909117607 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1623008909117607 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((569 / 1600 : ℝ) - Real.pi * Real.exp (1139 / 800 : ℝ)) := by
    rw [show (569 / 1600 : ℝ) - Real.pi * Real.exp (1139 / 800 : ℝ) =
      -(Real.pi * Real.exp (1139 / 800 : ℝ) - (569 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (569 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (569 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1138_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1623008909117607 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1138_endpointUpper :
    hpThetaJensenKernelEndpointUpper (569 / 800 : ℝ) (1139 / 1600 : ℝ) ≤ (18922309 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1139 / 800 : ℝ)) (5218391769332651 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1139 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1138_product_upper
  have hD : (1596267103826103 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (569 / 400 : ℝ) - (1139 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1138_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1138_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (569 / 400 : ℝ) - (1139 / 3200 : ℝ)) ≤
      (1 / (1596267103826103 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1596267103826103 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1139 / 3200 : ℝ) - Real.pi * Real.exp (569 / 400 : ℝ)) ≤
      (2 / (1596267103826103 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1139 / 3200 : ℝ) - Real.pi * Real.exp (569 / 400 : ℝ) =
      -(Real.pi * Real.exp (569 / 400 : ℝ) - (1139 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5218391769332651 / 400000000000000 : ℝ) ^ 2 - 6 *
      (5218391769332651 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1138_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (569 / 800 : ℝ) (1139 / 1600 : ℝ)) :
    (37024563 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (18922309 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1138_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1138_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1139_leftExp :
    (41526637673 / 10000000000 : ℝ) ≤ Real.exp (1139 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1139 / 800 : ℝ) (522748404367 / 500000000000 : ℝ)
    (41526637673 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1139_rightExp :
    Real.exp (57 / 40 : ℝ) ≤ (41578578429 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 40 : ℝ) (261384412313 / 250000000000 : ℝ)
    (41578578429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1139_denomUpper :
    Real.exp (127063595942497397 / 10000000000000000 : ℝ) ≤ (82459721852887 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (127063595942497397 / 10000000000000000 : ℝ)
    (185933200967 / 125000000000 : ℝ) (82459721852887 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1139_denomLower :
    (1621988108851851 / 5000000000 : ℝ) ≤ Real.exp (15862156587549427 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15862156587549427 / 1250000000000000 : ℝ) (743346295191
    / 500000000000 : ℝ) (1621988108851851 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1139_product_lower :
    (16307469087549427 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1139 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1139_leftExp
    (by norm_num : (0 : ℝ) ≤ (41526637673 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1139_product_upper :
    Real.pi * Real.exp (57 / 40 : ℝ) ≤ (130622970942497397 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1139_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1139_endpointLower :
    (18266919 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1139 / 1600 : ℝ) (57 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16307469087549427 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1139 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1139_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 40 : ℝ) - (1139 / 3200 : ℝ)) ≤
      (82459721852887 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1139_denomUpper
    linarith [hpThetaJensenCell1139_product_upper]
  have hi : (1 / (82459721852887 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 40 : ℝ) - (1139 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (82459721852887 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (82459721852887 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1139 / 3200 : ℝ) - Real.pi * Real.exp (57 / 40 : ℝ)) := by
    rw [show (1139 / 3200 : ℝ) - Real.pi * Real.exp (57 / 40 : ℝ) =
      -(Real.pi * Real.exp (57 / 40 : ℝ) - (1139 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1139 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1139 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1139_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (82459721852887 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1139_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1139 / 1600 : ℝ) (57 / 80 : ℝ) ≤ (37343777 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 40 : ℝ)) (130622970942497397 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1139_product_upper
  have hD : (1621988108851851 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1139 / 800 : ℝ) - (57 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1139_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1139_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1139 / 800 : ℝ) - (57 / 160 : ℝ)) ≤
      (1 / (1621988108851851 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1621988108851851 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 160 : ℝ) - Real.pi * Real.exp (1139 / 800 : ℝ)) ≤
      (2 / (1621988108851851 / 5000000000 : ℝ) : ℝ) := by
    rw [show (57 / 160 : ℝ) - Real.pi * Real.exp (1139 / 800 : ℝ) =
      -(Real.pi * Real.exp (1139 / 800 : ℝ) - (57 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (130622970942497397 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (130622970942497397 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1139_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1139 / 1600 : ℝ) (57 / 80 : ℝ)) :
    (18266919 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (37343777 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1139_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1139_endpointUpper

def hpThetaJensenCellsBatch056Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9382167 / 2000000000 : ℝ)
  | 1 => (46306079 / 10000000000 : ℝ)
  | 2 => (11427049 / 2500000000 : ℝ)
  | 3 => (45117121 / 10000000000 : ℝ)
  | 4 => (11133197 / 2500000000 : ℝ)
  | 5 => (10988783 / 2500000000 : ℝ)
  | 6 => (43384089 / 10000000000 : ℝ)
  | 7 => (8563919 / 2000000000 : ℝ)
  | 8 => (21130793 / 5000000000 : ℝ)
  | 9 => (41709999 / 10000000000 : ℝ)
  | 10 => (10291193 / 2500000000 : ℝ)
  | 11 => (40625843 / 10000000000 : ℝ)
  | 12 => (40093151 / 10000000000 : ℝ)
  | 13 => (39566633 / 10000000000 : ℝ)
  | 14 => (3904623 / 1000000000 : ℝ)
  | 15 => (963297 / 250000000 : ℝ)
  | 16 => (19011763 / 5000000000 : ℝ)
  | 17 => (18760553 / 5000000000 : ℝ)
  | 18 => (37024563 / 10000000000 : ℝ)
  | 19 => (18266919 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch056Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (47932673 / 10000000000 : ℝ)
  | 1 => (11828919 / 2500000000 : ℝ)
  | 2 => (46705679 / 10000000000 : ℝ)
  | 3 => (5762827 / 1250000000 : ℝ)
  | 4 => (45506419 / 10000000000 : ℝ)
  | 5 => (44917023 / 10000000000 : ℝ)
  | 6 => (44334363 / 10000000000 : ℝ)
  | 7 => (43758373 / 10000000000 : ℝ)
  | 8 => (10797247 / 2500000000 : ℝ)
  | 9 => (21313073 / 5000000000 : ℝ)
  | 10 => (21034891 / 5000000000 : ℝ)
  | 11 => (41519833 / 10000000000 : ℝ)
  | 12 => (40976237 / 10000000000 : ℝ)
  | 13 => (40438931 / 10000000000 : ℝ)
  | 14 => (19953927 / 5000000000 : ℝ)
  | 15 => (7876589 / 2000000000 : ℝ)
  | 16 => (19432071 / 5000000000 : ℝ)
  | 17 => (38351387 / 10000000000 : ℝ)
  | 18 => (18922309 / 5000000000 : ℝ)
  | 19 => (37343777 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch056_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch056Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch056Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1120_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1121_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1122_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1123_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1124_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1125_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1126_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1127_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1128_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1129_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1130_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1131_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1132_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1133_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1134_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1135_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1136_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1137_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1138_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1139_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper] at h ⊢
    exact h

end HodgeProofHP
