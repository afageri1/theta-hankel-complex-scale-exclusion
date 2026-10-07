import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1480_leftExp :
    (2543927809 / 400000000 : ℝ) ≤ Real.exp (37 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 20 : ℝ) (42380652711 / 40000000000 : ℝ) (2543927809
    / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1480_rightExp :
    Real.exp (1481 / 800 : ℝ) ≤ (31838871339 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1481 / 800 : ℝ) (52977885297 / 50000000000 : ℝ)
    (31838871339 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1480_denomUpper :
    Real.exp (97712275326503027 / 5000000000000000 : ℝ) ≤ (38378713335527793 / 125000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (97712275326503027 / 5000000000000000 : ℝ) (184172332099
    / 100000000000 : ℝ) (38378713335527793 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1480_denomLower :
    (2993564713841489963 / 10000000000 : ℝ) ≤ Real.exp (975857281666491 / 50000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (975857281666491 / 50000000000000 : ℝ) (1840267241533 /
    1000000000000 : ℝ) (2993564713841489963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1480_product_lower :
    (998997906666491 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1480_leftExp
    (by norm_num : (0 : ℝ) ≤ (2543927809 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1480_product_upper :
    Real.pi * Real.exp (1481 / 800 : ℝ) ≤ (100024775326503027 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1480_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1480_endpointLower :
    (48103 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 40 : ℝ) (1481 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (998997906666491 / 50000000000000 : ℝ) (Real.pi * Real.exp (37 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell1480_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1481 / 800 : ℝ) - (37 / 80 : ℝ)) ≤
      (38378713335527793 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1480_denomUpper
    linarith [hpThetaJensenCell1480_product_upper]
  have hi : (1 / (38378713335527793 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1481 / 800 : ℝ) - (37 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38378713335527793 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38378713335527793 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 80 : ℝ) - Real.pi * Real.exp (1481 / 800 : ℝ)) := by
    rw [show (37 / 80 : ℝ) - Real.pi * Real.exp (1481 / 800 : ℝ) =
      -(Real.pi * Real.exp (1481 / 800 : ℝ) - (37 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 20 : ℝ)) := by
    have h := hpThetaJensenCell1480_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38378713335527793 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1480_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 40 : ℝ) (1481 / 1600 : ℝ) ≤ (99191 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1481 / 800 : ℝ)) (100024775326503027 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1481 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1480_product_upper
  have hD : (2993564713841489963 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 20 : ℝ) - (1481 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1480_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1480_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 20 : ℝ) - (1481 / 3200 : ℝ)) ≤
      (1 / (2993564713841489963 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2993564713841489963 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1481 / 3200 : ℝ) - Real.pi * Real.exp (37 / 20 : ℝ)) ≤
      (2 / (2993564713841489963 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1481 / 3200 : ℝ) - Real.pi * Real.exp (37 / 20 : ℝ) =
      -(Real.pi * Real.exp (37 / 20 : ℝ) - (1481 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (100024775326503027 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (100024775326503027 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1480_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 40 : ℝ) (1481 / 1600 : ℝ)) :
    (48103 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (99191 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1480_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1480_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1481_leftExp :
    (2547109707 / 400000000 : ℝ) ≤ Real.exp (1481 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1481 / 800 : ℝ) (1059557705939 / 1000000000000 : ℝ)
    (2547109707 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1481_rightExp :
    Real.exp (741 / 400 : ℝ) ≤ (63757389627 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (741 / 400 : ℝ) (529799547861 / 500000000000 : ℝ)
    (63757389627 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1481_denomUpper :
    Real.exp (195671643950455811 / 10000000000000000 : ℝ) ≤ (629421420748096619 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (195671643950455811 / 10000000000000000 : ℝ)
    (921572993669 / 500000000000 : ℝ) (629421420748096619 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1481_denomLower :
    (767089797197406563 / 2500000000 : ℝ) ≤ Real.exp (977091184829193 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (977091184829193 / 50000000000000 : ℝ) (1841686983639 /
    1000000000000 : ℝ) (767089797197406563 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1481_product_lower :
    (1000247434829193 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1481 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1481_leftExp
    (by norm_num : (0 : ℝ) ≤ (2547109707 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1481_product_upper :
    Real.pi * Real.exp (741 / 400 : ℝ) ≤ (200299768950455811 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1481_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1481_endpointLower :
    (94103 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1481 / 1600 : ℝ) (741 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1000247434829193 / 50000000000000 : ℝ) (Real.pi * Real.exp (1481 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1481_product_lower
  have hD : Real.exp (Real.pi * Real.exp (741 / 400 : ℝ) - (1481 / 3200 : ℝ)) ≤
      (629421420748096619 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1481_denomUpper
    linarith [hpThetaJensenCell1481_product_upper]
  have hi : (1 / (629421420748096619 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (741 / 400 : ℝ) - (1481 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (629421420748096619 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (629421420748096619 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1481 / 3200 : ℝ) - Real.pi * Real.exp (741 / 400 : ℝ)) := by
    rw [show (1481 / 3200 : ℝ) - Real.pi * Real.exp (741 / 400 : ℝ) =
      -(Real.pi * Real.exp (741 / 400 : ℝ) - (1481 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1481 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1481 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1481_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (629421420748096619 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1481_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1481 / 1600 : ℝ) (741 / 800 : ℝ) ≤ (3881 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (741 / 400 : ℝ)) (200299768950455811 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (741 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1481_product_upper
  have hD : (767089797197406563 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1481 / 800 : ℝ) - (741 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1481_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1481_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1481 / 800 : ℝ) - (741 / 1600 : ℝ)) ≤
      (1 / (767089797197406563 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (767089797197406563 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((741 / 1600 : ℝ) - Real.pi * Real.exp (1481 / 800 : ℝ)) ≤
      (2 / (767089797197406563 / 2500000000 : ℝ) : ℝ) := by
    rw [show (741 / 1600 : ℝ) - Real.pi * Real.exp (1481 / 800 : ℝ) =
      -(Real.pi * Real.exp (1481 / 800 : ℝ) - (741 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (200299768950455811 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (200299768950455811 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1481_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1481 / 1600 : ℝ) (741 / 800 : ℝ)) :
    (94103 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3881 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1481_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1481_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1482_leftExp :
    (7969673703 / 1250000000 : ℝ) ≤ Real.exp (741 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (741 / 400 : ℝ) (1059599095721 / 1000000000000 : ℝ)
    (7969673703 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1482_rightExp :
    Real.exp (1483 / 800 : ℝ) ≤ (12767427239 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1483 / 800 : ℝ) (13245506089 / 12500000000 : ℝ)
    (12767427239 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1482_denomUpper :
    Real.exp (39183810042051727 / 2000000000000000 : ℝ) ≤ (806484916486550087 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (39183810042051727 / 2000000000000000 : ℝ) (36891431133 /
    20000000000 : ℝ) (806484916486550087 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1482_denomLower :
    (1572560360242157459 / 5000000000 : ℝ) ≤ Real.exp (3057270784119397 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3057270784119397 / 156250000000000 : ℝ) (1843109621459 /
    1000000000000 : ℝ) (1572560360242157459 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1482_product_lower :
    (3129682893494397 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (741 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1482_leftExp
    (by norm_num : (0 : ℝ) ≤ (7969673703 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1482_product_upper :
    Real.pi * Real.exp (1483 / 800 : ℝ) ≤ (40110060042051727 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1482_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1482_endpointLower :
    (46021 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (741 / 800 : ℝ) (1483 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3129682893494397 / 156250000000000 : ℝ) (Real.pi * Real.exp (741 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1482_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1483 / 800 : ℝ) - (741 / 1600 : ℝ)) ≤
      (806484916486550087 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1482_denomUpper
    linarith [hpThetaJensenCell1482_product_upper]
  have hi : (1 / (806484916486550087 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1483 / 800 : ℝ) - (741 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (806484916486550087 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (806484916486550087 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((741 / 1600 : ℝ) - Real.pi * Real.exp (1483 / 800 : ℝ)) := by
    rw [show (741 / 1600 : ℝ) - Real.pi * Real.exp (1483 / 800 : ℝ) =
      -(Real.pi * Real.exp (1483 / 800 : ℝ) - (741 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (741 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (741 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1482_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (806484916486550087 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1482_endpointUpper :
    hpThetaJensenKernelEndpointUpper (741 / 800 : ℝ) (1483 / 1600 : ℝ) ≤ (94903 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1483 / 800 : ℝ)) (40110060042051727 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1483 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1482_product_upper
  have hD : (1572560360242157459 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (741 / 400 : ℝ) - (1483 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1482_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1482_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (741 / 400 : ℝ) - (1483 / 3200 : ℝ)) ≤
      (1 / (1572560360242157459 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1572560360242157459 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1483 / 3200 : ℝ) - Real.pi * Real.exp (741 / 400 : ℝ)) ≤
      (2 / (1572560360242157459 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1483 / 3200 : ℝ) - Real.pi * Real.exp (741 / 400 : ℝ) =
      -(Real.pi * Real.exp (741 / 400 : ℝ) - (1483 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40110060042051727 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (40110060042051727 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1482_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (741 / 800 : ℝ) (1483 / 1600 : ℝ)) :
    (46021 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (94903 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1482_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1482_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1483_leftExp :
    (997455253 / 156250000 : ℝ) ≤ Real.exp (1483 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1483 / 800 : ℝ) (1059640487119 / 1000000000000 : ℝ)
    (997455253 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1483_rightExp :
    Real.exp (371 / 200 : ℝ) ≤ (15979245627 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (371 / 200 : ℝ) (211936376027 / 200000000000 : ℝ)
    (15979245627 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1483_denomUpper :
    Real.exp (49041692457063811 / 2500000000000000 : ℝ) ≤ (413356317895007593 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (49041692457063811 / 2500000000000000 : ℝ) (1846000036243
    / 1000000000000 : ℝ) (413356317895007593 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1483_denomLower :
    (1611951749781292663 / 5000000000 : ℝ) ≤ Real.exp (382642063210347 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (382642063210347 / 19531250000000 : ℝ) (1844535162183 /
    1000000000000 : ℝ) (1611951749781292663 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1483_product_lower :
    (391699680397847 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (1483 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1483_leftExp
    (by norm_num : (0 : ℝ) ≤ (997455253 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1483_product_upper :
    Real.pi * Real.exp (371 / 200 : ℝ) ≤ (50200286207063811 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1483_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1483_endpointLower :
    (11253 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1483 / 1600 : ℝ) (371 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (391699680397847 / 19531250000000 : ℝ) (Real.pi * Real.exp (1483 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1483_product_lower
  have hD : Real.exp (Real.pi * Real.exp (371 / 200 : ℝ) - (1483 / 3200 : ℝ)) ≤
      (413356317895007593 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1483_denomUpper
    linarith [hpThetaJensenCell1483_product_upper]
  have hi : (1 / (413356317895007593 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (371 / 200 : ℝ) - (1483 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (413356317895007593 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (413356317895007593 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1483 / 3200 : ℝ) - Real.pi * Real.exp (371 / 200 : ℝ)) := by
    rw [show (1483 / 3200 : ℝ) - Real.pi * Real.exp (371 / 200 : ℝ) =
      -(Real.pi * Real.exp (371 / 200 : ℝ) - (1483 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1483 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1483 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1483_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (413356317895007593 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1483_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1483 / 1600 : ℝ) (371 / 400 : ℝ) ≤ (3713 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (371 / 200 : ℝ)) (50200286207063811 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (371 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1483_product_upper
  have hD : (1611951749781292663 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1483 / 800 : ℝ) - (371 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1483_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1483_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1483 / 800 : ℝ) - (371 / 800 : ℝ)) ≤
      (1 / (1611951749781292663 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1611951749781292663 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((371 / 800 : ℝ) - Real.pi * Real.exp (1483 / 800 : ℝ)) ≤
      (2 / (1611951749781292663 / 5000000000 : ℝ) : ℝ) := by
    rw [show (371 / 800 : ℝ) - Real.pi * Real.exp (1483 / 800 : ℝ) =
      -(Real.pi * Real.exp (1483 / 800 : ℝ) - (371 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50200286207063811 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (50200286207063811 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1483_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1483 / 1600 : ℝ) (371 / 400 : ℝ)) :
    (11253 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3713 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1483_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1483_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1484_leftExp :
    (31958491253 / 5000000000 : ℝ) ≤ Real.exp (371 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (371 / 200 : ℝ) (529840940067 / 500000000000 : ℝ)
    (31958491253 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1484_rightExp :
    Real.exp (297 / 160 : ℝ) ≤ (63996928693 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (297 / 160 : ℝ) (1059723274767 / 1000000000000 : ℝ)
    (63996928693 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1484_denomUpper :
    Real.exp (196414803203427949 / 10000000000000000 : ℝ) ≤ (3389897132040867393 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (196414803203427949 / 10000000000000000 : ℝ)
    (1847431433473 / 1000000000000 : ℝ) (3389897132040867393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1484_denomLower :
    (3304763281665983219 / 10000000000 : ℝ) ≤ Real.exp (12260028494061847 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (12260028494061847 / 625000000000000 : ℝ) (1845963613149
    / 1000000000000 : ℝ) (3304763281665983219 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1484_product_lower :
    (12550067556561847 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (371 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1484_leftExp
    (by norm_num : (0 : ℝ) ≤ (31958491253 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1484_product_upper :
    Real.pi * Real.exp (297 / 160 : ℝ) ≤ (201052303203427949 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1484_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1484_endpointLower :
    (88047 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (371 / 400 : ℝ) (297 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12550067556561847 / 625000000000000 : ℝ) (Real.pi * Real.exp (371 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1484_product_lower
  have hD : Real.exp (Real.pi * Real.exp (297 / 160 : ℝ) - (371 / 800 : ℝ)) ≤
      (3389897132040867393 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1484_denomUpper
    linarith [hpThetaJensenCell1484_product_upper]
  have hi : (1 / (3389897132040867393 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (297 / 160 : ℝ) - (371 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3389897132040867393 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3389897132040867393 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((371 / 800 : ℝ) - Real.pi * Real.exp (297 / 160 : ℝ)) := by
    rw [show (371 / 800 : ℝ) - Real.pi * Real.exp (297 / 160 : ℝ) =
      -(Real.pi * Real.exp (297 / 160 : ℝ) - (371 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (371 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (371 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1484_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3389897132040867393 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1484_endpointUpper :
    hpThetaJensenKernelEndpointUpper (371 / 400 : ℝ) (297 / 320 : ℝ) ≤ (9079 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (297 / 160 : ℝ)) (201052303203427949 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (297 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1484_product_upper
  have hD : (3304763281665983219 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (371 / 200 : ℝ) - (297 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1484_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1484_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (371 / 200 : ℝ) - (297 / 640 : ℝ)) ≤
      (1 / (3304763281665983219 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3304763281665983219 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((297 / 640 : ℝ) - Real.pi * Real.exp (371 / 200 : ℝ)) ≤
      (2 / (3304763281665983219 / 10000000000 : ℝ) : ℝ) := by
    rw [show (297 / 640 : ℝ) - Real.pi * Real.exp (371 / 200 : ℝ) =
      -(Real.pi * Real.exp (371 / 200 : ℝ) - (297 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (201052303203427949 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (201052303203427949 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1484_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (371 / 400 : ℝ) (297 / 320 : ℝ)) :
    (88047 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9079 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1484_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1484_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1485_leftExp :
    (6399692869 / 1000000000 : ℝ) ≤ Real.exp (297 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (297 / 160 : ℝ) (529861637383 / 500000000000 : ℝ)
    (6399692869 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1485_rightExp :
    Real.exp (743 / 400 : ℝ) ≤ (6407697487 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (743 / 400 : ℝ) (211952934203 / 200000000000 : ℝ)
    (6407697487 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1485_denomUpper :
    Real.exp (19666315071276791 / 1000000000000000 : ℝ) ≤ (3475138475691168723 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (19666315071276791 / 1000000000000000 : ℝ) (184886575559
    / 100000000000 : ℝ) (3475138475691168723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1485_denomLower :
    (1693878711988532019 / 5000000000 : ℝ) ≤ Real.exp (2455106114963431 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2455106114963431 / 125000000000000 : ℝ) (1847394981657 /
    1000000000000 : ℝ) (1693878711988532019 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1485_product_lower :
    (2513152989963431 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (297 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1485_leftExp
    (by norm_num : (0 : ℝ) ≤ (6399692869 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1485_product_upper :
    Real.pi * Real.exp (743 / 400 : ℝ) ≤ (20130377571276791 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1485_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1485_endpointLower :
    (86111 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (297 / 320 : ℝ) (743 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2513152989963431 / 125000000000000 : ℝ) (Real.pi * Real.exp (297 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1485_product_lower
  have hD : Real.exp (Real.pi * Real.exp (743 / 400 : ℝ) - (297 / 640 : ℝ)) ≤
      (3475138475691168723 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1485_denomUpper
    linarith [hpThetaJensenCell1485_product_upper]
  have hi : (1 / (3475138475691168723 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (743 / 400 : ℝ) - (297 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3475138475691168723 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3475138475691168723 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((297 / 640 : ℝ) - Real.pi * Real.exp (743 / 400 : ℝ)) := by
    rw [show (297 / 640 : ℝ) - Real.pi * Real.exp (743 / 400 : ℝ) =
      -(Real.pi * Real.exp (743 / 400 : ℝ) - (297 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (297 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (297 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1485_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3475138475691168723 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1485_endpointUpper :
    hpThetaJensenKernelEndpointUpper (297 / 320 : ℝ) (743 / 800 : ℝ) ≤ (88797 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (743 / 400 : ℝ)) (20130377571276791 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (743 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1485_product_upper
  have hD : (1693878711988532019 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (297 / 160 : ℝ) - (743 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1485_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1485_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (297 / 160 : ℝ) - (743 / 1600 : ℝ)) ≤
      (1 / (1693878711988532019 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1693878711988532019 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((743 / 1600 : ℝ) - Real.pi * Real.exp (297 / 160 : ℝ)) ≤
      (2 / (1693878711988532019 / 5000000000 : ℝ) : ℝ) := by
    rw [show (743 / 1600 : ℝ) - Real.pi * Real.exp (297 / 160 : ℝ) =
      -(Real.pi * Real.exp (297 / 160 : ℝ) - (743 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20130377571276791 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (20130377571276791 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1485_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (297 / 320 : ℝ) (743 / 800 : ℝ)) :
    (86111 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (88797 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1485_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1485_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1486_leftExp :
    (64076974867 / 10000000000 : ℝ) ≤ Real.exp (743 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (743 / 400 : ℝ) (529882335507 / 500000000000 : ℝ)
    (64076974867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1486_rightExp :
    Real.exp (1487 / 800 : ℝ) ≤ (6415712117 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1487 / 800 : ℝ) (1059806068881 / 1000000000000 : ℝ)
    (6415712117 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1486_denomUpper :
    Real.exp (19691181276782381 / 1000000000000000 : ℝ) ≤ (1781317666071686871 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (19691181276782381 / 1000000000000000 : ℝ) (92515150503 /
    50000000000 : ℝ) (1781317666071686871 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1486_denomLower :
    (347294493531783601 / 1000000000 : ℝ) ≤ Real.exp (24582104578296033 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (24582104578296033 / 1250000000000000 : ℝ) (184882927501
    / 100000000000 : ℝ) (347294493531783601 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1486_product_lower :
    (25162963953296033 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (743 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1486_leftExp
    (by norm_num : (0 : ℝ) ≤ (64076974867 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1486_product_upper :
    Real.pi * Real.exp (1487 / 800 : ℝ) ≤ (20155556276782381 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1486_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1486_endpointLower :
    (16843 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (743 / 800 : ℝ) (1487 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25162963953296033 / 1250000000000000 : ℝ) (Real.pi * Real.exp (743 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1486_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1487 / 800 : ℝ) - (743 / 1600 : ℝ)) ≤
      (1781317666071686871 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1486_denomUpper
    linarith [hpThetaJensenCell1486_product_upper]
  have hi : (1 / (1781317666071686871 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1487 / 800 : ℝ) - (743 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1781317666071686871 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1781317666071686871 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((743 / 1600 : ℝ) - Real.pi * Real.exp (1487 / 800 : ℝ)) := by
    rw [show (743 / 1600 : ℝ) - Real.pi * Real.exp (1487 / 800 : ℝ) =
      -(Real.pi * Real.exp (1487 / 800 : ℝ) - (743 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (743 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (743 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1486_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1781317666071686871 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1486_endpointUpper :
    hpThetaJensenKernelEndpointUpper (743 / 800 : ℝ) (1487 / 1600 : ℝ) ≤ (21711 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1487 / 800 : ℝ)) (20155556276782381 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1487 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1486_product_upper
  have hD : (347294493531783601 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (743 / 400 : ℝ) - (1487 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1486_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1486_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (743 / 400 : ℝ) - (1487 / 3200 : ℝ)) ≤
      (1 / (347294493531783601 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (347294493531783601 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1487 / 3200 : ℝ) - Real.pi * Real.exp (743 / 400 : ℝ)) ≤
      (2 / (347294493531783601 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1487 / 3200 : ℝ) - Real.pi * Real.exp (743 / 400 : ℝ) =
      -(Real.pi * Real.exp (743 / 400 : ℝ) - (1487 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20155556276782381 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (20155556276782381 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1486_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (743 / 800 : ℝ) (1487 / 1600 : ℝ)) :
    (16843 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (21711 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1486_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1486_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1487_leftExp :
    (64157121167 / 10000000000 : ℝ) ≤ Real.exp (1487 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1487 / 800 : ℝ) (13247575861 / 12500000000 : ℝ)
    (64157121167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1487_rightExp :
    Real.exp (93 / 50 : ℝ) ≤ (16059341929 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93 / 50 : ℝ) (211969493673 / 200000000000 : ℝ)
    (16059341929 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1487_denomUpper :
    Real.exp (49290197438752897 / 2500000000000000 : ℝ) ≤ (730490041100033223 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (49290197438752897 / 2500000000000000 : ℝ) (925871602113
    / 500000000000 : ℝ) (730490041100033223 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1487_denomLower :
    (3560386534410843761 / 10000000000 : ℝ) ≤ Real.exp (24613187325159733 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (24613187325159733 / 1250000000000000 : ℝ) (925133250329
    / 500000000000 : ℝ) (3560386534410843761 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1487_product_lower :
    (25194437325159733 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1487 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1487_leftExp
    (by norm_num : (0 : ℝ) ≤ (64157121167 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1487_product_upper :
    Real.pi * Real.exp (93 / 50 : ℝ) ≤ (50451916188752897 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1487_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1487_endpointLower :
    (41179 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1487 / 1600 : ℝ) (93 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25194437325159733 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1487 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1487_product_lower
  have hD : Real.exp (Real.pi * Real.exp (93 / 50 : ℝ) - (1487 / 3200 : ℝ)) ≤
      (730490041100033223 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1487_denomUpper
    linarith [hpThetaJensenCell1487_product_upper]
  have hi : (1 / (730490041100033223 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (93 / 50 : ℝ) - (1487 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (730490041100033223 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (730490041100033223 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1487 / 3200 : ℝ) - Real.pi * Real.exp (93 / 50 : ℝ)) := by
    rw [show (1487 / 3200 : ℝ) - Real.pi * Real.exp (93 / 50 : ℝ) =
      -(Real.pi * Real.exp (93 / 50 : ℝ) - (1487 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1487 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1487 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1487_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (730490041100033223 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1487_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1487 / 1600 : ℝ) (93 / 100 : ℝ) ≤ (21233 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (93 / 50 : ℝ)) (50451916188752897 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (93 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1487_product_upper
  have hD : (3560386534410843761 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1487 / 800 : ℝ) - (93 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1487_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1487_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1487 / 800 : ℝ) - (93 / 200 : ℝ)) ≤
      (1 / (3560386534410843761 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3560386534410843761 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((93 / 200 : ℝ) - Real.pi * Real.exp (1487 / 800 : ℝ)) ≤
      (2 / (3560386534410843761 / 10000000000 : ℝ) : ℝ) := by
    rw [show (93 / 200 : ℝ) - Real.pi * Real.exp (1487 / 800 : ℝ) =
      -(Real.pi * Real.exp (1487 / 800 : ℝ) - (93 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50451916188752897 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (50451916188752897 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1487_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1487 / 1600 : ℝ) (93 / 100 : ℝ)) :
    (41179 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (21233 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1487_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1487_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1488_leftExp :
    (32118683857 / 5000000000 : ℝ) ≤ Real.exp (93 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (93 / 50 : ℝ) (264961867091 / 250000000000 : ℝ)
    (32118683857 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1488_rightExp :
    Real.exp (1489 / 800 : ℝ) ≤ (8039714329 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1489 / 800 : ℝ) (211977773893 / 200000000000 : ℝ)
    (8039714329 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1488_denomUpper :
    Real.exp (24676260257986097 / 1250000000000000 : ℝ) ≤ (1872323703951861681 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (24676260257986097 / 1250000000000000 : ℝ) (463296586367
    / 250000000000 : ℝ) (1872323703951861681 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1488_denomLower :
    (730028937386920541 / 2000000000 : ℝ) ≤ Real.exp (12322154719460043 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12322154719460043 / 625000000000000 : ℝ) (1851706665961
    / 1000000000000 : ℝ) (730028937386920541 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1488_product_lower :
    (12612975031960043 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (93 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1488_leftExp
    (by norm_num : (0 : ℝ) ≤ (32118683857 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1488_product_upper :
    Real.pi * Real.exp (1489 / 800 : ℝ) ≤ (25257510257986097 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1488_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1488_endpointLower :
    (80539 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 100 : ℝ) (1489 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12612975031960043 / 625000000000000 : ℝ) (Real.pi * Real.exp (93 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1488_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1489 / 800 : ℝ) - (93 / 200 : ℝ)) ≤
      (1872323703951861681 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1488_denomUpper
    linarith [hpThetaJensenCell1488_product_upper]
  have hi : (1 / (1872323703951861681 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1489 / 800 : ℝ) - (93 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1872323703951861681 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1872323703951861681 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((93 / 200 : ℝ) - Real.pi * Real.exp (1489 / 800 : ℝ)) := by
    rw [show (93 / 200 : ℝ) - Real.pi * Real.exp (1489 / 800 : ℝ) =
      -(Real.pi * Real.exp (1489 / 800 : ℝ) - (93 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (93 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (93 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1488_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1872323703951861681 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1488_endpointUpper :
    hpThetaJensenKernelEndpointUpper (93 / 100 : ℝ) (1489 / 1600 : ℝ) ≤ (83059 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1489 / 800 : ℝ)) (25257510257986097 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1489 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1488_product_upper
  have hD : (730028937386920541 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (93 / 50 : ℝ) - (1489 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1488_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1488_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (93 / 50 : ℝ) - (1489 / 3200 : ℝ)) ≤
      (1 / (730028937386920541 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (730028937386920541 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1489 / 3200 : ℝ) - Real.pi * Real.exp (93 / 50 : ℝ)) ≤
      (2 / (730028937386920541 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1489 / 3200 : ℝ) - Real.pi * Real.exp (93 / 50 : ℝ) =
      -(Real.pi * Real.exp (93 / 50 : ℝ) - (1489 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25257510257986097 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (25257510257986097 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1488_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (93 / 100 : ℝ) (1489 / 1600 : ℝ)) :
    (80539 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (83059 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1488_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1488_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1489_leftExp :
    (64317714629 / 10000000000 : ℝ) ≤ Real.exp (1489 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1489 / 800 : ℝ) (132486108683 / 125000000000 : ℝ)
    (64317714629 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1489_rightExp :
    Real.exp (149 / 80 : ℝ) ≤ (12879632409 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (149 / 80 : ℝ) (1059930272183 / 1000000000000 : ℝ)
    (12879632409 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1489_denomUpper :
    Real.exp (39531938018687537 / 2000000000000000 : ℝ) ≤ (59988954945310107 / 156250000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (39531938018687537 / 2000000000000000 : ℝ) (1854632441241
    / 1000000000000 : ℝ) (59988954945310107 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1489_denomLower :
    (1871141830458512437 / 5000000000 : ℝ) ≤ Real.exp (24675470967093671 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (24675470967093671 / 1250000000000000 : ℝ) (463287444561
    / 250000000000 : ℝ) (1871141830458512437 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1489_product_lower :
    (25257502217093671 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1489 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1489_leftExp
    (by norm_num : (0 : ℝ) ≤ (64317714629 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1489_product_upper :
    Real.pi * Real.exp (149 / 80 : ℝ) ≤ (40462563018687537 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1489_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1489_endpointLower :
    (39379 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1489 / 1600 : ℝ) (149 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25257502217093671 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1489 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1489_product_lower
  have hD : Real.exp (Real.pi * Real.exp (149 / 80 : ℝ) - (1489 / 3200 : ℝ)) ≤
      (59988954945310107 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1489_denomUpper
    linarith [hpThetaJensenCell1489_product_upper]
  have hi : (1 / (59988954945310107 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (149 / 80 : ℝ) - (1489 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (59988954945310107 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (59988954945310107 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1489 / 3200 : ℝ) - Real.pi * Real.exp (149 / 80 : ℝ)) := by
    rw [show (1489 / 3200 : ℝ) - Real.pi * Real.exp (149 / 80 : ℝ) =
      -(Real.pi * Real.exp (149 / 80 : ℝ) - (1489 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1489 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1489 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1489_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (59988954945310107 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1489_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1489 / 1600 : ℝ) (149 / 160 : ℝ) ≤ (3249 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (149 / 80 : ℝ)) (40462563018687537 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (149 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1489_product_upper
  have hD : (1871141830458512437 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1489 / 800 : ℝ) - (149 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1489_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1489_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1489 / 800 : ℝ) - (149 / 320 : ℝ)) ≤
      (1 / (1871141830458512437 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1871141830458512437 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((149 / 320 : ℝ) - Real.pi * Real.exp (1489 / 800 : ℝ)) ≤
      (2 / (1871141830458512437 / 5000000000 : ℝ) : ℝ) := by
    rw [show (149 / 320 : ℝ) - Real.pi * Real.exp (1489 / 800 : ℝ) =
      -(Real.pi * Real.exp (1489 / 800 : ℝ) - (149 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40462563018687537 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (40462563018687537 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1489_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1489 / 1600 : ℝ) (149 / 160 : ℝ)) :
    (39379 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3249 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1489_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1489_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1490_leftExp :
    (32199081021 / 5000000000 : ℝ) ≤ Real.exp (149 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (149 / 80 : ℝ) (529965136091 / 500000000000 : ℝ)
    (32199081021 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1490_rightExp :
    Real.exp (1491 / 800 : ℝ) ≤ (32239355039 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1491 / 800 : ℝ) (1059971676517 / 1000000000000 : ℝ)
    (32239355039 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1490_denomUpper :
    Real.exp (98954807115037127 / 5000000000000000 : ℝ) ≤ (3936455421073406387 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (98954807115037127 / 5000000000000000 : ℝ) (371216299789
    / 200000000000 : ℝ) (3936455421073406387 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1490_denomLower :
    (1918434797508770667 / 5000000000 : ℝ) ≤ Real.exp (12353335980365679 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12353335980365679 / 625000000000000 : ℝ) (370919169003 /
    200000000000 : ℝ) (1918434797508770667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1490_product_lower :
    (12644546917865679 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (149 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1490_leftExp
    (by norm_num : (0 : ℝ) ≤ (32199081021 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1490_product_upper :
    Real.pi * Real.exp (1491 / 800 : ℝ) ≤ (101282932115037127 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1490_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1490_endpointLower :
    (38507 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (149 / 160 : ℝ) (1491 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12644546917865679 / 625000000000000 : ℝ) (Real.pi * Real.exp (149 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1490_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1491 / 800 : ℝ) - (149 / 320 : ℝ)) ≤
      (3936455421073406387 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1490_denomUpper
    linarith [hpThetaJensenCell1490_product_upper]
  have hi : (1 / (3936455421073406387 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1491 / 800 : ℝ) - (149 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3936455421073406387 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3936455421073406387 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((149 / 320 : ℝ) - Real.pi * Real.exp (1491 / 800 : ℝ)) := by
    rw [show (149 / 320 : ℝ) - Real.pi * Real.exp (1491 / 800 : ℝ) =
      -(Real.pi * Real.exp (1491 / 800 : ℝ) - (149 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (149 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (149 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1490_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3936455421073406387 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1490_endpointUpper :
    hpThetaJensenKernelEndpointUpper (149 / 160 : ℝ) (1491 / 1600 : ℝ) ≤ (79429 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1491 / 800 : ℝ)) (101282932115037127 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1491 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1490_product_upper
  have hD : (1918434797508770667 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (149 / 80 : ℝ) - (1491 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1490_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1490_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (149 / 80 : ℝ) - (1491 / 3200 : ℝ)) ≤
      (1 / (1918434797508770667 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1918434797508770667 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1491 / 3200 : ℝ) - Real.pi * Real.exp (149 / 80 : ℝ)) ≤
      (2 / (1918434797508770667 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1491 / 3200 : ℝ) - Real.pi * Real.exp (149 / 80 : ℝ) =
      -(Real.pi * Real.exp (149 / 80 : ℝ) - (1491 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (101282932115037127 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (101282932115037127 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1490_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (149 / 160 : ℝ) (1491 / 1600 : ℝ)) :
    (38507 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (79429 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1490_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1490_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1491_leftExp :
    (2579148403 / 400000000 : ℝ) ≤ Real.exp (1491 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1491 / 800 : ℝ) (264992919129 / 250000000000 : ℝ)
    (2579148403 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1491_rightExp :
    Real.exp (373 / 200 : ℝ) ≤ (32279679431 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (373 / 200 : ℝ) (106001308247 / 100000000000 : ℝ)
    (32279679431 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1491_denomUpper :
    Real.exp (99079927442673583 / 5000000000000000 : ℝ) ≤ (807240879342323419 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (99079927442673583 / 5000000000000000 : ℝ) (464383381537
    / 250000000000 : ℝ) (807240879342323419 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1491_denomLower :
    (3933970535048891387 / 10000000000 : ℝ) ≤ Real.exp (989516498709697 / 50000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (989516498709697 / 50000000000000 : ℝ) (1856044873659 /
    1000000000000 : ℝ) (3933970535048891387 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1491_product_lower :
    (1012828998709697 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1491 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1491_leftExp
    (by norm_num : (0 : ℝ) ≤ (2579148403 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1491_product_upper :
    Real.pi * Real.exp (373 / 200 : ℝ) ≤ (101409614942673583 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1491_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1491_endpointLower :
    (75307 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1491 / 1600 : ℝ) (373 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1012828998709697 / 50000000000000 : ℝ) (Real.pi * Real.exp (1491 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1491_product_lower
  have hD : Real.exp (Real.pi * Real.exp (373 / 200 : ℝ) - (1491 / 3200 : ℝ)) ≤
      (807240879342323419 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1491_denomUpper
    linarith [hpThetaJensenCell1491_product_upper]
  have hi : (1 / (807240879342323419 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (373 / 200 : ℝ) - (1491 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (807240879342323419 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (807240879342323419 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1491 / 3200 : ℝ) - Real.pi * Real.exp (373 / 200 : ℝ)) := by
    rw [show (1491 / 3200 : ℝ) - Real.pi * Real.exp (373 / 200 : ℝ) =
      -(Real.pi * Real.exp (373 / 200 : ℝ) - (1491 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1491 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1491 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1491_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (807240879342323419 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1491_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1491 / 1600 : ℝ) (373 / 400 : ℝ) ≤ (7767 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (373 / 200 : ℝ)) (101409614942673583 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (373 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1491_product_upper
  have hD : (3933970535048891387 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1491 / 800 : ℝ) - (373 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1491_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1491_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1491 / 800 : ℝ) - (373 / 800 : ℝ)) ≤
      (1 / (3933970535048891387 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3933970535048891387 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((373 / 800 : ℝ) - Real.pi * Real.exp (1491 / 800 : ℝ)) ≤
      (2 / (3933970535048891387 / 10000000000 : ℝ) : ℝ) := by
    rw [show (373 / 800 : ℝ) - Real.pi * Real.exp (1491 / 800 : ℝ) =
      -(Real.pi * Real.exp (1491 / 800 : ℝ) - (373 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (101409614942673583 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (101409614942673583 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1491_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1491 / 1600 : ℝ) (373 / 400 : ℝ)) :
    (75307 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7767 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1491_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1491_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1492_leftExp :
    (64559358859 / 10000000000 : ℝ) ≤ Real.exp (373 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (373 / 200 : ℝ) (1060013082469 / 1000000000000 : ℝ)
    (64559358859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1492_rightExp :
    Real.exp (1493 / 800 : ℝ) ≤ (64640108519 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1493 / 800 : ℝ) (26501362251 / 25000000000 : ℝ)
    (64640108519 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1492_denomUpper :
    Real.exp (198410412442530767 / 10000000000000000 : ℝ) ≤ (129331629447645061 / 312500000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (198410412442530767 / 10000000000000000 : ℝ)
    (1858988530273 / 1000000000000 : ℝ) (129331629447645061 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1492_denomLower :
    (4033656511609920549 / 10000000000 : ℝ) ≤ Real.exp (24769192539570441 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (24769192539570441 / 1250000000000000 : ℝ) (1857496871741
    / 1000000000000 : ℝ) (4033656511609920549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1492_product_lower :
    (25352395664570441 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (373 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1492_leftExp
    (by norm_num : (0 : ℝ) ≤ (64559358859 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1492_product_upper :
    Real.pi * Real.exp (1493 / 800 : ℝ) ≤ (203072912442530767 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1492_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1492_endpointLower :
    (36817 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (373 / 400 : ℝ) (1493 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25352395664570441 / 1250000000000000 : ℝ) (Real.pi * Real.exp (373 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1492_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1493 / 800 : ℝ) - (373 / 800 : ℝ)) ≤
      (129331629447645061 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1492_denomUpper
    linarith [hpThetaJensenCell1492_product_upper]
  have hi : (1 / (129331629447645061 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1493 / 800 : ℝ) - (373 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (129331629447645061 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (129331629447645061 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((373 / 800 : ℝ) - Real.pi * Real.exp (1493 / 800 : ℝ)) := by
    rw [show (373 / 800 : ℝ) - Real.pi * Real.exp (1493 / 800 : ℝ) =
      -(Real.pi * Real.exp (1493 / 800 : ℝ) - (373 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (373 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (373 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1492_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (129331629447645061 / 312500000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1492_endpointUpper :
    hpThetaJensenKernelEndpointUpper (373 / 400 : ℝ) (1493 / 1600 : ℝ) ≤ (18987 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1493 / 800 : ℝ)) (203072912442530767 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1493 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1492_product_upper
  have hD : (4033656511609920549 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (373 / 200 : ℝ) - (1493 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1492_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1492_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (373 / 200 : ℝ) - (1493 / 3200 : ℝ)) ≤
      (1 / (4033656511609920549 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4033656511609920549 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1493 / 3200 : ℝ) - Real.pi * Real.exp (373 / 200 : ℝ)) ≤
      (2 / (4033656511609920549 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1493 / 3200 : ℝ) - Real.pi * Real.exp (373 / 200 : ℝ) =
      -(Real.pi * Real.exp (373 / 200 : ℝ) - (1493 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (203072912442530767 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (203072912442530767 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1492_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (373 / 400 : ℝ) (1493 / 1600 : ℝ)) :
    (36817 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (18987 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1492_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1492_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1493_leftExp :
    (16160027129 / 2500000000 : ℝ) ≤ Real.exp (1493 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1493 / 800 : ℝ) (1060054490039 / 1000000000000 : ℝ)
    (16160027129 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1493_rightExp :
    Real.exp (747 / 400 : ℝ) ≤ (2588838367 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (747 / 400 : ℝ) (1060095899227 / 1000000000000 : ℝ)
    (2588838367 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1493_denomUpper :
    Real.exp (7946451491898631 / 400000000000000 : ℝ) ≤ (4243752858053738721 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (7946451491898631 / 400000000000000 : ℝ) (465111629709 /
    250000000000 : ℝ) (4243752858053738721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1493_denomLower :
    (4135999578179225219 / 10000000000 : ℝ) ≤ Real.exp (6200128056031171 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6200128056031171 / 312500000000000 : ℝ) (929475923343 /
    500000000000 : ℝ) (4135999578179225219 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1493_product_lower :
    (6346026493531171 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1493 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1493_leftExp
    (by norm_num : (0 : ℝ) ≤ (16160027129 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1493_product_upper :
    Real.pi * Real.exp (747 / 400 : ℝ) ≤ (8133076491898631 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1493_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1493_endpointLower :
    (71997 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1493 / 1600 : ℝ) (747 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6346026493531171 / 312500000000000 : ℝ) (Real.pi * Real.exp (1493 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1493_product_lower
  have hD : Real.exp (Real.pi * Real.exp (747 / 400 : ℝ) - (1493 / 3200 : ℝ)) ≤
      (4243752858053738721 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1493_denomUpper
    linarith [hpThetaJensenCell1493_product_upper]
  have hi : (1 / (4243752858053738721 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (747 / 400 : ℝ) - (1493 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4243752858053738721 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4243752858053738721 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1493 / 3200 : ℝ) - Real.pi * Real.exp (747 / 400 : ℝ)) := by
    rw [show (1493 / 3200 : ℝ) - Real.pi * Real.exp (747 / 400 : ℝ) =
      -(Real.pi * Real.exp (747 / 400 : ℝ) - (1493 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1493 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1493 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1493_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4243752858053738721 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1493_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1493 / 1600 : ℝ) (747 / 800 : ℝ) ≤ (74261 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (747 / 400 : ℝ)) (8133076491898631 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (747 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1493_product_upper
  have hD : (4135999578179225219 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1493 / 800 : ℝ) - (747 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1493_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1493_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1493 / 800 : ℝ) - (747 / 1600 : ℝ)) ≤
      (1 / (4135999578179225219 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4135999578179225219 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((747 / 1600 : ℝ) - Real.pi * Real.exp (1493 / 800 : ℝ)) ≤
      (2 / (4135999578179225219 / 10000000000 : ℝ) : ℝ) := by
    rw [show (747 / 1600 : ℝ) - Real.pi * Real.exp (1493 / 800 : ℝ) =
      -(Real.pi * Real.exp (1493 / 800 : ℝ) - (747 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8133076491898631 / 400000000000000 : ℝ) ^ 2 - 6 *
      (8133076491898631 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1493_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1493 / 1600 : ℝ) (747 / 800 : ℝ)) :
    (71997 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (74261 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1493_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1493_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1494_leftExp :
    (16180239793 / 2500000000 : ℝ) ≤ Real.exp (747 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (747 / 400 : ℝ) (530047949613 / 500000000000 : ℝ)
    (16180239793 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1494_rightExp :
    Real.exp (299 / 160 : ℝ) ≤ (64801910959 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (299 / 160 : ℝ) (66258581877 / 62500000000 : ℝ)
    (64801910959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1494_denomUpper :
    Real.exp (198912479855417687 / 10000000000000000 : ℝ) ≤ (271981431749249171 / 625000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (198912479855417687 / 10000000000000000 : ℝ)
    (1861907499429 / 1000000000000 : ℝ) (271981431749249171 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1494_denomLower :
    (4241073887933624133 / 10000000000 : ℝ) ≤ Real.exp (6207967892721307 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6207967892721307 / 312500000000000 : ℝ) (1860409806009 /
    1000000000000 : ℝ) (4241073887933624133 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1494_product_lower :
    (6353963986471307 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (747 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1494_leftExp
    (by norm_num : (0 : ℝ) ≤ (16180239793 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1494_product_upper :
    Real.pi * Real.exp (299 / 160 : ℝ) ≤ (203581229855417687 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1494_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1494_endpointLower :
    (35197 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (747 / 800 : ℝ) (299 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6353963986471307 / 312500000000000 : ℝ) (Real.pi * Real.exp (747 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1494_product_lower
  have hD : Real.exp (Real.pi * Real.exp (299 / 160 : ℝ) - (747 / 1600 : ℝ)) ≤
      (271981431749249171 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1494_denomUpper
    linarith [hpThetaJensenCell1494_product_upper]
  have hi : (1 / (271981431749249171 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (299 / 160 : ℝ) - (747 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (271981431749249171 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (271981431749249171 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((747 / 1600 : ℝ) - Real.pi * Real.exp (299 / 160 : ℝ)) := by
    rw [show (747 / 1600 : ℝ) - Real.pi * Real.exp (299 / 160 : ℝ) =
      -(Real.pi * Real.exp (299 / 160 : ℝ) - (747 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (747 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (747 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1494_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (271981431749249171 / 625000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1494_endpointUpper :
    hpThetaJensenKernelEndpointUpper (747 / 800 : ℝ) (299 / 320 : ℝ) ≤ (7261 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (299 / 160 : ℝ)) (203581229855417687 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (299 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1494_product_upper
  have hD : (4241073887933624133 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (747 / 400 : ℝ) - (299 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1494_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1494_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (747 / 400 : ℝ) - (299 / 640 : ℝ)) ≤
      (1 / (4241073887933624133 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4241073887933624133 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((299 / 640 : ℝ) - Real.pi * Real.exp (747 / 400 : ℝ)) ≤
      (2 / (4241073887933624133 / 10000000000 : ℝ) : ℝ) := by
    rw [show (299 / 640 : ℝ) - Real.pi * Real.exp (747 / 400 : ℝ) =
      -(Real.pi * Real.exp (747 / 400 : ℝ) - (299 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (203581229855417687 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (203581229855417687 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1494_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (747 / 800 : ℝ) (299 / 320 : ℝ)) :
    (35197 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7261 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1494_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1494_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1495_leftExp :
    (16200477739 / 2500000000 : ℝ) ≤ Real.exp (299 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (299 / 160 : ℝ) (1060137310031 / 1000000000000 : ℝ)
    (16200477739 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1495_rightExp :
    Real.exp (187 / 100 : ℝ) ≤ (32441481997 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (187 / 100 : ℝ) (530089361227 / 500000000000 : ℝ)
    (32441481997 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1495_denomUpper :
    Real.exp (99581995251401221 / 5000000000000000 : ℝ) ≤ (89250817466172717 / 200000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (99581995251401221 / 5000000000000000 : ℝ) (931685739777
    / 500000000000 : ℝ) (89250817466172717 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1495_denomLower :
    (4348955756548692691 / 10000000000 : ℝ) ≤ Real.exp (6215817657627561 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6215817657627561 / 312500000000000 : ℝ) (18618707573 /
    10000000000 : ℝ) (4348955756548692691 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1495_product_lower :
    (6361911407627561 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (299 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1495_leftExp
    (by norm_num : (0 : ℝ) ≤ (16200477739 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1495_product_upper :
    Real.pi * Real.exp (187 / 100 : ℝ) ≤ (101917932751401221 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1495_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1495_endpointLower :
    (8603 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (299 / 320 : ℝ) (187 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6361911407627561 / 312500000000000 : ℝ) (Real.pi * Real.exp (299 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1495_product_lower
  have hD : Real.exp (Real.pi * Real.exp (187 / 100 : ℝ) - (299 / 640 : ℝ)) ≤
      (89250817466172717 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1495_denomUpper
    linarith [hpThetaJensenCell1495_product_upper]
  have hi : (1 / (89250817466172717 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (187 / 100 : ℝ) - (299 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (89250817466172717 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (89250817466172717 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((299 / 640 : ℝ) - Real.pi * Real.exp (187 / 100 : ℝ)) := by
    rw [show (299 / 640 : ℝ) - Real.pi * Real.exp (187 / 100 : ℝ) =
      -(Real.pi * Real.exp (187 / 100 : ℝ) - (299 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (299 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (299 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1495_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (89250817466172717 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1495_endpointUpper :
    hpThetaJensenKernelEndpointUpper (299 / 320 : ℝ) (187 / 200 : ℝ) ≤ (70993 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (187 / 100 : ℝ)) (101917932751401221 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (187 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1495_product_upper
  have hD : (4348955756548692691 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (299 / 160 : ℝ) - (187 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1495_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1495_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (299 / 160 : ℝ) - (187 / 400 : ℝ)) ≤
      (1 / (4348955756548692691 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4348955756548692691 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((187 / 400 : ℝ) - Real.pi * Real.exp (299 / 160 : ℝ)) ≤
      (2 / (4348955756548692691 / 10000000000 : ℝ) : ℝ) := by
    rw [show (187 / 400 : ℝ) - Real.pi * Real.exp (299 / 160 : ℝ) =
      -(Real.pi * Real.exp (299 / 160 : ℝ) - (187 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (101917932751401221 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (101917932751401221 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1495_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (299 / 320 : ℝ) (187 / 200 : ℝ)) :
    (8603 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (70993 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1495_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1495_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1496_leftExp :
    (64882963991 / 10000000000 : ℝ) ≤ Real.exp (187 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (187 / 100 : ℝ) (1060178722453 / 1000000000000 : ℝ)
    (64882963991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1496_rightExp :
    Real.exp (1497 / 800 : ℝ) ≤ (64964118409 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1497 / 800 : ℝ) (530110068247 / 500000000000 : ℝ)
    (64964118409 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1496_denomUpper :
    Real.exp (199415819644885537 / 10000000000000000 : ℝ) ≤ (2288173817896592187 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (199415819644885537 / 10000000000000000 : ℝ)
    (1864838466841 / 1000000000000 : ℝ) (2288173817896592187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1496_denomLower :
    (2229861857841287889 / 5000000000 : ℝ) ≤ Real.exp (24894709451301709 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (24894709451301709 / 1250000000000000 : ℝ) (1863334708063
    / 1000000000000 : ℝ) (2229861857841287889 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1496_product_lower :
    (25479475076301709 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (187 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1496_leftExp
    (by norm_num : (0 : ℝ) ≤ (64882963991 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1496_product_upper :
    Real.pi * Real.exp (1497 / 800 : ℝ) ≤ (204090819644885537 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1496_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1496_endpointLower :
    (67287 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (187 / 200 : ℝ) (1497 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25479475076301709 / 1250000000000000 : ℝ) (Real.pi * Real.exp (187 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1496_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1497 / 800 : ℝ) - (187 / 400 : ℝ)) ≤
      (2288173817896592187 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1496_denomUpper
    linarith [hpThetaJensenCell1496_product_upper]
  have hi : (1 / (2288173817896592187 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1497 / 800 : ℝ) - (187 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2288173817896592187 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2288173817896592187 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((187 / 400 : ℝ) - Real.pi * Real.exp (1497 / 800 : ℝ)) := by
    rw [show (187 / 400 : ℝ) - Real.pi * Real.exp (1497 / 800 : ℝ) =
      -(Real.pi * Real.exp (1497 / 800 : ℝ) - (187 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (187 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (187 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1496_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2288173817896592187 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1496_endpointUpper :
    hpThetaJensenKernelEndpointUpper (187 / 200 : ℝ) (1497 / 1600 : ℝ) ≤ (6941 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1497 / 800 : ℝ)) (204090819644885537 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1497 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1496_product_upper
  have hD : (2229861857841287889 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (187 / 100 : ℝ) - (1497 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1496_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1496_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (187 / 100 : ℝ) - (1497 / 3200 : ℝ)) ≤
      (1 / (2229861857841287889 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2229861857841287889 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1497 / 3200 : ℝ) - Real.pi * Real.exp (187 / 100 : ℝ)) ≤
      (2 / (2229861857841287889 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1497 / 3200 : ℝ) - Real.pi * Real.exp (187 / 100 : ℝ) =
      -(Real.pi * Real.exp (187 / 100 : ℝ) - (1497 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (204090819644885537 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (204090819644885537 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1496_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (187 / 200 : ℝ) (1497 / 1600 : ℝ)) :
    (67287 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6941 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1496_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1496_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1497_leftExp :
    (32482059203 / 5000000000 : ℝ) ≤ Real.exp (1497 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1497 / 800 : ℝ) (1060220136493 / 1000000000000 : ℝ)
    (32482059203 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1497_rightExp :
    Real.exp (749 / 400 : ℝ) ≤ (16261343583 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (749 / 400 : ℝ) (132532694019 / 125000000000 : ℝ)
    (16261343583 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1497_denomUpper :
    Real.exp (49916991920947719 / 2500000000000000 : ℝ) ≤ (2346603219227588953 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (49916991920947719 / 2500000000000000 : ℝ) (74652338757 /
    40000000000 : ℝ) (2346603219227588953 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1497_denomLower :
    (4573458595993637017 / 10000000000 : ℝ) ≤ Real.exp (12463094041958897 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (12463094041958897 / 625000000000000 : ℝ) (233100208241 /
    125000000000 : ℝ) (4573458595993637017 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1497_product_lower :
    (12755672166958897 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1497 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1497_leftExp
    (by norm_num : (0 : ℝ) ≤ (32482059203 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1497_product_upper :
    Real.pi * Real.exp (749 / 400 : ℝ) ≤ (51086523170947719 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1497_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1497_endpointLower :
    (65783 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1497 / 1600 : ℝ) (749 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12755672166958897 / 625000000000000 : ℝ) (Real.pi * Real.exp (1497 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1497_product_lower
  have hD : Real.exp (Real.pi * Real.exp (749 / 400 : ℝ) - (1497 / 3200 : ℝ)) ≤
      (2346603219227588953 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1497_denomUpper
    linarith [hpThetaJensenCell1497_product_upper]
  have hi : (1 / (2346603219227588953 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (749 / 400 : ℝ) - (1497 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2346603219227588953 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2346603219227588953 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1497 / 3200 : ℝ) - Real.pi * Real.exp (749 / 400 : ℝ)) := by
    rw [show (1497 / 3200 : ℝ) - Real.pi * Real.exp (749 / 400 : ℝ) =
      -(Real.pi * Real.exp (749 / 400 : ℝ) - (1497 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1497 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1497 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1497_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2346603219227588953 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1497_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1497 / 1600 : ℝ) (749 / 800 : ℝ) ≤ (3393 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (749 / 400 : ℝ)) (51086523170947719 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (749 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1497_product_upper
  have hD : (4573458595993637017 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1497 / 800 : ℝ) - (749 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1497_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1497_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1497 / 800 : ℝ) - (749 / 1600 : ℝ)) ≤
      (1 / (4573458595993637017 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4573458595993637017 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((749 / 1600 : ℝ) - Real.pi * Real.exp (1497 / 800 : ℝ)) ≤
      (2 / (4573458595993637017 / 10000000000 : ℝ) : ℝ) := by
    rw [show (749 / 1600 : ℝ) - Real.pi * Real.exp (1497 / 800 : ℝ) =
      -(Real.pi * Real.exp (1497 / 800 : ℝ) - (749 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51086523170947719 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (51086523170947719 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1497_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1497 / 1600 : ℝ) (749 / 800 : ℝ)) :
    (65783 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3393 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1497_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1497_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1498_leftExp :
    (65045374329 / 10000000000 : ℝ) ≤ Real.exp (749 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (749 / 400 : ℝ) (1060261552151 / 1000000000000 : ℝ)
    (65045374329 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1498_rightExp :
    Real.exp (1499 / 800 : ℝ) ≤ (4070420743 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1499 / 800 : ℝ) (265075742357 / 250000000000 : ℝ)
    (4070420743 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1498_denomUpper :
    Real.exp (12495027188263599 / 625000000000000 : ℝ) ≤ (4813202953823198343 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (12495027188263599 / 625000000000000 : ℝ) (933890746703 /
    500000000000 : ℝ) (4813202953823198343 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1498_denomLower :
    (938048717560751123 / 2000000000 : ℝ) ≤ Real.exp (24957706578623971 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (24957706578623971 / 1250000000000000 : ℝ) (1866271638529
    / 1000000000000 : ℝ) (938048717560751123 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1498_product_lower :
    (25543253453623971 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (749 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1498_leftExp
    (by norm_num : (0 : ℝ) ≤ (65045374329 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1498_product_upper :
    Real.pi * Real.exp (1499 / 800 : ℝ) ≤ (12787605313263599 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1498_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1498_endpointLower :
    (64309 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (749 / 800 : ℝ) (1499 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (25543253453623971 / 1250000000000000 : ℝ) (Real.pi * Real.exp (749 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1498_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1499 / 800 : ℝ) - (749 / 1600 : ℝ)) ≤
      (4813202953823198343 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1498_denomUpper
    linarith [hpThetaJensenCell1498_product_upper]
  have hi : (1 / (4813202953823198343 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1499 / 800 : ℝ) - (749 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4813202953823198343 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4813202953823198343 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((749 / 1600 : ℝ) - Real.pi * Real.exp (1499 / 800 : ℝ)) := by
    rw [show (749 / 1600 : ℝ) - Real.pi * Real.exp (1499 / 800 : ℝ) =
      -(Real.pi * Real.exp (1499 / 800 : ℝ) - (749 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (749 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (749 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1498_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4813202953823198343 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1498_endpointUpper :
    hpThetaJensenKernelEndpointUpper (749 / 800 : ℝ) (1499 / 1600 : ℝ) ≤ (33171 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1499 / 800 : ℝ)) (12787605313263599 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1499 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1498_product_upper
  have hD : (938048717560751123 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (749 / 400 : ℝ) - (1499 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1498_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1498_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (749 / 400 : ℝ) - (1499 / 3200 : ℝ)) ≤
      (1 / (938048717560751123 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (938048717560751123 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1499 / 3200 : ℝ) - Real.pi * Real.exp (749 / 400 : ℝ)) ≤
      (2 / (938048717560751123 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1499 / 3200 : ℝ) - Real.pi * Real.exp (749 / 400 : ℝ) =
      -(Real.pi * Real.exp (749 / 400 : ℝ) - (1499 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12787605313263599 / 625000000000000 : ℝ) ^ 2 - 6 *
      (12787605313263599 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1498_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (749 / 800 : ℝ) (1499 / 1600 : ℝ)) :
    (64309 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (33171 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1498_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1498_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1499_leftExp :
    (13025346377 / 2000000000 : ℝ) ≤ Real.exp (1499 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1499 / 800 : ℝ) (1060302969427 / 1000000000000 : ℝ)
    (13025346377 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1499_rightExp :
    Real.exp (15 / 8 : ℝ) ≤ (13041638241 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15 / 8 : ℝ) (530172194161 / 500000000000 : ℝ)
    (13041638241 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1499_denomUpper :
    Real.exp (40034644406457913 / 2000000000000000 : ℝ) ≤ (4936425366735233161 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (40034644406457913 / 2000000000000000 : ℝ) (46731438699 /
    25000000000 : ℝ) (4936425366735233161 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1499_denomLower :
    (4810164309488995383 / 10000000000 : ℝ) ≤ Real.exp (4997852996901523 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4997852996901523 / 250000000000000 : ℝ) (933872316733 /
    500000000000 : ℝ) (4810164309488995383 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1499_product_lower :
    (5115040496901523 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1499 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1499_leftExp
    (by norm_num : (0 : ℝ) ≤ (13025346377 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1499_product_upper :
    Real.pi * Real.exp (15 / 8 : ℝ) ≤ (40971519406457913 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1499_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1499_endpointLower :
    (62867 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1499 / 1600 : ℝ) (15 / 16 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5115040496901523 / 250000000000000 : ℝ) (Real.pi * Real.exp (1499 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1499_product_lower
  have hD : Real.exp (Real.pi * Real.exp (15 / 8 : ℝ) - (1499 / 3200 : ℝ)) ≤
      (4936425366735233161 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1499_denomUpper
    linarith [hpThetaJensenCell1499_product_upper]
  have hi : (1 / (4936425366735233161 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (15 / 8 : ℝ) - (1499 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4936425366735233161 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4936425366735233161 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1499 / 3200 : ℝ) - Real.pi * Real.exp (15 / 8 : ℝ)) := by
    rw [show (1499 / 3200 : ℝ) - Real.pi * Real.exp (15 / 8 : ℝ) =
      -(Real.pi * Real.exp (15 / 8 : ℝ) - (1499 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1499 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1499 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1499_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4936425366735233161 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1499_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1499 / 1600 : ℝ) (15 / 16 : ℝ) ≤ (64857 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (15 / 8 : ℝ)) (40971519406457913 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (15 / 16 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1499_product_upper
  have hD : (4810164309488995383 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1499 / 800 : ℝ) - (15 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell1499_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1499_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1499 / 800 : ℝ) - (15 / 32 : ℝ)) ≤
      (1 / (4810164309488995383 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4810164309488995383 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((15 / 32 : ℝ) - Real.pi * Real.exp (1499 / 800 : ℝ)) ≤
      (2 / (4810164309488995383 / 10000000000 : ℝ) : ℝ) := by
    rw [show (15 / 32 : ℝ) - Real.pi * Real.exp (1499 / 800 : ℝ) =
      -(Real.pi * Real.exp (1499 / 800 : ℝ) - (15 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40971519406457913 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (40971519406457913 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1499_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1499 / 1600 : ℝ) (15 / 16 : ℝ)) :
    (62867 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (64857 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1499_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1499_endpointUpper

def hpThetaJensenCellsBatch074Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (48103 / 5000000000 : ℝ)
  | 1 => (94103 / 10000000000 : ℝ)
  | 2 => (46021 / 5000000000 : ℝ)
  | 3 => (11253 / 1250000000 : ℝ)
  | 4 => (88047 / 10000000000 : ℝ)
  | 5 => (86111 / 10000000000 : ℝ)
  | 6 => (16843 / 2000000000 : ℝ)
  | 7 => (41179 / 5000000000 : ℝ)
  | 8 => (80539 / 10000000000 : ℝ)
  | 9 => (39379 / 5000000000 : ℝ)
  | 10 => (38507 / 5000000000 : ℝ)
  | 11 => (75307 / 10000000000 : ℝ)
  | 12 => (36817 / 5000000000 : ℝ)
  | 13 => (71997 / 10000000000 : ℝ)
  | 14 => (35197 / 5000000000 : ℝ)
  | 15 => (8603 / 1250000000 : ℝ)
  | 16 => (67287 / 10000000000 : ℝ)
  | 17 => (65783 / 10000000000 : ℝ)
  | 18 => (64309 / 10000000000 : ℝ)
  | 19 => (62867 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch074Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (99191 / 10000000000 : ℝ)
  | 1 => (3881 / 400000000 : ℝ)
  | 2 => (94903 / 10000000000 : ℝ)
  | 3 => (3713 / 400000000 : ℝ)
  | 4 => (9079 / 1000000000 : ℝ)
  | 5 => (88797 / 10000000000 : ℝ)
  | 6 => (21711 / 2500000000 : ℝ)
  | 7 => (21233 / 2500000000 : ℝ)
  | 8 => (83059 / 10000000000 : ℝ)
  | 9 => (3249 / 400000000 : ℝ)
  | 10 => (79429 / 10000000000 : ℝ)
  | 11 => (7767 / 1000000000 : ℝ)
  | 12 => (18987 / 2500000000 : ℝ)
  | 13 => (74261 / 10000000000 : ℝ)
  | 14 => (7261 / 1000000000 : ℝ)
  | 15 => (70993 / 10000000000 : ℝ)
  | 16 => (6941 / 1000000000 : ℝ)
  | 17 => (3393 / 500000000 : ℝ)
  | 18 => (33171 / 5000000000 : ℝ)
  | 19 => (64857 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch074_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch074Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch074Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1480_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1481_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1482_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1483_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1484_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1485_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1486_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1487_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1488_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1489_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1490_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1491_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1492_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1493_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1494_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1495_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1496_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1497_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1498_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1499_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper] at h ⊢
    exact h

end HodgeProofHP
