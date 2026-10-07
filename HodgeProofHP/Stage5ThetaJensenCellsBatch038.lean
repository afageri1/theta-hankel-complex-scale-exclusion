import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell760_leftExp :
    (1616068537 / 625000000 : ℝ) ≤ Real.exp (19 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 20 : ℝ) (1030132567221 / 1000000000000 : ℝ)
    (1616068537 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell760_rightExp :
    Real.exp (761 / 800 : ℝ) ≤ (12944719087 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (761 / 800 : ℝ) (1030172807561 / 1000000000000 : ℝ)
    (12944719087 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell760_denomUpper :
    Real.exp (39479538870685591 / 5000000000000000 : ℝ) ≤ (13431334969049 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39479538870685591 / 5000000000000000 : ℝ) (63992770969 /
    50000000000 : ℝ) (13431334969049 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell760_denomLower :
    (830710592317 / 312500000 : ℝ) ≤ Real.exp (616049396848863 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (616049396848863 / 78125000000000 : ℝ) (1279436515499 /
    1000000000000 : ℝ) (830710592317 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell760_product_lower :
    (634628498411363 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell760_leftExp
    (by norm_num : (0 : ℝ) ≤ (1616068537 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell760_product_upper :
    Real.pi * Real.exp (761 / 800 : ℝ) ≤ (40667038870685591 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell760_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell760_endpointLower :
    (100143133 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 40 : ℝ) (761 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (634628498411363 / 78125000000000 : ℝ) (Real.pi * Real.exp (19 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell760_product_lower
  have hD : Real.exp (Real.pi * Real.exp (761 / 800 : ℝ) - (19 / 80 : ℝ)) ≤
      (13431334969049 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell760_denomUpper
    linarith [hpThetaJensenCell760_product_upper]
  have hi : (1 / (13431334969049 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (761 / 800 : ℝ) - (19 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13431334969049 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13431334969049 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 80 : ℝ) - Real.pi * Real.exp (761 / 800 : ℝ)) := by
    rw [show (19 / 80 : ℝ) - Real.pi * Real.exp (761 / 800 : ℝ) =
      -(Real.pi * Real.exp (761 / 800 : ℝ) - (19 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 20 : ℝ)) := by
    have h := hpThetaJensenCell760_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13431334969049 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell760_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 40 : ℝ) (761 / 1600 : ℝ) ≤ (203494061 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (761 / 800 : ℝ)) (40667038870685591 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (761 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell760_product_upper
  have hD : (830710592317 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 20 : ℝ) - (761 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell760_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell760_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 20 : ℝ) - (761 / 3200 : ℝ)) ≤
      (1 / (830710592317 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (830710592317 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((761 / 3200 : ℝ) - Real.pi * Real.exp (19 / 20 : ℝ)) ≤
      (2 / (830710592317 / 312500000 : ℝ) : ℝ) := by
    rw [show (761 / 3200 : ℝ) - Real.pi * Real.exp (19 / 20 : ℝ) =
      -(Real.pi * Real.exp (19 / 20 : ℝ) - (761 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40667038870685591 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (40667038870685591 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell760_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 40 : ℝ) (761 / 1600 : ℝ)) :
    (100143133 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (203494061 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell760_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell760_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell761_leftExp :
    (6472359543 / 2500000000 : ℝ) ≤ Real.exp (761 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (761 / 800 : ℝ) (25754320189 / 25000000000 : ℝ)
    (6472359543 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell761_rightExp :
    Real.exp (381 / 400 : ℝ) ≤ (25921820207 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (381 / 400 : ℝ) (1030213049473 / 1000000000000 : ℝ)
    (25921820207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell761_denomUpper :
    Real.exp (79057683909569751 / 10000000000000000 : ℝ) ≤ (27128862688383 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (79057683909569751 / 10000000000000000 : ℝ) (128024986027
    / 100000000000 : ℝ) (27128862688383 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell761_denomLower :
    (5369163298887 / 2000000000 : ℝ) ≤ Real.exp (2467275057676557 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2467275057676557 / 312500000000000 : ℝ) (1279830318877 /
    1000000000000 : ℝ) (5369163298887 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell761_product_lower :
    (2541689120176557 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (761 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell761_leftExp
    (by norm_num : (0 : ℝ) ≤ (6472359543 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell761_product_upper :
    Real.pi * Real.exp (381 / 400 : ℝ) ≤ (81435808909569751 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell761_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell761_endpointLower :
    (795494787 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (761 / 1600 : ℝ) (381 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2541689120176557 / 312500000000000 : ℝ) (Real.pi * Real.exp (761 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell761_product_lower
  have hD : Real.exp (Real.pi * Real.exp (381 / 400 : ℝ) - (761 / 3200 : ℝ)) ≤
      (27128862688383 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell761_denomUpper
    linarith [hpThetaJensenCell761_product_upper]
  have hi : (1 / (27128862688383 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (381 / 400 : ℝ) - (761 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27128862688383 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27128862688383 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((761 / 3200 : ℝ) - Real.pi * Real.exp (381 / 400 : ℝ)) := by
    rw [show (761 / 3200 : ℝ) - Real.pi * Real.exp (381 / 400 : ℝ) =
      -(Real.pi * Real.exp (381 / 400 : ℝ) - (761 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (761 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (761 / 800 : ℝ)) := by
    have h := hpThetaJensenCell761_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27128862688383 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell761_endpointUpper :
    hpThetaJensenKernelEndpointUpper (761 / 1600 : ℝ) (381 / 800 : ℝ) ≤ (202061349 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (381 / 400 : ℝ)) (81435808909569751 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (381 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell761_product_upper
  have hD : (5369163298887 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (761 / 800 : ℝ) - (381 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell761_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell761_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (761 / 800 : ℝ) - (381 / 1600 : ℝ)) ≤
      (1 / (5369163298887 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5369163298887 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((381 / 1600 : ℝ) - Real.pi * Real.exp (761 / 800 : ℝ)) ≤
      (2 / (5369163298887 / 2000000000 : ℝ) : ℝ) := by
    rw [show (381 / 1600 : ℝ) - Real.pi * Real.exp (761 / 800 : ℝ) =
      -(Real.pi * Real.exp (761 / 800 : ℝ) - (381 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (81435808909569751 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (81435808909569751 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell761_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (761 / 1600 : ℝ) (381 / 800 : ℝ)) :
    (795494787 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (202061349 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell761_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell761_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell762_leftExp :
    (5184364041 / 2000000000 : ℝ) ≤ Real.exp (381 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (381 / 400 : ℝ) (8048539449 / 7812500000 : ℝ) (5184364041
    / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell762_rightExp :
    Real.exp (763 / 800 : ℝ) ≤ (12977121371 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (763 / 800 : ℝ) (257563323239 / 250000000000 : ℝ)
    (12977121371 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell762_denomUpper :
    Real.exp (39578208659284003 / 5000000000000000 : ℝ) ≤ (27398041859891 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39578208659284003 / 5000000000000000 : ℝ) (1280644931943
    / 1000000000000 : ℝ) (27398041859891 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell762_denomLower :
    (13555921075213 / 5000000000 : ℝ) ≤ Real.exp (1976285199536659 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1976285199536659 / 250000000000000 : ℝ) (1280224751903 /
    1000000000000 : ℝ) (13555921075213 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell762_product_lower :
    (2035894574536659 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (381 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell762_leftExp
    (by norm_num : (0 : ℝ) ≤ (5184364041 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell762_product_upper :
    Real.pi * Real.exp (763 / 800 : ℝ) ≤ (40768833659284003 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell762_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell762_endpointLower :
    (789873967 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (381 / 800 : ℝ) (763 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2035894574536659 / 250000000000000 : ℝ) (Real.pi * Real.exp (381 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell762_product_lower
  have hD : Real.exp (Real.pi * Real.exp (763 / 800 : ℝ) - (381 / 1600 : ℝ)) ≤
      (27398041859891 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell762_denomUpper
    linarith [hpThetaJensenCell762_product_upper]
  have hi : (1 / (27398041859891 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (763 / 800 : ℝ) - (381 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27398041859891 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27398041859891 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((381 / 1600 : ℝ) - Real.pi * Real.exp (763 / 800 : ℝ)) := by
    rw [show (381 / 1600 : ℝ) - Real.pi * Real.exp (763 / 800 : ℝ) =
      -(Real.pi * Real.exp (763 / 800 : ℝ) - (381 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (381 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (381 / 400 : ℝ)) := by
    have h := hpThetaJensenCell762_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27398041859891 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell762_endpointUpper :
    hpThetaJensenKernelEndpointUpper (381 / 800 : ℝ) (763 / 1600 : ℝ) ≤ (16050887 / 100000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (763 / 800 : ℝ)) (40768833659284003 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (763 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell762_product_upper
  have hD : (13555921075213 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (381 / 400 : ℝ) - (763 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell762_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell762_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (381 / 400 : ℝ) - (763 / 3200 : ℝ)) ≤
      (1 / (13555921075213 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13555921075213 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((763 / 3200 : ℝ) - Real.pi * Real.exp (381 / 400 : ℝ)) ≤
      (2 / (13555921075213 / 5000000000 : ℝ) : ℝ) := by
    rw [show (763 / 3200 : ℝ) - Real.pi * Real.exp (381 / 400 : ℝ) =
      -(Real.pi * Real.exp (381 / 400 : ℝ) - (763 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (40768833659284003 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (40768833659284003 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell762_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (381 / 800 : ℝ) (763 / 1600 : ℝ)) :
    (789873967 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16050887 / 100000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell762_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell762_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell763_leftExp :
    (1297712137 / 500000000 : ℝ) ≤ Real.exp (763 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (763 / 800 : ℝ) (206050658591 / 200000000000 : ℝ)
    (1297712137 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell763_rightExp :
    Real.exp (191 / 200 : ℝ) ≤ (2598670583 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (191 / 200 : ℝ) (1030293538011 / 1000000000000 : ℝ)
    (2598670583 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell763_denomUpper :
    Real.exp (7925527812858719 / 1000000000000000 : ℝ) ≤ (27670244412589 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7925527812858719 / 1000000000000000 : ℝ) (25620812711 /
    20000000000 : ℝ) (27670244412589 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell763_denomLower :
    (6845213087799 / 2500000000 : ℝ) ≤ Real.exp (494688383487763 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (494688383487763 / 62500000000000 : ℝ) (640309907849 /
    500000000000 : ℝ) (6845213087799 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell763_product_lower :
    (509610258487763 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (763 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell763_leftExp
    (by norm_num : (0 : ℝ) ≤ (1297712137 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell763_product_upper :
    Real.pi * Real.exp (191 / 200 : ℝ) ≤ (8163965312858719 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell763_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell763_endpointLower :
    (196070633 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (763 / 1600 : ℝ) (191 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (509610258487763 / 62500000000000 : ℝ) (Real.pi * Real.exp (763 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell763_product_lower
  have hD : Real.exp (Real.pi * Real.exp (191 / 200 : ℝ) - (763 / 3200 : ℝ)) ≤
      (27670244412589 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell763_denomUpper
    linarith [hpThetaJensenCell763_product_upper]
  have hi : (1 / (27670244412589 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (191 / 200 : ℝ) - (763 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27670244412589 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27670244412589 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((763 / 3200 : ℝ) - Real.pi * Real.exp (191 / 200 : ℝ)) := by
    rw [show (763 / 3200 : ℝ) - Real.pi * Real.exp (191 / 200 : ℝ) =
      -(Real.pi * Real.exp (191 / 200 : ℝ) - (763 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (763 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (763 / 800 : ℝ)) := by
    have h := hpThetaJensenCell763_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27670244412589 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell763_endpointUpper :
    hpThetaJensenKernelEndpointUpper (763 / 1600 : ℝ) (191 / 400 : ℝ) ≤ (796873033 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (191 / 200 : ℝ)) (8163965312858719 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (191 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell763_product_upper
  have hD : (6845213087799 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (763 / 800 : ℝ) - (191 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell763_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell763_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (763 / 800 : ℝ) - (191 / 800 : ℝ)) ≤
      (1 / (6845213087799 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6845213087799 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((191 / 800 : ℝ) - Real.pi * Real.exp (763 / 800 : ℝ)) ≤
      (2 / (6845213087799 / 2500000000 : ℝ) : ℝ) := by
    rw [show (191 / 800 : ℝ) - Real.pi * Real.exp (763 / 800 : ℝ) =
      -(Real.pi * Real.exp (763 / 800 : ℝ) - (191 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8163965312858719 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (8163965312858719 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell763_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (763 / 1600 : ℝ) (191 / 400 : ℝ)) :
    (196070633 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (796873033 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell763_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell763_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell764_leftExp :
    (6496676457 / 2500000000 : ℝ) ≤ Real.exp (191 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (191 / 200 : ℝ) (103029353801 / 100000000000 : ℝ)
    (6496676457 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell764_rightExp :
    Real.exp (153 / 160 : ℝ) ≤ (26019209523 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (153 / 160 : ℝ) (1030333784639 / 1000000000000 : ℝ)
    (26019209523 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell764_denomUpper :
    Real.exp (79354266502990139 / 10000000000000000 : ℝ) ≤ (6986376952453 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79354266502990139 / 10000000000000000 : ℝ) (640718486127
    / 500000000000 : ℝ) (6986376952453 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell764_denomLower :
    (2765288403417 / 1000000000 : ℝ) ≤ Real.exp (2476531316737443 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2476531316737443 / 312500000000000 : ℝ) (640507755707 /
    500000000000 : ℝ) (2765288403417 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell764_product_lower :
    (2551238347987443 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (191 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell764_leftExp
    (by norm_num : (0 : ℝ) ≤ (6496676457 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell764_product_upper :
    Real.pi * Real.exp (153 / 160 : ℝ) ≤ (81741766502990139 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell764_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell764_endpointLower :
    (97340051 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (191 / 400 : ℝ) (153 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2551238347987443 / 312500000000000 : ℝ) (Real.pi * Real.exp (191 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell764_product_lower
  have hD : Real.exp (Real.pi * Real.exp (153 / 160 : ℝ) - (191 / 800 : ℝ)) ≤
      (6986376952453 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell764_denomUpper
    linarith [hpThetaJensenCell764_product_upper]
  have hi : (1 / (6986376952453 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (153 / 160 : ℝ) - (191 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6986376952453 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6986376952453 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((191 / 800 : ℝ) - Real.pi * Real.exp (153 / 160 : ℝ)) := by
    rw [show (191 / 800 : ℝ) - Real.pi * Real.exp (153 / 160 : ℝ) =
      -(Real.pi * Real.exp (153 / 160 : ℝ) - (191 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (191 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (191 / 200 : ℝ)) := by
    have h := hpThetaJensenCell764_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6986376952453 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell764_endpointUpper :
    hpThetaJensenKernelEndpointUpper (191 / 400 : ℝ) (153 / 320 : ℝ) ≤ (197807843 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (153 / 160 : ℝ)) (81741766502990139 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (153 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell764_product_upper
  have hD : (2765288403417 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (191 / 200 : ℝ) - (153 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell764_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell764_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (191 / 200 : ℝ) - (153 / 640 : ℝ)) ≤
      (1 / (2765288403417 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2765288403417 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((153 / 640 : ℝ) - Real.pi * Real.exp (191 / 200 : ℝ)) ≤
      (2 / (2765288403417 / 1000000000 : ℝ) : ℝ) := by
    rw [show (153 / 640 : ℝ) - Real.pi * Real.exp (191 / 200 : ℝ) =
      -(Real.pi * Real.exp (191 / 200 : ℝ) - (153 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (81741766502990139 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (81741766502990139 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell764_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (191 / 400 : ℝ) (153 / 320 : ℝ)) :
    (97340051 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (197807843 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell764_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell764_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell765_leftExp :
    (26019209521 / 10000000000 : ℝ) ≤ Real.exp (153 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (153 / 160 : ℝ) (515166892319 / 500000000000 : ℝ)
    (26019209521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell765_rightExp :
    Real.exp (383 / 400 : ℝ) ≤ (26051753871 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (383 / 400 : ℝ) (515187016419 / 500000000000 : ℝ)
    (26051753871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell765_denomUpper :
    Real.exp (79453382598856503 / 10000000000000000 : ℝ) ≤ (28223870003203 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (79453382598856503 / 10000000000000000 : ℝ) (640916971599
    / 500000000000 : ℝ) (28223870003203 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell765_denomLower :
    (27927974639853 / 10000000000 : ℝ) ≤ Real.exp (9918498809687179 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9918498809687179 / 1250000000000000 : ℝ) (256282368043 /
    200000000000 : ℝ) (27927974639853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell765_product_lower :
    (10217717559687179 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (153 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell765_leftExp
    (by norm_num : (0 : ℝ) ≤ (26019209521 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell765_product_upper :
    Real.pi * Real.exp (383 / 400 : ℝ) ≤ (81844007598856503 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell765_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell765_endpointLower :
    (386593761 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (153 / 320 : ℝ) (383 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10217717559687179 / 1250000000000000 : ℝ) (Real.pi * Real.exp (153 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell765_product_lower
  have hD : Real.exp (Real.pi * Real.exp (383 / 400 : ℝ) - (153 / 640 : ℝ)) ≤
      (28223870003203 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell765_denomUpper
    linarith [hpThetaJensenCell765_product_upper]
  have hi : (1 / (28223870003203 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (383 / 400 : ℝ) - (153 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (28223870003203 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (28223870003203 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((153 / 640 : ℝ) - Real.pi * Real.exp (383 / 400 : ℝ)) := by
    rw [show (153 / 640 : ℝ) - Real.pi * Real.exp (383 / 400 : ℝ) =
      -(Real.pi * Real.exp (383 / 400 : ℝ) - (153 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (153 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (153 / 160 : ℝ)) := by
    have h := hpThetaJensenCell765_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (28223870003203 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell765_endpointUpper :
    hpThetaJensenKernelEndpointUpper (153 / 320 : ℝ) (383 / 800 : ℝ) ≤ (785619293 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (383 / 400 : ℝ)) (81844007598856503 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (383 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell765_product_upper
  have hD : (27927974639853 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (153 / 160 : ℝ) - (383 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell765_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell765_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (153 / 160 : ℝ) - (383 / 1600 : ℝ)) ≤
      (1 / (27927974639853 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (27927974639853 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((383 / 1600 : ℝ) - Real.pi * Real.exp (153 / 160 : ℝ)) ≤
      (2 / (27927974639853 / 10000000000 : ℝ) : ℝ) := by
    rw [show (383 / 1600 : ℝ) - Real.pi * Real.exp (153 / 160 : ℝ) =
      -(Real.pi * Real.exp (153 / 160 : ℝ) - (383 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (81844007598856503 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (81844007598856503 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell765_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (153 / 320 : ℝ) (383 / 800 : ℝ)) :
    (386593761 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (785619293 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell765_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell765_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell766_leftExp :
    (26051753869 / 10000000000 : ℝ) ≤ Real.exp (383 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (383 / 400 : ℝ) (1030374032837 / 1000000000000 : ℝ)
    (26051753869 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell766_rightExp :
    Real.exp (767 / 800 : ℝ) ≤ (1043373557 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (767 / 800 : ℝ) (103041428261 / 100000000000 : ℝ)
    (1043373557 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell766_denomUpper :
    Real.exp (3182105063056301 / 400000000000000 : ℝ) ≤ (14252684730287 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3182105063056301 / 400000000000000 : ℝ) (256446309907 /
    200000000000 : ℝ) (14252684730287 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell766_denomLower :
    (28206162095367 / 10000000000 : ℝ) ≤ Real.exp (9930888317602431 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9930888317602431 / 1250000000000000 : ℝ) (1281808803243
    / 1000000000000 : ℝ) (28206162095367 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell766_product_lower :
    (10230497692602431 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (383 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell766_leftExp
    (by norm_num : (0 : ℝ) ≤ (26051753869 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell766_product_upper :
    Real.pi * Real.exp (767 / 800 : ℝ) ≤ (3277855063056301 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell766_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell766_endpointLower :
    (1535367601 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (383 / 800 : ℝ) (767 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10230497692602431 / 1250000000000000 : ℝ) (Real.pi * Real.exp (383 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell766_product_lower
  have hD : Real.exp (Real.pi * Real.exp (767 / 800 : ℝ) - (383 / 1600 : ℝ)) ≤
      (14252684730287 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell766_denomUpper
    linarith [hpThetaJensenCell766_product_upper]
  have hi : (1 / (14252684730287 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (767 / 800 : ℝ) - (383 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14252684730287 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14252684730287 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((383 / 1600 : ℝ) - Real.pi * Real.exp (767 / 800 : ℝ)) := by
    rw [show (383 / 1600 : ℝ) - Real.pi * Real.exp (767 / 800 : ℝ) =
      -(Real.pi * Real.exp (767 / 800 : ℝ) - (383 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (383 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (383 / 400 : ℝ)) := by
    have h := hpThetaJensenCell766_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14252684730287 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell766_endpointUpper :
    hpThetaJensenKernelEndpointUpper (383 / 800 : ℝ) (767 / 1600 : ℝ) ≤ (390018361 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (767 / 800 : ℝ)) (3277855063056301 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (767 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell766_product_upper
  have hD : (28206162095367 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (383 / 400 : ℝ) - (767 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell766_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell766_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (383 / 400 : ℝ) - (767 / 3200 : ℝ)) ≤
      (1 / (28206162095367 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28206162095367 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((767 / 3200 : ℝ) - Real.pi * Real.exp (383 / 400 : ℝ)) ≤
      (2 / (28206162095367 / 10000000000 : ℝ) : ℝ) := by
    rw [show (767 / 3200 : ℝ) - Real.pi * Real.exp (383 / 400 : ℝ) =
      -(Real.pi * Real.exp (383 / 400 : ℝ) - (767 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3277855063056301 / 400000000000000 : ℝ) ^ 2 - 6 *
      (3277855063056301 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell766_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (383 / 800 : ℝ) (767 / 1600 : ℝ)) :
    (1535367601 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (390018361 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell766_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell766_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell767_leftExp :
    (26084338923 / 10000000000 : ℝ) ≤ Real.exp (767 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (767 / 800 : ℝ) (1030414282609 / 1000000000000 : ℝ)
    (26084338923 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell767_rightExp :
    Real.exp (24 / 25 : ℝ) ≤ (5223392947 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (24 / 25 : ℝ) (515227266977 / 500000000000 : ℝ)
    (5223392947 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell767_denomUpper :
    Real.exp (15930399718544571 / 2000000000000000 : ℝ) ≤ (28790045162049 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15930399718544571 / 2000000000000000 : ℝ) (320657448103
    / 250000000000 : ℝ) (28790045162049 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell767_denomLower :
    (14243742422539 / 5000000000 : ℝ) ≤ Real.exp (9943293810723177 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9943293810723177 / 1250000000000000 : ℝ) (320551600413 /
    250000000000 : ℝ) (14243742422539 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell767_product_lower :
    (10243293810723177 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (767 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell767_leftExp
    (by norm_num : (0 : ℝ) ≤ (26084338923 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell767_product_upper :
    Real.pi * Real.exp (24 / 25 : ℝ) ≤ (16409774718544571 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell767_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell767_endpointLower :
    (762209169 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (767 / 1600 : ℝ) (12 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10243293810723177 / 1250000000000000 : ℝ) (Real.pi * Real.exp (767 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell767_product_lower
  have hD : Real.exp (Real.pi * Real.exp (24 / 25 : ℝ) - (767 / 3200 : ℝ)) ≤
      (28790045162049 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell767_denomUpper
    linarith [hpThetaJensenCell767_product_upper]
  have hi : (1 / (28790045162049 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (24 / 25 : ℝ) - (767 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (28790045162049 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (28790045162049 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((767 / 3200 : ℝ) - Real.pi * Real.exp (24 / 25 : ℝ)) := by
    rw [show (767 / 3200 : ℝ) - Real.pi * Real.exp (24 / 25 : ℝ) =
      -(Real.pi * Real.exp (24 / 25 : ℝ) - (767 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (767 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (767 / 800 : ℝ)) := by
    have h := hpThetaJensenCell767_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (28790045162049 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell767_endpointUpper :
    hpThetaJensenKernelEndpointUpper (767 / 1600 : ℝ) (12 / 25 : ℝ) ≤ (1548967169 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (24 / 25 : ℝ)) (16409774718544571 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (12 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell767_product_upper
  have hD : (14243742422539 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (767 / 800 : ℝ) - (6 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell767_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell767_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (767 / 800 : ℝ) - (6 / 25 : ℝ)) ≤
      (1 / (14243742422539 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14243742422539 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((6 / 25 : ℝ) - Real.pi * Real.exp (767 / 800 : ℝ)) ≤
      (2 / (14243742422539 / 5000000000 : ℝ) : ℝ) := by
    rw [show (6 / 25 : ℝ) - Real.pi * Real.exp (767 / 800 : ℝ) =
      -(Real.pi * Real.exp (767 / 800 : ℝ) - (6 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16409774718544571 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (16409774718544571 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell767_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (767 / 1600 : ℝ) (12 / 25 : ℝ)) :
    (762209169 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1548967169 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell767_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell767_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell768_leftExp :
    (26116964733 / 10000000000 : ℝ) ≤ Real.exp (24 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (24 / 25 : ℝ) (1030454533953 / 1000000000000 : ℝ)
    (26116964733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell768_rightExp :
    Real.exp (769 / 800 : ℝ) ≤ (26149631353 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (769 / 800 : ℝ) (103049478687 / 100000000000 : ℝ)
    (26149631353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell768_denomUpper :
    Real.exp (79751498811165329 / 10000000000000000 : ℝ) ≤ (1817371039269 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79751498811165329 / 10000000000000000 : ℝ)
    (1283028672999 / 1000000000000 : ℝ) (1817371039269 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell768_denomLower :
    (14385990921607 / 5000000000 : ℝ) ≤ Real.exp (9955715308684367 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9955715308684367 / 1250000000000000 : ℝ) (1282604636587
    / 1000000000000 : ℝ) (14385990921607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell768_product_lower :
    (10256105933684367 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (24 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell768_leftExp
    (by norm_num : (0 : ℝ) ≤ (26116964733 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell768_product_upper :
    Real.pi * Real.exp (769 / 800 : ℝ) ≤ (82151498811165329 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell768_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell768_endpointLower :
    (302705421 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (12 / 25 : ℝ) (769 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10256105933684367 / 1250000000000000 : ℝ) (Real.pi * Real.exp (24 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell768_product_lower
  have hD : Real.exp (Real.pi * Real.exp (769 / 800 : ℝ) - (6 / 25 : ℝ)) ≤
      (1817371039269 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell768_denomUpper
    linarith [hpThetaJensenCell768_product_upper]
  have hi : (1 / (1817371039269 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (769 / 800 : ℝ) - (6 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1817371039269 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1817371039269 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((6 / 25 : ℝ) - Real.pi * Real.exp (769 / 800 : ℝ)) := by
    rw [show (6 / 25 : ℝ) - Real.pi * Real.exp (769 / 800 : ℝ) =
      -(Real.pi * Real.exp (769 / 800 : ℝ) - (6 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (24 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (24 / 25 : ℝ)) := by
    have h := hpThetaJensenCell768_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1817371039269 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell768_endpointUpper :
    hpThetaJensenKernelEndpointUpper (12 / 25 : ℝ) (769 / 1600 : ℝ) ≤ (153791961 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (769 / 800 : ℝ)) (82151498811165329 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (769 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell768_product_upper
  have hD : (14385990921607 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (24 / 25 : ℝ) - (769 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell768_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell768_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (24 / 25 : ℝ) - (769 / 3200 : ℝ)) ≤
      (1 / (14385990921607 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14385990921607 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((769 / 3200 : ℝ) - Real.pi * Real.exp (24 / 25 : ℝ)) ≤
      (2 / (14385990921607 / 5000000000 : ℝ) : ℝ) := by
    rw [show (769 / 3200 : ℝ) - Real.pi * Real.exp (24 / 25 : ℝ) =
      -(Real.pi * Real.exp (24 / 25 : ℝ) - (769 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (82151498811165329 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (82151498811165329 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell768_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (12 / 25 : ℝ) (769 / 1600 : ℝ)) :
    (302705421 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (153791961 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell768_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell768_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell769_leftExp :
    (26149631351 / 10000000000 : ℝ) ≤ Real.exp (769 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (769 / 800 : ℝ) (1030494786869 / 1000000000000 : ℝ)
    (26149631351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell769_rightExp :
    Real.exp (77 / 80 : ℝ) ≤ (2618233883 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 80 : ℝ) (1030535041359 / 1000000000000 : ℝ)
    (2618233883 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell769_denomUpper :
    Real.exp (7985112739195619 / 1000000000000000 : ℝ) ≤ (29369083905453 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7985112739195619 / 1000000000000000 : ℝ) (1283428192457
    / 1000000000000 : ℝ) (29369083905453 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell769_denomLower :
    (29059692587059 / 10000000000 : ℝ) ≤ Real.exp (9968152831906349 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9968152831906349 / 1250000000000000 : ℝ) (64150175461 /
    50000000000 : ℝ) (29059692587059 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell769_product_lower :
    (10268934081906349 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (769 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell769_leftExp
    (by norm_num : (0 : ℝ) ≤ (26149631351 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell769_product_upper :
    Real.pi * Real.exp (77 / 80 : ℝ) ≤ (8225425239195619 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell769_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell769_endpointLower :
    (751346877 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (769 / 1600 : ℝ) (77 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10268934081906349 / 1250000000000000 : ℝ) (Real.pi * Real.exp (769 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell769_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 80 : ℝ) - (769 / 3200 : ℝ)) ≤
      (29369083905453 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell769_denomUpper
    linarith [hpThetaJensenCell769_product_upper]
  have hi : (1 / (29369083905453 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 80 : ℝ) - (769 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29369083905453 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29369083905453 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((769 / 3200 : ℝ) - Real.pi * Real.exp (77 / 80 : ℝ)) := by
    rw [show (769 / 3200 : ℝ) - Real.pi * Real.exp (77 / 80 : ℝ) =
      -(Real.pi * Real.exp (77 / 80 : ℝ) - (769 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (769 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (769 / 800 : ℝ)) := by
    have h := hpThetaJensenCell769_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29369083905453 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell769_endpointUpper :
    hpThetaJensenKernelEndpointUpper (769 / 1600 : ℝ) (77 / 160 : ℝ) ≤ (763465309 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 80 : ℝ)) (8225425239195619 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell769_product_upper
  have hD : (29059692587059 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (769 / 800 : ℝ) - (77 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell769_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell769_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (769 / 800 : ℝ) - (77 / 320 : ℝ)) ≤
      (1 / (29059692587059 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29059692587059 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 320 : ℝ) - Real.pi * Real.exp (769 / 800 : ℝ)) ≤
      (2 / (29059692587059 / 10000000000 : ℝ) : ℝ) := by
    rw [show (77 / 320 : ℝ) - Real.pi * Real.exp (769 / 800 : ℝ) =
      -(Real.pi * Real.exp (769 / 800 : ℝ) - (77 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8225425239195619 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (8225425239195619 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell769_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (769 / 1600 : ℝ) (77 / 160 : ℝ)) :
    (751346877 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (763465309 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell769_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell769_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell770_leftExp :
    (26182338829 / 10000000000 : ℝ) ≤ Real.exp (77 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 80 : ℝ) (515267520679 / 500000000000 : ℝ)
    (26182338829 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell770_rightExp :
    Real.exp (771 / 800 : ℝ) ≤ (13107543609 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (771 / 800 : ℝ) (1030575297421 / 1000000000000 : ℝ)
    (13107543609 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell770_denomUpper :
    Real.exp (39975442249229137 / 5000000000000000 : ℝ) ≤ (7415881897349 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39975442249229137 / 5000000000000000 : ℝ) (1283828351961
    / 1000000000000 : ℝ) (7415881897349 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell770_denomLower :
    (14675328553191 / 5000000000 : ℝ) ≤ Real.exp (9980606400809471 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9980606400809471 / 1250000000000000 : ℝ) (320850755181 /
    250000000000 : ℝ) (14675328553191 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell770_product_lower :
    (10281778275809471 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell770_leftExp
    (by norm_num : (0 : ℝ) ≤ (26182338829 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell770_product_upper :
    Real.pi * Real.exp (771 / 800 : ℝ) ≤ (41178567249229137 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell770_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell770_endpointLower :
    (372979533 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 160 : ℝ) (771 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10281778275809471 / 1250000000000000 : ℝ) (Real.pi * Real.exp (77 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell770_product_lower
  have hD : Real.exp (Real.pi * Real.exp (771 / 800 : ℝ) - (77 / 320 : ℝ)) ≤
      (7415881897349 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell770_denomUpper
    linarith [hpThetaJensenCell770_product_upper]
  have hi : (1 / (7415881897349 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (771 / 800 : ℝ) - (77 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7415881897349 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7415881897349 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 320 : ℝ) - Real.pi * Real.exp (771 / 800 : ℝ)) := by
    rw [show (77 / 320 : ℝ) - Real.pi * Real.exp (771 / 800 : ℝ) =
      -(Real.pi * Real.exp (771 / 800 : ℝ) - (77 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 80 : ℝ)) := by
    have h := hpThetaJensenCell770_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7415881897349 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell770_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 160 : ℝ) (771 / 1600 : ℝ) ≤ (1516000039 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (771 / 800 : ℝ)) (41178567249229137 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (771 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell770_product_upper
  have hD : (14675328553191 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 80 : ℝ) - (771 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell770_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell770_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 80 : ℝ) - (771 / 3200 : ℝ)) ≤
      (1 / (14675328553191 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14675328553191 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((771 / 3200 : ℝ) - Real.pi * Real.exp (77 / 80 : ℝ)) ≤
      (2 / (14675328553191 / 5000000000 : ℝ) : ℝ) := by
    rw [show (771 / 3200 : ℝ) - Real.pi * Real.exp (77 / 80 : ℝ) =
      -(Real.pi * Real.exp (77 / 80 : ℝ) - (771 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41178567249229137 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (41178567249229137 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell770_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 160 : ℝ) (771 / 1600 : ℝ)) :
    (372979533 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1516000039 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell770_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell770_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell771_leftExp :
    (1638442951 / 625000000 : ℝ) ≤ Real.exp (771 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (771 / 800 : ℝ) (51528764871 / 50000000000 : ℝ)
    (1638442951 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell771_rightExp :
    Real.exp (193 / 200 : ℝ) ≤ (5249575313 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (193 / 200 : ℝ) (515307777527 / 500000000000 : ℝ)
    (5249575313 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell771_denomUpper :
    Real.exp (16010154056293609 / 2000000000000000 : ℝ) ≤ (14980654393521 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16010154056293609 / 2000000000000000 : ℝ) (1284229152637
    / 1000000000000 : ℝ) (14980654393521 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell771_denomLower :
    (3705614492881 / 1250000000 : ℝ) ≤ Real.exp (624567252164749 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (624567252164749 / 78125000000000 : ℝ) (256760634447 /
    200000000000 : ℝ) (3705614492881 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell771_product_lower :
    (643414908414749 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (771 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell771_leftExp
    (by norm_num : (0 : ℝ) ≤ (1638442951 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell771_product_upper :
    Real.pi * Real.exp (193 / 200 : ℝ) ≤ (16492029056293609 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell771_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell771_endpointLower :
    (148120009 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (771 / 1600 : ℝ) (193 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (643414908414749 / 78125000000000 : ℝ) (Real.pi * Real.exp (771 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell771_product_lower
  have hD : Real.exp (Real.pi * Real.exp (193 / 200 : ℝ) - (771 / 3200 : ℝ)) ≤
      (14980654393521 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell771_denomUpper
    linarith [hpThetaJensenCell771_product_upper]
  have hi : (1 / (14980654393521 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (193 / 200 : ℝ) - (771 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14980654393521 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14980654393521 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((771 / 3200 : ℝ) - Real.pi * Real.exp (193 / 200 : ℝ)) := by
    rw [show (771 / 3200 : ℝ) - Real.pi * Real.exp (193 / 200 : ℝ) =
      -(Real.pi * Real.exp (193 / 200 : ℝ) - (771 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (771 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (771 / 800 : ℝ)) := by
    have h := hpThetaJensenCell771_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14980654393521 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell771_endpointUpper :
    hpThetaJensenKernelEndpointUpper (771 / 1600 : ℝ) (193 / 400 : ℝ) ≤ (1505127723 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (193 / 200 : ℝ)) (16492029056293609 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (193 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell771_product_upper
  have hD : (3705614492881 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (771 / 800 : ℝ) - (193 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell771_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell771_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (771 / 800 : ℝ) - (193 / 800 : ℝ)) ≤
      (1 / (3705614492881 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3705614492881 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((193 / 800 : ℝ) - Real.pi * Real.exp (771 / 800 : ℝ)) ≤
      (2 / (3705614492881 / 1250000000 : ℝ) : ℝ) := by
    rw [show (193 / 800 : ℝ) - Real.pi * Real.exp (771 / 800 : ℝ) =
      -(Real.pi * Real.exp (771 / 800 : ℝ) - (193 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16492029056293609 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (16492029056293609 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell771_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (771 / 1600 : ℝ) (193 / 400 : ℝ)) :
    (148120009 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1505127723 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell771_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell771_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell772_leftExp :
    (6561969141 / 2500000000 : ℝ) ≤ Real.exp (193 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (193 / 200 : ℝ) (1030615555053 / 1000000000000 : ℝ)
    (6561969141 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell772_rightExp :
    Real.exp (773 / 800 : ℝ) ≤ (13140353463 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (773 / 800 : ℝ) (1030655814261 / 1000000000000 : ℝ)
    (13140353463 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell772_denomUpper :
    Real.exp (40075392456886559 / 5000000000000000 : ℝ) ≤ (7565617306801 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40075392456886559 / 5000000000000000 : ℝ) (1284630595701
    / 1000000000000 : ℝ) (7565617306801 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell772_denomLower :
    (29942510216391 / 10000000000 : ℝ) ≤ Real.exp (2501390438451559 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2501390438451559 / 312500000000000 : ℝ) (1284203964931 /
    1000000000000 : ℝ) (29942510216391 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell772_product_lower :
    (2576878719701559 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (193 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell772_leftExp
    (by norm_num : (0 : ℝ) ≤ (6561969141 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell772_product_upper :
    Real.pi * Real.exp (773 / 800 : ℝ) ≤ (41281642456886559 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell772_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell772_endpointLower :
    (1470539473 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (193 / 400 : ℝ) (773 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2576878719701559 / 312500000000000 : ℝ) (Real.pi * Real.exp (193 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell772_product_lower
  have hD : Real.exp (Real.pi * Real.exp (773 / 800 : ℝ) - (193 / 800 : ℝ)) ≤
      (7565617306801 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell772_denomUpper
    linarith [hpThetaJensenCell772_product_upper]
  have hi : (1 / (7565617306801 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (773 / 800 : ℝ) - (193 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7565617306801 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7565617306801 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((193 / 800 : ℝ) - Real.pi * Real.exp (773 / 800 : ℝ)) := by
    rw [show (193 / 800 : ℝ) - Real.pi * Real.exp (773 / 800 : ℝ) =
      -(Real.pi * Real.exp (773 / 800 : ℝ) - (193 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (193 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (193 / 200 : ℝ)) := by
    have h := hpThetaJensenCell772_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7565617306801 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell772_endpointUpper :
    hpThetaJensenKernelEndpointUpper (193 / 400 : ℝ) (773 / 1600 : ℝ) ≤ (373578379 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (773 / 800 : ℝ)) (41281642456886559 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (773 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell772_product_upper
  have hD : (29942510216391 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (193 / 200 : ℝ) - (773 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell772_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell772_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (193 / 200 : ℝ) - (773 / 3200 : ℝ)) ≤
      (1 / (29942510216391 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29942510216391 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((773 / 3200 : ℝ) - Real.pi * Real.exp (193 / 200 : ℝ)) ≤
      (2 / (29942510216391 / 10000000000 : ℝ) : ℝ) := by
    rw [show (773 / 3200 : ℝ) - Real.pi * Real.exp (193 / 200 : ℝ) =
      -(Real.pi * Real.exp (193 / 200 : ℝ) - (773 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41281642456886559 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (41281642456886559 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell772_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (193 / 400 : ℝ) (773 / 1600 : ℝ)) :
    (1470539473 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (373578379 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell772_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell772_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell773_leftExp :
    (6570176731 / 2500000000 : ℝ) ≤ Real.exp (773 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (773 / 800 : ℝ) (51532790713 / 50000000000 : ℝ)
    (6570176731 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell773_rightExp :
    Real.exp (387 / 400 : ℝ) ≤ (526271567 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (387 / 400 : ℝ) (6441850469 / 6250000000 : ℝ)
    (526271567 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell773_denomUpper :
    Real.exp (1605018570986231 / 200000000000000 : ℝ) ≤ (15283525573903 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1605018570986231 / 200000000000000 : ℝ) (160629085287 /
    125000000000 : ℝ) (15283525573903 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell773_denomLower :
    (15121740795581 / 5000000000 : ℝ) ≤ Real.exp (2504515894586969 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2504515894586969 / 312500000000000 : ℝ) (1284605399977 /
    1000000000000 : ℝ) (15121740795581 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell773_product_lower :
    (2580101832086969 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (773 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell773_leftExp
    (by norm_num : (0 : ℝ) ≤ (6570176731 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell773_product_upper :
    Real.pi * Real.exp (387 / 400 : ℝ) ≤ (1653331070986231 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell773_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell773_endpointLower :
    (145993613 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (773 / 1600 : ℝ) (387 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2580101832086969 / 312500000000000 : ℝ) (Real.pi * Real.exp (773 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell773_product_lower
  have hD : Real.exp (Real.pi * Real.exp (387 / 400 : ℝ) - (773 / 3200 : ℝ)) ≤
      (15283525573903 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell773_denomUpper
    linarith [hpThetaJensenCell773_product_upper]
  have hi : (1 / (15283525573903 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (387 / 400 : ℝ) - (773 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15283525573903 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15283525573903 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((773 / 3200 : ℝ) - Real.pi * Real.exp (387 / 400 : ℝ)) := by
    rw [show (773 / 3200 : ℝ) - Real.pi * Real.exp (387 / 400 : ℝ) =
      -(Real.pi * Real.exp (387 / 400 : ℝ) - (773 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (773 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (773 / 800 : ℝ)) := by
    have h := hpThetaJensenCell773_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15283525573903 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell773_endpointUpper :
    hpThetaJensenKernelEndpointUpper (773 / 1600 : ℝ) (387 / 800 : ℝ) ≤ (92722329 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (387 / 400 : ℝ)) (1653331070986231 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (387 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell773_product_upper
  have hD : (15121740795581 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (773 / 800 : ℝ) - (387 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell773_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell773_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (773 / 800 : ℝ) - (387 / 1600 : ℝ)) ≤
      (1 / (15121740795581 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15121740795581 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((387 / 1600 : ℝ) - Real.pi * Real.exp (773 / 800 : ℝ)) ≤
      (2 / (15121740795581 / 5000000000 : ℝ) : ℝ) := by
    rw [show (387 / 1600 : ℝ) - Real.pi * Real.exp (773 / 800 : ℝ) =
      -(Real.pi * Real.exp (773 / 800 : ℝ) - (387 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1653331070986231 / 200000000000000 : ℝ) ^ 2 - 6 *
      (1653331070986231 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell773_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (773 / 1600 : ℝ) (387 / 800 : ℝ)) :
    (145993613 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (92722329 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell773_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell773_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell774_leftExp :
    (6578394587 / 2500000000 : ℝ) ≤ Real.exp (387 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (387 / 400 : ℝ) (1030696075039 / 1000000000000 : ℝ)
    (6578394587 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell774_rightExp :
    Real.exp (31 / 32 : ℝ) ≤ (26346490889 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 32 : ℝ) (64421021087 / 62500000000 : ℝ)
    (26346490889 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell774_denomUpper :
    Real.exp (80351201351446177 / 10000000000000000 : ℝ) ≤ (30875097386649 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (80351201351446177 / 10000000000000000 : ℝ)
    (1285435413603 / 1000000000000 : ℝ) (30875097386649 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell774_denomLower :
    (15273936153559 / 5000000000 : ℝ) ≤ Real.exp (2507645382170313 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2507645382170313 / 312500000000000 : ℝ) (642503739277 /
    500000000000 : ℝ) (15273936153559 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell774_product_lower :
    (2583328975920313 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (387 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell774_leftExp
    (by norm_num : (0 : ℝ) ≤ (6578394587 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell774_product_upper :
    Real.pi * Real.exp (31 / 32 : ℝ) ≤ (82769951351446177 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell774_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell774_endpointLower :
    (724694953 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (387 / 800 : ℝ) (31 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2583328975920313 / 312500000000000 : ℝ) (Real.pi * Real.exp (387 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell774_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 32 : ℝ) - (387 / 1600 : ℝ)) ≤
      (30875097386649 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell774_denomUpper
    linarith [hpThetaJensenCell774_product_upper]
  have hi : (1 / (30875097386649 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 32 : ℝ) - (387 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (30875097386649 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (30875097386649 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((387 / 1600 : ℝ) - Real.pi * Real.exp (31 / 32 : ℝ)) := by
    rw [show (387 / 1600 : ℝ) - Real.pi * Real.exp (31 / 32 : ℝ) =
      -(Real.pi * Real.exp (31 / 32 : ℝ) - (387 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (387 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (387 / 400 : ℝ)) := by
    have h := hpThetaJensenCell774_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (30875097386649 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell774_endpointUpper :
    hpThetaJensenKernelEndpointUpper (387 / 800 : ℝ) (31 / 64 : ℝ) ≤ (1472858813 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 32 : ℝ)) (82769951351446177 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell774_product_upper
  have hD : (15273936153559 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (387 / 400 : ℝ) - (31 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell774_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell774_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (387 / 400 : ℝ) - (31 / 128 : ℝ)) ≤
      (1 / (15273936153559 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15273936153559 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 128 : ℝ) - Real.pi * Real.exp (387 / 400 : ℝ)) ≤
      (2 / (15273936153559 / 5000000000 : ℝ) : ℝ) := by
    rw [show (31 / 128 : ℝ) - Real.pi * Real.exp (387 / 400 : ℝ) =
      -(Real.pi * Real.exp (387 / 400 : ℝ) - (31 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (82769951351446177 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (82769951351446177 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell774_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (387 / 800 : ℝ) (31 / 64 : ℝ)) :
    (724694953 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1472858813 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell774_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell774_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell775_leftExp :
    (26346490887 / 10000000000 : ℝ) ≤ Real.exp (31 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 32 : ℝ) (1030736337391 / 1000000000000 : ℝ)
    (26346490887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell775_rightExp :
    Real.exp (97 / 100 : ℝ) ≤ (13189722297 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97 / 100 : ℝ) (257694150329 / 250000000000 : ℝ)
    (13189722297 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell775_denomUpper :
    Real.exp (40225801740199121 / 5000000000000000 : ℝ) ≤ (15593325677297 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40225801740199121 / 5000000000000000 : ℝ) (642919395397
    / 500000000000 : ℝ) (15593325677297 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell775_denomLower :
    (15427862582731 / 5000000000 : ℝ) ≤ Real.exp (10043115624834013 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10043115624834013 / 1250000000000000 : ℝ) (128541020183
    / 100000000000 : ℝ) (15427862582731 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell775_product_lower :
    (10346240624834013 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell775_leftExp
    (by norm_num : (0 : ℝ) ≤ (26346490887 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell775_product_upper :
    Real.pi * Real.exp (97 / 100 : ℝ) ≤ (41436739240199121 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell775_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell775_endpointLower :
    (1438900649 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 64 : ℝ) (97 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10346240624834013 / 1250000000000000 : ℝ) (Real.pi * Real.exp (31 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell775_product_lower
  have hD : Real.exp (Real.pi * Real.exp (97 / 100 : ℝ) - (31 / 128 : ℝ)) ≤
      (15593325677297 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell775_denomUpper
    linarith [hpThetaJensenCell775_product_upper]
  have hi : (1 / (15593325677297 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (97 / 100 : ℝ) - (31 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15593325677297 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15593325677297 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 128 : ℝ) - Real.pi * Real.exp (97 / 100 : ℝ)) := by
    rw [show (31 / 128 : ℝ) - Real.pi * Real.exp (97 / 100 : ℝ) =
      -(Real.pi * Real.exp (97 / 100 : ℝ) - (31 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 32 : ℝ)) := by
    have h := hpThetaJensenCell775_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15593325677297 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell775_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 64 : ℝ) (97 / 200 : ℝ) ≤ (182777251 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (97 / 100 : ℝ)) (41436739240199121 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (97 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell775_product_upper
  have hD : (15427862582731 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 32 : ℝ) - (97 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell775_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell775_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 32 : ℝ) - (97 / 400 : ℝ)) ≤
      (1 / (15427862582731 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15427862582731 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((97 / 400 : ℝ) - Real.pi * Real.exp (31 / 32 : ℝ)) ≤
      (2 / (15427862582731 / 5000000000 : ℝ) : ℝ) := by
    rw [show (97 / 400 : ℝ) - Real.pi * Real.exp (31 / 32 : ℝ) =
      -(Real.pi * Real.exp (31 / 32 : ℝ) - (97 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41436739240199121 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (41436739240199121 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell775_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 64 : ℝ) (97 / 200 : ℝ)) :
    (1438900649 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (182777251 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell775_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell775_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell776_leftExp :
    (1648715287 / 625000000 : ℝ) ≤ Real.exp (97 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (97 / 100 : ℝ) (206155320263 / 200000000000 : ℝ)
    (1648715287 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell776_rightExp :
    Real.exp (777 / 800 : ℝ) ≤ (13206219759 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (777 / 800 : ℝ) (515408433407 / 500000000000 : ℝ)
    (13206219759 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell776_denomUpper :
    Real.exp (40276067551336087 / 5000000000000000 : ℝ) ≤ (31501757070253 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40276067551336087 / 5000000000000000 : ℝ) (643121407533
    / 500000000000 : ℝ) (31501757070253 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell776_denomLower :
    (6233416709959 / 2000000000 : ℝ) ≤ Real.exp (628479117927113 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (628479117927113 / 78125000000000 : ℝ) (1285813570977 /
    1000000000000 : ℝ) (6233416709959 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell776_product_lower :
    (647448844489613 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (97 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell776_leftExp
    (by norm_num : (0 : ℝ) ≤ (1648715287 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell776_product_upper :
    Real.pi * Real.exp (777 / 800 : ℝ) ≤ (41488567551336087 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell776_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell776_endpointLower :
    (7142341 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 200 : ℝ) (777 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (647448844489613 / 78125000000000 : ℝ) (Real.pi * Real.exp (97 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell776_product_lower
  have hD : Real.exp (Real.pi * Real.exp (777 / 800 : ℝ) - (97 / 400 : ℝ)) ≤
      (31501757070253 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell776_denomUpper
    linarith [hpThetaJensenCell776_product_upper]
  have hi : (1 / (31501757070253 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (777 / 800 : ℝ) - (97 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31501757070253 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31501757070253 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((97 / 400 : ℝ) - Real.pi * Real.exp (777 / 800 : ℝ)) := by
    rw [show (97 / 400 : ℝ) - Real.pi * Real.exp (777 / 800 : ℝ) =
      -(Real.pi * Real.exp (777 / 800 : ℝ) - (97 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (97 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (97 / 100 : ℝ)) := by
    have h := hpThetaJensenCell776_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31501757070253 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell776_endpointUpper :
    hpThetaJensenKernelEndpointUpper (97 / 200 : ℝ) (777 / 1600 : ℝ) ≤ (362908673 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (777 / 800 : ℝ)) (41488567551336087 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (777 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell776_product_upper
  have hD : (6233416709959 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (97 / 100 : ℝ) - (777 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell776_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell776_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (97 / 100 : ℝ) - (777 / 3200 : ℝ)) ≤
      (1 / (6233416709959 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6233416709959 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((777 / 3200 : ℝ) - Real.pi * Real.exp (97 / 100 : ℝ)) ≤
      (2 / (6233416709959 / 2000000000 : ℝ) : ℝ) := by
    rw [show (777 / 3200 : ℝ) - Real.pi * Real.exp (97 / 100 : ℝ) =
      -(Real.pi * Real.exp (97 / 100 : ℝ) - (777 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41488567551336087 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (41488567551336087 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell776_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (97 / 200 : ℝ) (777 / 1600 : ℝ)) :
    (7142341 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (362908673 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell776_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell776_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell777_leftExp :
    (6603109879 / 2500000000 : ℝ) ≤ Real.exp (777 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (777 / 800 : ℝ) (1030816866813 / 1000000000000 : ℝ)
    (6603109879 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell777_rightExp :
    Real.exp (389 / 400 : ℝ) ≤ (2644547571 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (389 / 400 : ℝ) (257714283471 / 250000000000 : ℝ)
    (2644547571 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell777_denomUpper :
    Real.exp (8065279637220603 / 1000000000000000 : ℝ) ≤ (31820459113271 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8065279637220603 / 1000000000000000 : ℝ) (128664748757 /
    100000000000 : ℝ) (31820459113271 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell777_denomLower :
    (31481991451087 / 10000000000 : ℝ) ≤ Real.exp (2517058083873421 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2517058083873421 / 312500000000000 : ℝ) (160777198399 /
    125000000000 : ℝ) (31481991451087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell777_product_lower :
    (2593034646373421 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (777 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell777_leftExp
    (by norm_num : (0 : ℝ) ≤ (6603109879 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell777_product_upper :
    Real.pi * Real.exp (389 / 400 : ℝ) ≤ (8308092137220603 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell777_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell777_endpointLower :
    (1418092407 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (777 / 1600 : ℝ) (389 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2593034646373421 / 312500000000000 : ℝ) (Real.pi * Real.exp (777 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell777_product_lower
  have hD : Real.exp (Real.pi * Real.exp (389 / 400 : ℝ) - (777 / 3200 : ℝ)) ≤
      (31820459113271 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell777_denomUpper
    linarith [hpThetaJensenCell777_product_upper]
  have hi : (1 / (31820459113271 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (389 / 400 : ℝ) - (777 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31820459113271 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31820459113271 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((777 / 3200 : ℝ) - Real.pi * Real.exp (389 / 400 : ℝ)) := by
    rw [show (777 / 3200 : ℝ) - Real.pi * Real.exp (389 / 400 : ℝ) =
      -(Real.pi * Real.exp (389 / 400 : ℝ) - (777 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (777 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (777 / 800 : ℝ)) := by
    have h := hpThetaJensenCell777_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31820459113271 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell777_endpointUpper :
    hpThetaJensenKernelEndpointUpper (777 / 1600 : ℝ) (389 / 800 : ℝ) ≤ (1441108709 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (389 / 400 : ℝ)) (8308092137220603 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (389 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell777_product_upper
  have hD : (31481991451087 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (777 / 800 : ℝ) - (389 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell777_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell777_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (777 / 800 : ℝ) - (389 / 1600 : ℝ)) ≤
      (1 / (31481991451087 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31481991451087 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((389 / 1600 : ℝ) - Real.pi * Real.exp (777 / 800 : ℝ)) ≤
      (2 / (31481991451087 / 10000000000 : ℝ) : ℝ) := by
    rw [show (389 / 1600 : ℝ) - Real.pi * Real.exp (777 / 800 : ℝ) =
      -(Real.pi * Real.exp (777 / 800 : ℝ) - (389 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8308092137220603 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (8308092137220603 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell777_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (777 / 1600 : ℝ) (389 / 800 : ℝ)) :
    (1418092407 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1441108709 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell777_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell777_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell778_leftExp :
    (26445475709 / 10000000000 : ℝ) ≤ Real.exp (389 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (389 / 400 : ℝ) (1030857133883 / 1000000000000 : ℝ)
    (26445475709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell778_rightExp :
    Real.exp (779 / 800 : ℝ) ≤ (3309819153 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (779 / 800 : ℝ) (1030897402527 / 1000000000000 : ℝ)
    (3309819153 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell778_denomUpper :
    Real.exp (10094198432330729 / 1250000000000000 : ℝ) ≤ (1004462584897 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10094198432330729 / 1250000000000000 : ℝ) (643526404759
    / 500000000000 : ℝ) (1004462584897 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell778_denomLower :
    (397506167881 / 125000000 : ℝ) ≤ Real.exp (10080814990448591 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10080814990448591 / 1250000000000000 : ℝ) (643311125819
    / 500000000000 : ℝ) (397506167881 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell778_product_lower :
    (10385111865448591 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (389 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell778_leftExp
    (by norm_num : (0 : ℝ) ≤ (26445475709 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell778_product_upper :
    Real.pi * Real.exp (779 / 800 : ℝ) ≤ (10398104682330729 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell778_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell778_endpointLower :
    (175971639 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (389 / 800 : ℝ) (779 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10385111865448591 / 1250000000000000 : ℝ) (Real.pi * Real.exp (389 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell778_product_lower
  have hD : Real.exp (Real.pi * Real.exp (779 / 800 : ℝ) - (389 / 1600 : ℝ)) ≤
      (1004462584897 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell778_denomUpper
    linarith [hpThetaJensenCell778_product_upper]
  have hi : (1 / (1004462584897 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (779 / 800 : ℝ) - (389 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1004462584897 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1004462584897 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((389 / 1600 : ℝ) - Real.pi * Real.exp (779 / 800 : ℝ)) := by
    rw [show (389 / 1600 : ℝ) - Real.pi * Real.exp (779 / 800 : ℝ) =
      -(Real.pi * Real.exp (779 / 800 : ℝ) - (389 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (389 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (389 / 400 : ℝ)) := by
    have h := hpThetaJensenCell778_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1004462584897 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell778_endpointUpper :
    hpThetaJensenKernelEndpointUpper (389 / 800 : ℝ) (779 / 1600 : ℝ) ≤ (715319951 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (779 / 800 : ℝ)) (10398104682330729 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (779 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell778_product_upper
  have hD : (397506167881 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (389 / 400 : ℝ) - (779 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell778_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell778_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (389 / 400 : ℝ) - (779 / 3200 : ℝ)) ≤
      (1 / (397506167881 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (397506167881 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((779 / 3200 : ℝ) - Real.pi * Real.exp (389 / 400 : ℝ)) ≤
      (2 / (397506167881 / 125000000 : ℝ) : ℝ) := by
    rw [show (779 / 3200 : ℝ) - Real.pi * Real.exp (389 / 400 : ℝ) =
      -(Real.pi * Real.exp (389 / 400 : ℝ) - (779 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10398104682330729 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (10398104682330729 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell778_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (389 / 800 : ℝ) (779 / 1600 : ℝ)) :
    (175971639 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (715319951 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell778_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell778_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell779_leftExp :
    (13239276611 / 5000000000 : ℝ) ≤ Real.exp (779 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (779 / 800 : ℝ) (515448701263 / 500000000000 : ℝ)
    (13239276611 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell779_rightExp :
    Real.exp (39 / 40 : ℝ) ≤ (26511672111 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 40 : ℝ) (128867209093 / 125000000000 : ℝ)
    (26511672111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell779_denomUpper :
    Real.exp (80854508522212823 / 10000000000000000 : ℝ) ≤ (8117208425781 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (80854508522212823 / 10000000000000000 : ℝ) (128745878209
    / 100000000000 : ℝ) (8117208425781 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell779_denomLower :
    (8030658666039 / 2500000000 : ℝ) ≤ Real.exp (5046706935863089 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5046706935863089 / 625000000000000 : ℝ) (1287027565491 /
    1000000000000 : ℝ) (8030658666039 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell779_product_lower :
    (5199050685863089 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (779 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell779_leftExp
    (by norm_num : (0 : ℝ) ≤ (13239276611 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell779_product_upper :
    Real.pi * Real.exp (39 / 40 : ℝ) ≤ (83288883522212823 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell779_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell779_endpointLower :
    (1397510157 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (779 / 1600 : ℝ) (39 / 80 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5199050685863089 / 625000000000000 : ℝ) (Real.pi * Real.exp (779 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell779_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 40 : ℝ) - (779 / 3200 : ℝ)) ≤
      (8117208425781 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell779_denomUpper
    linarith [hpThetaJensenCell779_product_upper]
  have hi : (1 / (8117208425781 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 40 : ℝ) - (779 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8117208425781 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8117208425781 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((779 / 3200 : ℝ) - Real.pi * Real.exp (39 / 40 : ℝ)) := by
    rw [show (779 / 3200 : ℝ) - Real.pi * Real.exp (39 / 40 : ℝ) =
      -(Real.pi * Real.exp (39 / 40 : ℝ) - (779 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (779 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (779 / 800 : ℝ)) := by
    have h := hpThetaJensenCell779_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8117208425781 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell779_endpointUpper :
    hpThetaJensenKernelEndpointUpper (779 / 1600 : ℝ) (39 / 80 : ℝ) ≤ (88764257 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 40 : ℝ)) (83288883522212823 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell779_product_upper
  have hD : (8030658666039 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (779 / 800 : ℝ) - (39 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell779_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell779_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (779 / 800 : ℝ) - (39 / 160 : ℝ)) ≤
      (1 / (8030658666039 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8030658666039 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 160 : ℝ) - Real.pi * Real.exp (779 / 800 : ℝ)) ≤
      (2 / (8030658666039 / 2500000000 : ℝ) : ℝ) := by
    rw [show (39 / 160 : ℝ) - Real.pi * Real.exp (779 / 800 : ℝ) =
      -(Real.pi * Real.exp (779 / 800 : ℝ) - (39 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (83288883522212823 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (83288883522212823 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell779_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (779 / 1600 : ℝ) (39 / 80 : ℝ)) :
    (1397510157 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (88764257 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell779_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell779_endpointUpper

def hpThetaJensenCellsBatch038Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (100143133 / 625000000 : ℝ)
  | 1 => (795494787 / 5000000000 : ℝ)
  | 2 => (789873967 / 5000000000 : ℝ)
  | 3 => (196070633 / 1250000000 : ℝ)
  | 4 => (97340051 / 625000000 : ℝ)
  | 5 => (386593761 / 2500000000 : ℝ)
  | 6 => (1535367601 / 10000000000 : ℝ)
  | 7 => (762209169 / 5000000000 : ℝ)
  | 8 => (302705421 / 2000000000 : ℝ)
  | 9 => (751346877 / 5000000000 : ℝ)
  | 10 => (372979533 / 2500000000 : ℝ)
  | 11 => (148120009 / 1000000000 : ℝ)
  | 12 => (1470539473 / 10000000000 : ℝ)
  | 13 => (145993613 / 1000000000 : ℝ)
  | 14 => (724694953 / 5000000000 : ℝ)
  | 15 => (1438900649 / 10000000000 : ℝ)
  | 16 => (7142341 / 50000000 : ℝ)
  | 17 => (1418092407 / 10000000000 : ℝ)
  | 18 => (175971639 / 1250000000 : ℝ)
  | 19 => (1397510157 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch038Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (203494061 / 1250000000 : ℝ)
  | 1 => (202061349 / 1250000000 : ℝ)
  | 2 => (16050887 / 100000000 : ℝ)
  | 3 => (796873033 / 5000000000 : ℝ)
  | 4 => (197807843 / 1250000000 : ℝ)
  | 5 => (785619293 / 5000000000 : ℝ)
  | 6 => (390018361 / 2500000000 : ℝ)
  | 7 => (1548967169 / 10000000000 : ℝ)
  | 8 => (153791961 / 1000000000 : ℝ)
  | 9 => (763465309 / 5000000000 : ℝ)
  | 10 => (1516000039 / 10000000000 : ℝ)
  | 11 => (1505127723 / 10000000000 : ℝ)
  | 12 => (373578379 / 2500000000 : ℝ)
  | 13 => (92722329 / 625000000 : ℝ)
  | 14 => (1472858813 / 10000000000 : ℝ)
  | 15 => (182777251 / 1250000000 : ℝ)
  | 16 => (362908673 / 2500000000 : ℝ)
  | 17 => (1441108709 / 10000000000 : ℝ)
  | 18 => (715319951 / 5000000000 : ℝ)
  | 19 => (88764257 / 625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch038_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch038Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch038Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell760_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell761_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell762_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell763_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell764_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell765_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell766_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell767_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell768_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell769_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell770_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell771_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell772_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell773_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell774_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell775_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell776_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell777_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell778_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell779_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper] at h ⊢
    exact h

end HodgeProofHP
