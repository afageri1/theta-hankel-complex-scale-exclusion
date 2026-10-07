import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell60_leftExp :
    (2694710377 / 2500000000 : ℝ) ≤ Real.exp (3 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 40 : ℝ) (1002346498729 / 1000000000000 : ℝ)
    (2694710377 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell60_rightExp :
    Real.exp (61 / 800 : ℝ) ≤ (5396161743 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 800 : ℝ) (501192826827 / 500000000000 : ℝ)
    (5396161743 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell60_denomUpper :
    Real.exp (16858793958676599 / 5000000000000000 : ℝ) ≤ (291297151327 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16858793958676599 / 5000000000000000 : ℝ) (222223765913
    / 200000000000 : ℝ) (291297151327 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell60_denomLower :
    (144987515323 / 5000000000 : ℝ) ≤ Real.exp (1052253039087523 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1052253039087523 / 312500000000000 : ℝ) (111096088599 /
    100000000000 : ℝ) (144987515323 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell60_product_lower :
    (1058210070337523 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell60_leftExp
    (by norm_num : (0 : ℝ) ≤ (2694710377 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell60_product_upper :
    Real.pi * Real.exp (61 / 800 : ℝ) ≤ (16952543958676599 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell60_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell60_endpointLower :
    (17542035589 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 80 : ℝ) (61 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1058210070337523 / 312500000000000 : ℝ) (Real.pi * Real.exp (3 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell60_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 800 : ℝ) - (3 / 160 : ℝ)) ≤
      (291297151327 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell60_denomUpper
    linarith [hpThetaJensenCell60_product_upper]
  have hi : (1 / (291297151327 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 800 : ℝ) - (3 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (291297151327 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (291297151327 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 160 : ℝ) - Real.pi * Real.exp (61 / 800 : ℝ)) := by
    rw [show (3 / 160 : ℝ) - Real.pi * Real.exp (61 / 800 : ℝ) =
      -(Real.pi * Real.exp (61 / 800 : ℝ) - (3 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 40 : ℝ)) := by
    have h := hpThetaJensenCell60_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (291297151327 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell60_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 80 : ℝ) (61 / 1600 : ℝ) ≤ (17730263239 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 800 : ℝ)) (16952543958676599 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell60_product_upper
  have hD : (144987515323 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 40 : ℝ) - (61 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell60_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell60_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 40 : ℝ) - (61 / 3200 : ℝ)) ≤
      (1 / (144987515323 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (144987515323 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 3200 : ℝ) - Real.pi * Real.exp (3 / 40 : ℝ)) ≤
      (2 / (144987515323 / 5000000000 : ℝ) : ℝ) := by
    rw [show (61 / 3200 : ℝ) - Real.pi * Real.exp (3 / 40 : ℝ) =
      -(Real.pi * Real.exp (3 / 40 : ℝ) - (61 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16952543958676599 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (16952543958676599 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell60_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 80 : ℝ) (61 / 1600 : ℝ)) :
    (17542035589 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17730263239 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell60_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell60_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell61_leftExp :
    (2698080871 / 2500000000 : ℝ) ≤ Real.exp (61 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 800 : ℝ) (1002385653653 / 1000000000000 : ℝ)
    (2698080871 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell61_rightExp :
    Real.exp (31 / 400 : ℝ) ≤ (432232893 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 400 : ℝ) (1002424810109 / 1000000000000 : ℝ)
    (432232893 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell61_denomUpper :
    Real.exp (1350274831018549 / 400000000000000 : ℝ) ≤ (146221850153 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1350274831018549 / 400000000000000 : ℝ) (555627618849 /
    500000000000 : ℝ) (146221850153 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell61_denomLower :
    (1819467707 / 62500000 : ℝ) ≤ Real.exp (1053478972460829 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1053478972460829 / 312500000000000 : ℝ) (555548545371 /
    500000000000 : ℝ) (1819467707 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell61_product_lower :
    (1059533659960829 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell61_leftExp
    (by norm_num : (0 : ℝ) ≤ (2698080871 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell61_product_upper :
    Real.pi * Real.exp (31 / 400 : ℝ) ≤ (1357899831018549 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell61_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell61_endpointLower :
    (17534399871 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 1600 : ℝ) (31 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1059533659960829 / 312500000000000 : ℝ) (Real.pi * Real.exp (61 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell61_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 400 : ℝ) - (61 / 3200 : ℝ)) ≤
      (146221850153 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell61_denomUpper
    linarith [hpThetaJensenCell61_product_upper]
  have hi : (1 / (146221850153 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 400 : ℝ) - (61 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (146221850153 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (146221850153 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 3200 : ℝ) - Real.pi * Real.exp (31 / 400 : ℝ)) := by
    rw [show (61 / 3200 : ℝ) - Real.pi * Real.exp (31 / 400 : ℝ) =
      -(Real.pi * Real.exp (31 / 400 : ℝ) - (61 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 800 : ℝ)) := by
    have h := hpThetaJensenCell61_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (146221850153 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell61_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 1600 : ℝ) (31 / 800 : ℝ) ≤ (17722600087 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 400 : ℝ)) (1357899831018549 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell61_product_upper
  have hD : (1819467707 / 62500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 800 : ℝ) - (31 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell61_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell61_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 800 : ℝ) - (31 / 1600 : ℝ)) ≤
      (1 / (1819467707 / 62500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1819467707 / 62500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 1600 : ℝ) - Real.pi * Real.exp (61 / 800 : ℝ)) ≤
      (2 / (1819467707 / 62500000 : ℝ) : ℝ) := by
    rw [show (31 / 1600 : ℝ) - Real.pi * Real.exp (61 / 800 : ℝ) =
      -(Real.pi * Real.exp (61 / 800 : ℝ) - (31 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1357899831018549 / 400000000000000 : ℝ) ^ 2 - 6 *
      (1357899831018549 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell61_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 1600 : ℝ) (31 / 800 : ℝ)) :
    (17534399871 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17722600087 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell61_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell61_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell62_leftExp :
    (2701455581 / 2500000000 : ℝ) ≤ Real.exp (31 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 400 : ℝ) (250606202527 / 250000000000 : ℝ)
    (2701455581 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell62_rightExp :
    Real.exp (63 / 800 : ℝ) ≤ (10819338049 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 800 : ℝ) (1002463968093 / 1000000000000 : ℝ)
    (10819338049 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell62_denomUpper :
    Real.exp (33796206679372057 / 10000000000000000 : ℝ) ≤ (293596319511 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33796206679372057 / 10000000000000000 : ℝ) (111139184681
    / 100000000000 : ℝ) (293596319511 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell62_denomLower :
    (73065166047 / 2500000000 : ℝ) ≤ Real.exp (1054706561453119 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1054706561453119 / 312500000000000 : ℝ) (111123349617 /
    100000000000 : ℝ) (73065166047 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell62_product_lower :
    (1060858905203119 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell62_leftExp
    (by norm_num : (0 : ℝ) ≤ (2701455581 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell62_product_upper :
    Real.pi * Real.exp (63 / 800 : ℝ) ≤ (33989956679372057 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell62_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell62_endpointLower :
    (17526635541 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 800 : ℝ) (63 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1060858905203119 / 312500000000000 : ℝ) (Real.pi * Real.exp (31 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell62_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 800 : ℝ) - (31 / 1600 : ℝ)) ≤
      (293596319511 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell62_denomUpper
    linarith [hpThetaJensenCell62_product_upper]
  have hi : (1 / (293596319511 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 800 : ℝ) - (31 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (293596319511 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (293596319511 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 1600 : ℝ) - Real.pi * Real.exp (63 / 800 : ℝ)) := by
    rw [show (31 / 1600 : ℝ) - Real.pi * Real.exp (63 / 800 : ℝ) =
      -(Real.pi * Real.exp (63 / 800 : ℝ) - (31 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 400 : ℝ)) := by
    have h := hpThetaJensenCell62_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (293596319511 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell62_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 800 : ℝ) (63 / 1600 : ℝ) ≤ (8857403569 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 800 : ℝ)) (33989956679372057 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell62_product_upper
  have hD : (73065166047 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 400 : ℝ) - (63 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell62_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell62_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 400 : ℝ) - (63 / 3200 : ℝ)) ≤
      (1 / (73065166047 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (73065166047 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 3200 : ℝ) - Real.pi * Real.exp (31 / 400 : ℝ)) ≤
      (2 / (73065166047 / 2500000000 : ℝ) : ℝ) := by
    rw [show (63 / 3200 : ℝ) - Real.pi * Real.exp (31 / 400 : ℝ) =
      -(Real.pi * Real.exp (31 / 400 : ℝ) - (63 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33989956679372057 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (33989956679372057 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell62_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 800 : ℝ) (63 / 1600 : ℝ)) :
    (17526635541 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8857403569 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell62_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell62_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell63_leftExp :
    (10819338047 / 10000000000 : ℝ) ≤ Real.exp (63 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 800 : ℝ) (250615992023 / 250000000000 : ℝ)
    (10819338047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell63_rightExp :
    Real.exp (2 / 25 : ℝ) ≤ (10832870677 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2 / 25 : ℝ) (501251563803 / 500000000000 : ℝ)
    (10832870677 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell63_denomUpper :
    Real.exp (33835595688768461 / 10000000000000000 : ℝ) ≤ (73688761723 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33835595688768461 / 10000000000000000 : ℝ) (55576432859
    / 50000000000 : ℝ) (73688761723 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell63_denomLower :
    (146706280751 / 5000000000 : ℝ) ≤ Real.exp (4223743231718853 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4223743231718853 / 1250000000000000 : ℝ) (138921262819 /
    125000000000 : ℝ) (146706280751 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell63_product_lower :
    (4248743231718853 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (63 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell63_leftExp
    (by norm_num : (0 : ℝ) ≤ (10819338047 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell63_product_upper :
    Real.pi * Real.exp (2 / 25 : ℝ) ≤ (34032470688768461 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell63_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell63_endpointLower :
    (17518742783 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 1600 : ℝ) (1 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4248743231718853 / 1250000000000000 : ℝ) (Real.pi * Real.exp (63 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell63_product_lower
  have hD : Real.exp (Real.pi * Real.exp (2 / 25 : ℝ) - (63 / 3200 : ℝ)) ≤
      (73688761723 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell63_denomUpper
    linarith [hpThetaJensenCell63_product_upper]
  have hi : (1 / (73688761723 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (2 / 25 : ℝ) - (63 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (73688761723 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (73688761723 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 3200 : ℝ) - Real.pi * Real.exp (2 / 25 : ℝ)) := by
    rw [show (63 / 3200 : ℝ) - Real.pi * Real.exp (2 / 25 : ℝ) =
      -(Real.pi * Real.exp (2 / 25 : ℝ) - (63 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 800 : ℝ)) := by
    have h := hpThetaJensenCell63_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (73688761723 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell63_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 1600 : ℝ) (1 / 25 : ℝ) ≤ (553340143 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (2 / 25 : ℝ)) (34032470688768461 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell63_product_upper
  have hD : (146706280751 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 800 : ℝ) - (1 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell63_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell63_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 800 : ℝ) - (1 / 50 : ℝ)) ≤
      (1 / (146706280751 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (146706280751 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 50 : ℝ) - Real.pi * Real.exp (63 / 800 : ℝ)) ≤
      (2 / (146706280751 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1 / 50 : ℝ) - Real.pi * Real.exp (63 / 800 : ℝ) =
      -(Real.pi * Real.exp (63 / 800 : ℝ) - (1 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34032470688768461 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (34032470688768461 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell63_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 1600 : ℝ) (1 / 25 : ℝ)) :
    (17518742783 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (553340143 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell63_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell63_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell64_leftExp :
    (2708217669 / 2500000000 : ℝ) ≤ Real.exp (2 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2 / 25 : ℝ) (200500625521 / 200000000000 : ℝ)
    (2708217669 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell64_rightExp :
    Real.exp (13 / 160 : ℝ) ≤ (10846420233 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 160 : ℝ) (20050845773 / 20000000000 : ℝ)
    (10846420233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell64_denomUpper :
    Real.exp (33875037879051169 / 10000000000000000 : ℝ) ≤ (73979980277 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33875037879051169 / 10000000000000000 : ℝ)
    (1111665669139 / 1000000000000 : ℝ) (73979980277 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell64_denomLower :
    (147285281667 / 5000000000 : ℝ) ≤ Real.exp (1057166714148631 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1057166714148631 / 312500000000000 : ℝ) (1085455967 /
    976562500 : ℝ) (147285281667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell64_product_lower :
    (1063514370398631 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (2 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell64_leftExp
    (by norm_num : (0 : ℝ) ≤ (2708217669 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell64_product_upper :
    Real.pi * Real.exp (13 / 160 : ℝ) ≤ (34075037879051169 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell64_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell64_endpointLower :
    (1094420111 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 25 : ℝ) (13 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1063514370398631 / 312500000000000 : ℝ) (Real.pi * Real.exp (2 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell64_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 160 : ℝ) - (1 / 50 : ℝ)) ≤
      (73979980277 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell64_denomUpper
    linarith [hpThetaJensenCell64_product_upper]
  have hi : (1 / (73979980277 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 160 : ℝ) - (1 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (73979980277 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (73979980277 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 50 : ℝ) - Real.pi * Real.exp (13 / 160 : ℝ)) := by
    rw [show (1 / 50 : ℝ) - Real.pi * Real.exp (13 / 160 : ℝ) =
      -(Real.pi * Real.exp (13 / 160 : ℝ) - (1 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (2 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (2 / 25 : ℝ)) := by
    have h := hpThetaJensenCell64_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (73979980277 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell64_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 25 : ℝ) (13 / 320 : ℝ) ≤ (17698832591 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 160 : ℝ)) (34075037879051169 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell64_product_upper
  have hD : (147285281667 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (2 / 25 : ℝ) - (13 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell64_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell64_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (2 / 25 : ℝ) - (13 / 640 : ℝ)) ≤
      (1 / (147285281667 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (147285281667 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 640 : ℝ) - Real.pi * Real.exp (2 / 25 : ℝ)) ≤
      (2 / (147285281667 / 5000000000 : ℝ) : ℝ) := by
    rw [show (13 / 640 : ℝ) - Real.pi * Real.exp (2 / 25 : ℝ) =
      -(Real.pi * Real.exp (2 / 25 : ℝ) - (13 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34075037879051169 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (34075037879051169 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell64_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 25 : ℝ) (13 / 320 : ℝ)) :
    (1094420111 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17698832591 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell64_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell64_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell65_leftExp :
    (10846420231 / 10000000000 : ℝ) ≤ Real.exp (13 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 160 : ℝ) (1002542288649 / 1000000000000 : ℝ)
    (10846420231 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell65_rightExp :
    Real.exp (33 / 400 : ℝ) ≤ (2171997347 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 400 : ℝ) (1002581451223 / 1000000000000 : ℝ)
    (2171997347 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell65_denomUpper :
    Real.exp (6782906661353771 / 2000000000000000 : ℝ) ≤ (297090980541 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6782906661353771 / 2000000000000000 : ℝ) (1111802882953
    / 1000000000000 : ℝ) (297090980541 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell65_denomLower :
    (295734707973 / 10000000000 : ℝ) ≤ Real.exp (4233597128293469 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4233597128293469 / 1250000000000000 : ℝ) (277910979857 /
    250000000000 : ℝ) (295734707973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell65_product_lower :
    (4259378378293469 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell65_leftExp
    (by norm_num : (0 : ℝ) ≤ (10846420231 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell65_product_upper :
    Real.pi * Real.exp (33 / 400 : ℝ) ≤ (6823531661353771 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell65_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell65_endpointLower :
    (218782159 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 320 : ℝ) (33 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4259378378293469 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell65_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 400 : ℝ) - (13 / 640 : ℝ)) ≤
      (297090980541 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell65_denomUpper
    linarith [hpThetaJensenCell65_product_upper]
  have hi : (1 / (297090980541 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 400 : ℝ) - (13 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (297090980541 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (297090980541 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 640 : ℝ) - Real.pi * Real.exp (33 / 400 : ℝ)) := by
    rw [show (13 / 640 : ℝ) - Real.pi * Real.exp (33 / 400 : ℝ) =
      -(Real.pi * Real.exp (33 / 400 : ℝ) - (13 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 160 : ℝ)) := by
    have h := hpThetaJensenCell65_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (297090980541 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell65_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 320 : ℝ) (33 / 800 : ℝ) ≤ (17690651361 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 400 : ℝ)) (6823531661353771 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell65_product_upper
  have hD : (295734707973 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 160 : ℝ) - (33 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell65_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell65_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 160 : ℝ) - (33 / 1600 : ℝ)) ≤
      (1 / (295734707973 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (295734707973 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 1600 : ℝ) - Real.pi * Real.exp (13 / 160 : ℝ)) ≤
      (2 / (295734707973 / 10000000000 : ℝ) : ℝ) := by
    rw [show (33 / 1600 : ℝ) - Real.pi * Real.exp (13 / 160 : ℝ) =
      -(Real.pi * Real.exp (13 / 160 : ℝ) - (33 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6823531661353771 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (6823531661353771 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell65_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 320 : ℝ) (33 / 800 : ℝ)) :
    (218782159 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17690651361 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell65_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell65_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell66_leftExp :
    (5429993367 / 5000000000 : ℝ) ≤ Real.exp (33 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 400 : ℝ) (501290725611 / 500000000000 : ℝ)
    (5429993367 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell66_rightExp :
    Real.exp (67 / 800 : ℝ) ≤ (5436785103 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 800 : ℝ) (40104824613 / 40000000000 : ℝ)
    (5436785103 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell66_denomUpper :
    Real.exp (16977041022089079 / 5000000000000000 : ℝ) ≤ (59653652867 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16977041022089079 / 5000000000000000 : ℝ) (555970149473
    / 500000000000 : ℝ) (59653652867 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell66_denomLower :
    (296905034149 / 10000000000 : ℝ) ≤ Real.exp (2119267027727533 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2119267027727533 / 625000000000000 : ℝ) (555890565261 /
    500000000000 : ℝ) (296905034149 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell66_product_lower :
    (2132352965227533 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell66_leftExp
    (by norm_num : (0 : ℝ) ≤ (5429993367 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell66_product_upper :
    Real.pi * Real.exp (67 / 800 : ℝ) ≤ (17080166022089079 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell66_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell66_endpointLower :
    (8747147899 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 800 : ℝ) (67 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2132352965227533 / 625000000000000 : ℝ) (Real.pi * Real.exp (33 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell66_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 800 : ℝ) - (33 / 1600 : ℝ)) ≤
      (59653652867 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell66_denomUpper
    linarith [hpThetaJensenCell66_product_upper]
  have hi : (1 / (59653652867 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 800 : ℝ) - (33 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (59653652867 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (59653652867 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 1600 : ℝ) - Real.pi * Real.exp (67 / 800 : ℝ)) := by
    rw [show (33 / 1600 : ℝ) - Real.pi * Real.exp (67 / 800 : ℝ) =
      -(Real.pi * Real.exp (67 / 800 : ℝ) - (33 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 400 : ℝ)) := by
    have h := hpThetaJensenCell66_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (59653652867 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell66_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 800 : ℝ) (67 / 1600 : ℝ) ≤ (17682341079 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 800 : ℝ)) (17080166022089079 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell66_product_upper
  have hD : (296905034149 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 400 : ℝ) - (67 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell66_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell66_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 400 : ℝ) - (67 / 3200 : ℝ)) ≤
      (1 / (296905034149 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (296905034149 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 3200 : ℝ) - Real.pi * Real.exp (33 / 400 : ℝ)) ≤
      (2 / (296905034149 / 10000000000 : ℝ) : ℝ) := by
    rw [show (67 / 3200 : ℝ) - Real.pi * Real.exp (33 / 400 : ℝ) =
      -(Real.pi * Real.exp (33 / 400 : ℝ) - (67 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17080166022089079 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (17080166022089079 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell66_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 800 : ℝ) (67 / 1600 : ℝ)) :
    (8747147899 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17682341079 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell66_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell66_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell67_leftExp :
    (2174714041 / 2000000000 : ℝ) ≤ Real.exp (67 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 800 : ℝ) (250655153831 / 250000000000 : ℝ)
    (2174714041 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell67_rightExp :
    Real.exp (17 / 200 : ℝ) ≤ (2721792667 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 200 : ℝ) (501329890479 / 500000000000 : ℝ)
    (2721792667 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell67_denomUpper :
    Real.exp (8498421040098531 / 2500000000000000 : ℝ) ≤ (4678934559 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8498421040098531 / 2500000000000000 : ℝ) (556038958713 /
    500000000000 : ℝ) (4678934559 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell67_denomLower :
    (59616316137 / 2000000000 : ℝ) ≤ Real.exp (848695529186659 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (848695529186659 / 250000000000000 : ℝ) (1111918543779 /
    1000000000000 : ℝ) (59616316137 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell67_product_lower :
    (854008029186659 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell67_leftExp
    (by norm_num : (0 : ℝ) ≤ (2174714041 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell67_product_upper :
    Real.pi * Real.exp (17 / 200 : ℝ) ≤ (8550764790098531 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell67_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell67_endpointLower :
    (2185736399 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 1600 : ℝ) (17 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (854008029186659 / 250000000000000 : ℝ) (Real.pi * Real.exp (67 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell67_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 200 : ℝ) - (67 / 3200 : ℝ)) ≤
      (4678934559 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell67_denomUpper
    linarith [hpThetaJensenCell67_product_upper]
  have hi : (1 / (4678934559 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 200 : ℝ) - (67 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4678934559 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4678934559 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 3200 : ℝ) - Real.pi * Real.exp (17 / 200 : ℝ)) := by
    rw [show (67 / 3200 : ℝ) - Real.pi * Real.exp (17 / 200 : ℝ) =
      -(Real.pi * Real.exp (17 / 200 : ℝ) - (67 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 800 : ℝ)) := by
    have h := hpThetaJensenCell67_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4678934559 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell67_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 1600 : ℝ) (17 / 400 : ℝ) ≤ (17673901947 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 200 : ℝ)) (8550764790098531 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell67_product_upper
  have hD : (59616316137 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 800 : ℝ) - (17 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell67_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell67_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 800 : ℝ) - (17 / 800 : ℝ)) ≤
      (1 / (59616316137 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (59616316137 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 800 : ℝ) - Real.pi * Real.exp (67 / 800 : ℝ)) ≤
      (2 / (59616316137 / 2000000000 : ℝ) : ℝ) := by
    rw [show (17 / 800 : ℝ) - Real.pi * Real.exp (67 / 800 : ℝ) =
      -(Real.pi * Real.exp (67 / 800 : ℝ) - (17 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8550764790098531 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8550764790098531 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell67_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 1600 : ℝ) (17 / 400 : ℝ)) :
    (2185736399 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17673901947 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell67_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell67_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell68_leftExp :
    (5443585333 / 5000000000 : ℝ) ≤ Real.exp (17 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 200 : ℝ) (1002659780957 / 1000000000000 : ℝ)
    (5443585333 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell68_rightExp :
    Real.exp (69 / 800 : ℝ) ≤ (545039407 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 800 : ℝ) (1002698948121 / 1000000000000 : ℝ)
    (545039407 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell68_denomUpper :
    Real.exp (1701666985755351 / 500000000000000 : ℝ) ≤ (300641662197 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1701666985755351 / 500000000000000 : ℝ) (556107869337 /
    500000000000 : ℝ) (300641662197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell68_denomLower :
    (299264386859 / 10000000000 : ℝ) ≤ Real.exp (2124213954183767 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2124213954183767 / 625000000000000 : ℝ) (1112056159509 /
    1000000000000 : ℝ) (299264386859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell68_product_lower :
    (2137690516683767 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell68_leftExp
    (by norm_num : (0 : ℝ) ≤ (5443585333 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell68_product_upper :
    Real.pi * Real.exp (69 / 800 : ℝ) ≤ (1712291985755351 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell68_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell68_endpointLower :
    (17477359111 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 400 : ℝ) (69 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2137690516683767 / 625000000000000 : ℝ) (Real.pi * Real.exp (17 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell68_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 800 : ℝ) - (17 / 800 : ℝ)) ≤
      (300641662197 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell68_denomUpper
    linarith [hpThetaJensenCell68_product_upper]
  have hi : (1 / (300641662197 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 800 : ℝ) - (17 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (300641662197 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (300641662197 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 800 : ℝ) - Real.pi * Real.exp (69 / 800 : ℝ)) := by
    rw [show (17 / 800 : ℝ) - Real.pi * Real.exp (69 / 800 : ℝ) =
      -(Real.pi * Real.exp (69 / 800 : ℝ) - (17 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 200 : ℝ)) := by
    have h := hpThetaJensenCell68_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (300641662197 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell68_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 400 : ℝ) (69 / 1600 : ℝ) ≤ (8832667073 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 800 : ℝ)) (1712291985755351 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell68_product_upper
  have hD : (299264386859 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 200 : ℝ) - (69 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell68_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell68_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 200 : ℝ) - (69 / 3200 : ℝ)) ≤
      (1 / (299264386859 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (299264386859 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 3200 : ℝ) - Real.pi * Real.exp (17 / 200 : ℝ)) ≤
      (2 / (299264386859 / 10000000000 : ℝ) : ℝ) := by
    rw [show (69 / 3200 : ℝ) - Real.pi * Real.exp (17 / 200 : ℝ) =
      -(Real.pi * Real.exp (17 / 200 : ℝ) - (69 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1712291985755351 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1712291985755351 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell68_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 400 : ℝ) (69 / 1600 : ℝ)) :
    (17477359111 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8832667073 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell68_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell68_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell69_leftExp :
    (10900788139 / 10000000000 : ℝ) ≤ Real.exp (69 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 800 : ℝ) (25067473703 / 25000000000 : ℝ)
    (10900788139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell69_rightExp :
    Real.exp (7 / 80 : ℝ) ≤ (2182884529 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 80 : ℝ) (501369058407 / 500000000000 : ℝ)
    (2182884529 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell69_denomUpper :
    Real.exp (6814609756114697 / 2000000000000000 : ℝ) ≤ (150918927781 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6814609756114697 / 2000000000000000 : ℝ) (278088440753 /
    250000000000 : ℝ) (150918927781 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell69_denomLower :
    (60090698449 / 2000000000 : ℝ) ≤ Real.exp (4253384851397161 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4253384851397161 / 1250000000000000 : ℝ) (139024247253 /
    125000000000 : ℝ) (60090698449 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell69_product_lower :
    (4280728601397161 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell69_leftExp
    (by norm_num : (0 : ℝ) ≤ (10900788139 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell69_product_upper :
    Real.pi * Real.exp (7 / 80 : ℝ) ≤ (6857734756114697 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell69_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell69_endpointLower :
    (545896867 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 1600 : ℝ) (7 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4280728601397161 / 1250000000000000 : ℝ) (Real.pi * Real.exp (69 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell69_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 80 : ℝ) - (69 / 3200 : ℝ)) ≤
      (150918927781 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell69_denomUpper
    linarith [hpThetaJensenCell69_product_upper]
  have hi : (1 / (150918927781 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 80 : ℝ) - (69 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (150918927781 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (150918927781 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 3200 : ℝ) - Real.pi * Real.exp (7 / 80 : ℝ)) := by
    rw [show (69 / 3200 : ℝ) - Real.pi * Real.exp (7 / 80 : ℝ) =
      -(Real.pi * Real.exp (7 / 80 : ℝ) - (69 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 800 : ℝ)) := by
    have h := hpThetaJensenCell69_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (150918927781 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell69_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 1600 : ℝ) (7 / 160 : ℝ) ≤ (17656637873 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 80 : ℝ)) (6857734756114697 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell69_product_upper
  have hD : (60090698449 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 800 : ℝ) - (7 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell69_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell69_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 800 : ℝ) - (7 / 320 : ℝ)) ≤
      (1 / (60090698449 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (60090698449 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 320 : ℝ) - Real.pi * Real.exp (69 / 800 : ℝ)) ≤
      (2 / (60090698449 / 2000000000 : ℝ) : ℝ) := by
    rw [show (7 / 320 : ℝ) - Real.pi * Real.exp (69 / 800 : ℝ) =
      -(Real.pi * Real.exp (69 / 800 : ℝ) - (7 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6857734756114697 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (6857734756114697 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell69_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 1600 : ℝ) (7 / 160 : ℝ)) :
    (545896867 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17656637873 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell69_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell69_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell70_leftExp :
    (2728605661 / 2500000000 : ℝ) ≤ Real.exp (7 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 80 : ℝ) (1002738116813 / 1000000000000 : ℝ)
    (2728605661 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell70_rightExp :
    Real.exp (71 / 800 : ℝ) ≤ (2732018551 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 800 : ℝ) (250694321759 / 250000000000 : ℝ)
    (2732018551 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell70_denomUpper :
    Real.exp (8528202855691743 / 2500000000000000 : ℝ) ≤ (3788005399 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8528202855691743 / 2500000000000000 : ℝ) (1112491990739
    / 1000000000000 : ℝ) (3788005399 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell70_denomLower :
    (150824468249 / 5000000000 : ℝ) ≤ Real.exp (1064587120719039 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1064587120719039 / 312500000000000 : ℝ) (1112331999613 /
    1000000000000 : ℝ) (150824468249 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell70_product_lower :
    (1071520714469039 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell70_leftExp
    (by norm_num : (0 : ℝ) ≤ (2728605661 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell70_product_upper :
    Real.pi * Real.exp (71 / 800 : ℝ) ≤ (8582890355691743 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell70_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell70_endpointLower :
    (17459913287 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 160 : ℝ) (71 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1071520714469039 / 312500000000000 : ℝ) (Real.pi * Real.exp (7 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell70_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 800 : ℝ) - (7 / 320 : ℝ)) ≤
      (3788005399 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell70_denomUpper
    linarith [hpThetaJensenCell70_product_upper]
  have hi : (1 / (3788005399 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 800 : ℝ) - (7 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3788005399 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3788005399 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 320 : ℝ) - Real.pi * Real.exp (71 / 800 : ℝ)) := by
    rw [show (7 / 320 : ℝ) - Real.pi * Real.exp (71 / 800 : ℝ) =
      -(Real.pi * Real.exp (71 / 800 : ℝ) - (7 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 80 : ℝ)) := by
    have h := hpThetaJensenCell70_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3788005399 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell70_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 160 : ℝ) (71 / 1600 : ℝ) ≤ (17647813333 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 800 : ℝ)) (8582890355691743 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell70_product_upper
  have hD : (150824468249 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 80 : ℝ) - (71 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell70_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell70_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 80 : ℝ) - (71 / 3200 : ℝ)) ≤
      (1 / (150824468249 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (150824468249 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 3200 : ℝ) - Real.pi * Real.exp (7 / 80 : ℝ)) ≤
      (2 / (150824468249 / 5000000000 : ℝ) : ℝ) := by
    rw [show (71 / 3200 : ℝ) - Real.pi * Real.exp (7 / 80 : ℝ) =
      -(Real.pi * Real.exp (7 / 80 : ℝ) - (71 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8582890355691743 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8582890355691743 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell70_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 160 : ℝ) (71 / 1600 : ℝ)) :
    (17459913287 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17647813333 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell70_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell70_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell71_leftExp :
    (5464037101 / 5000000000 : ℝ) ≤ Real.exp (71 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 800 : ℝ) (200555457407 / 200000000000 : ℝ)
    (5464037101 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell71_rightExp :
    Real.exp (9 / 100 : ℝ) ≤ (5470871419 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 100 : ℝ) (1002816458789 / 1000000000000 : ℝ)
    (5470871419 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell71_denomUpper :
    Real.exp (17076313853830467 / 5000000000000000 : ℝ) ≤ (30424943163 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17076313853830467 / 5000000000000000 : ℝ) (1112630422157
    / 1000000000000 : ℝ) (30424943163 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell71_denomLower :
    (302850759667 / 10000000000 : ℝ) ≤ Real.exp (2131659405525599 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2131659405525599 / 625000000000000 : ℝ) (556235112289 /
    500000000000 : ℝ) (302850759667 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell71_product_lower :
    (2145721905525599 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell71_leftExp
    (by norm_num : (0 : ℝ) ≤ (5464037101 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell71_product_upper :
    Real.pi * Real.exp (9 / 100 : ℝ) ≤ (17187251353830467 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell71_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell71_endpointLower :
    (17450999939 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 1600 : ℝ) (9 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2145721905525599 / 625000000000000 : ℝ) (Real.pi * Real.exp (71 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell71_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 100 : ℝ) - (71 / 3200 : ℝ)) ≤
      (30424943163 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell71_denomUpper
    linarith [hpThetaJensenCell71_product_upper]
  have hi : (1 / (30424943163 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 100 : ℝ) - (71 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (30424943163 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (30424943163 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 3200 : ℝ) - Real.pi * Real.exp (9 / 100 : ℝ)) := by
    rw [show (71 / 3200 : ℝ) - Real.pi * Real.exp (9 / 100 : ℝ) =
      -(Real.pi * Real.exp (9 / 100 : ℝ) - (71 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 800 : ℝ)) := by
    have h := hpThetaJensenCell71_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (30424943163 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell71_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 1600 : ℝ) (9 / 200 : ℝ) ≤ (705554429 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 100 : ℝ)) (17187251353830467 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell71_product_upper
  have hD : (302850759667 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 800 : ℝ) - (9 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell71_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell71_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 800 : ℝ) - (9 / 400 : ℝ)) ≤
      (1 / (302850759667 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (302850759667 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 400 : ℝ) - Real.pi * Real.exp (71 / 800 : ℝ)) ≤
      (2 / (302850759667 / 10000000000 : ℝ) : ℝ) := by
    rw [show (9 / 400 : ℝ) - Real.pi * Real.exp (71 / 800 : ℝ) =
      -(Real.pi * Real.exp (71 / 800 : ℝ) - (9 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17187251353830467 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (17187251353830467 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell71_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 1600 : ℝ) (9 / 200 : ℝ)) :
    (17450999939 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (705554429 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell71_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell71_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell72_leftExp :
    (2735435709 / 2500000000 : ℝ) ≤ Real.exp (9 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 100 : ℝ) (250704114697 / 250000000000 : ℝ)
    (2735435709 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell72_rightExp :
    Real.exp (73 / 800 : ℝ) ≤ (1369428571 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 800 : ℝ) (125356954009 / 125000000000 : ℝ)
    (1369428571 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell72_denomUpper :
    Real.exp (4274062212653603 / 1250000000000000 : ℝ) ≤ (152732447669 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4274062212653603 / 1250000000000000 : ℝ) (34774033049 /
    31250000000 : ℝ) (152732447669 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell72_denomLower :
    (304059002251 / 10000000000 : ℝ) ≤ Real.exp (1067073961238591 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1067073961238591 / 312500000000000 : ℝ) (27815216331 /
    25000000000 : ℝ) (304059002251 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell72_product_lower :
    (1074202867488591 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell72_leftExp
    (by norm_num : (0 : ℝ) ≤ (2735435709 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell72_product_upper :
    Real.pi * Real.exp (73 / 800 : ℝ) ≤ (4302187212653603 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell72_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell72_endpointLower :
    (17441959911 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 200 : ℝ) (73 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1074202867488591 / 312500000000000 : ℝ) (Real.pi * Real.exp (9 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell72_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 800 : ℝ) - (9 / 400 : ℝ)) ≤
      (152732447669 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell72_denomUpper
    linarith [hpThetaJensenCell72_product_upper]
  have hi : (1 / (152732447669 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 800 : ℝ) - (9 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (152732447669 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (152732447669 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 400 : ℝ) - Real.pi * Real.exp (73 / 800 : ℝ)) := by
    rw [show (9 / 400 : ℝ) - Real.pi * Real.exp (73 / 800 : ℝ) =
      -(Real.pi * Real.exp (73 / 800 : ℝ) - (9 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 100 : ℝ)) := by
    have h := hpThetaJensenCell72_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (152732447669 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell72_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 200 : ℝ) (73 / 1600 : ℝ) ≤ (8814890121 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 800 : ℝ)) (4302187212653603 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell72_product_upper
  have hD : (304059002251 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 100 : ℝ) - (73 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell72_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell72_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 100 : ℝ) - (73 / 3200 : ℝ)) ≤
      (1 / (304059002251 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (304059002251 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 3200 : ℝ) - Real.pi * Real.exp (9 / 100 : ℝ)) ≤
      (2 / (304059002251 / 10000000000 : ℝ) : ℝ) := by
    rw [show (73 / 3200 : ℝ) - Real.pi * Real.exp (9 / 100 : ℝ) =
      -(Real.pi * Real.exp (9 / 100 : ℝ) - (73 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4302187212653603 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4302187212653603 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell72_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 200 : ℝ) (73 / 1600 : ℝ)) :
    (17441959911 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8814890121 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell72_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell72_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell73_leftExp :
    (10955428567 / 10000000000 : ℝ) ≤ Real.exp (73 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 800 : ℝ) (1002855632071 / 1000000000000 : ℝ)
    (10955428567 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell73_rightExp :
    Real.exp (37 / 400 : ℝ) ≤ (1371141427 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 400 : ℝ) (200578961377 / 200000000000 : ℝ)
    (1371141427 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell73_denomUpper :
    Real.exp (4279052684073211 / 1250000000000000 : ℝ) ≤ (38335858007 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4279052684073211 / 1250000000000000 : ℝ) (1112907897283
    / 1000000000000 : ℝ) (38335858007 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell73_denomLower :
    (305273704881 / 10000000000 : ℝ) ≤ Real.exp (4273279592832333 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4273279592832333 / 1250000000000000 : ℝ) (556373642951 /
    500000000000 : ℝ) (305273704881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell73_product_lower :
    (4302185842832333 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell73_leftExp
    (by norm_num : (0 : ℝ) ≤ (10955428567 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell73_product_upper :
    Real.pi * Real.exp (37 / 400 : ℝ) ≤ (4307568309073211 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell73_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell73_endpointLower :
    (8716396701 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 1600 : ℝ) (37 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4302185842832333 / 1250000000000000 : ℝ) (Real.pi * Real.exp (73 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell73_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 400 : ℝ) - (73 / 3200 : ℝ)) ≤
      (38335858007 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell73_denomUpper
    linarith [hpThetaJensenCell73_product_upper]
  have hi : (1 / (38335858007 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 400 : ℝ) - (73 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38335858007 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38335858007 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 3200 : ℝ) - Real.pi * Real.exp (37 / 400 : ℝ)) := by
    rw [show (73 / 3200 : ℝ) - Real.pi * Real.exp (37 / 400 : ℝ) =
      -(Real.pi * Real.exp (37 / 400 : ℝ) - (73 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 800 : ℝ)) := by
    have h := hpThetaJensenCell73_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38335858007 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell73_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 1600 : ℝ) (37 / 800 : ℝ) ≤ (17620572091 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 400 : ℝ)) (4307568309073211 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell73_product_upper
  have hD : (305273704881 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 800 : ℝ) - (37 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell73_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell73_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 800 : ℝ) - (37 / 1600 : ℝ)) ≤
      (1 / (305273704881 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (305273704881 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 1600 : ℝ) - Real.pi * Real.exp (73 / 800 : ℝ)) ≤
      (2 / (305273704881 / 10000000000 : ℝ) : ℝ) := by
    rw [show (37 / 1600 : ℝ) - Real.pi * Real.exp (73 / 800 : ℝ) =
      -(Real.pi * Real.exp (73 / 800 : ℝ) - (37 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4307568309073211 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4307568309073211 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell73_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 1600 : ℝ) (37 / 800 : ℝ)) :
    (8716396701 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17620572091 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell73_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell73_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell74_leftExp :
    (2193826283 / 2000000000 : ℝ) ≤ Real.exp (37 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 400 : ℝ) (250723701721 / 250000000000 : ℝ)
    (2193826283 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell74_rightExp :
    Real.exp (3 / 32 : ℝ) ≤ (2745712851 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 32 : ℝ) (1002933983229 / 1000000000000 : ℝ)
    (2745712851 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell74_denomUpper :
    Real.exp (8568099772711643 / 2500000000000000 : ℝ) ≤ (307915379119 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8568099772711643 / 2500000000000000 : ℝ) (69565433851 /
    62500000000 : ℝ) (307915379119 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell74_denomLower :
    (6129898167 / 200000000 : ℝ) ≤ Real.exp (855654012507817 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (855654012507817 / 250000000000000 : ℝ) (1112886122853 /
    1000000000000 : ℝ) (6129898167 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell74_product_lower :
    (861513387507817 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell74_leftExp
    (by norm_num : (0 : ℝ) ≤ (2193826283 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell74_product_upper :
    Real.pi * Real.exp (3 / 32 : ℝ) ≤ (8625912272711643 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell74_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell74_endpointLower :
    (17423500609 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 800 : ℝ) (3 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (861513387507817 / 250000000000000 : ℝ) (Real.pi * Real.exp (37 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell74_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 32 : ℝ) - (37 / 1600 : ℝ)) ≤
      (307915379119 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell74_denomUpper
    linarith [hpThetaJensenCell74_product_upper]
  have hi : (1 / (307915379119 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 32 : ℝ) - (37 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (307915379119 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (307915379119 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 1600 : ℝ) - Real.pi * Real.exp (3 / 32 : ℝ)) := by
    rw [show (37 / 1600 : ℝ) - Real.pi * Real.exp (3 / 32 : ℝ) =
      -(Real.pi * Real.exp (3 / 32 : ℝ) - (37 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 400 : ℝ)) := by
    have h := hpThetaJensenCell74_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (307915379119 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell74_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 800 : ℝ) (3 / 64 : ℝ) ≤ (1761123649 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 32 : ℝ)) (8625912272711643 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell74_product_upper
  have hD : (6129898167 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 400 : ℝ) - (3 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell74_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell74_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 400 : ℝ) - (3 / 128 : ℝ)) ≤
      (1 / (6129898167 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6129898167 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 128 : ℝ) - Real.pi * Real.exp (37 / 400 : ℝ)) ≤
      (2 / (6129898167 / 200000000 : ℝ) : ℝ) := by
    rw [show (3 / 128 : ℝ) - Real.pi * Real.exp (37 / 400 : ℝ) =
      -(Real.pi * Real.exp (37 / 400 : ℝ) - (3 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8625912272711643 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8625912272711643 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell74_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 800 : ℝ) (3 / 64 : ℝ)) :
    (17423500609 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1761123649 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell74_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell74_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell75_leftExp :
    (5491425701 / 5000000000 : ℝ) ≤ Real.exp (3 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 32 : ℝ) (250733495807 / 250000000000 : ℝ)
    (5491425701 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell75_rightExp :
    Real.exp (19 / 200 : ℝ) ≤ (1374573569 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 200 : ℝ) (1002973161103 / 1000000000000 : ℝ)
    (1374573569 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell75_denomUpper :
    Real.exp (4289053827355417 / 1250000000000000 : ℝ) ≤ (309150481931 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4289053827355417 / 1250000000000000 : ℝ) (139148273857 /
    125000000000 : ℝ) (309150481931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell75_denomLower :
    (307722653957 / 10000000000 : ℝ) ≤ Real.exp (2141633631356999 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2141633631356999 / 625000000000000 : ℝ) (556512582203 /
    500000000000 : ℝ) (307722653957 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell75_product_lower :
    (2156477381356999 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell75_leftExp
    (by norm_num : (0 : ℝ) ≤ (5491425701 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell75_product_upper :
    Real.pi * Real.exp (19 / 200 : ℝ) ≤ (4318350702355417 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell75_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell75_endpointLower :
    (17414081751 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 64 : ℝ) (19 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2156477381356999 / 625000000000000 : ℝ) (Real.pi * Real.exp (3 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell75_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 200 : ℝ) - (3 / 128 : ℝ)) ≤
      (309150481931 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell75_denomUpper
    linarith [hpThetaJensenCell75_product_upper]
  have hi : (1 / (309150481931 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 200 : ℝ) - (3 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (309150481931 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (309150481931 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 128 : ℝ) - Real.pi * Real.exp (19 / 200 : ℝ)) := by
    rw [show (3 / 128 : ℝ) - Real.pi * Real.exp (19 / 200 : ℝ) =
      -(Real.pi * Real.exp (19 / 200 : ℝ) - (3 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 32 : ℝ)) := by
    have h := hpThetaJensenCell75_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (309150481931 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell75_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 64 : ℝ) (19 / 400 : ℝ) ≤ (17601773637 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 200 : ℝ)) (4318350702355417 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell75_product_upper
  have hD : (307722653957 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 32 : ℝ) - (19 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell75_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell75_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 32 : ℝ) - (19 / 800 : ℝ)) ≤
      (1 / (307722653957 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (307722653957 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 800 : ℝ) - Real.pi * Real.exp (3 / 32 : ℝ)) ≤
      (2 / (307722653957 / 10000000000 : ℝ) : ℝ) := by
    rw [show (19 / 800 : ℝ) - Real.pi * Real.exp (3 / 32 : ℝ) =
      -(Real.pi * Real.exp (3 / 32 : ℝ) - (19 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4318350702355417 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4318350702355417 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell75_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 64 : ℝ) (19 / 400 : ℝ)) :
    (17414081751 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17601773637 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell75_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell75_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell76_leftExp :
    (10996588551 / 10000000000 : ℝ) ≤ Real.exp (19 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 200 : ℝ) (501486580551 / 500000000000 : ℝ)
    (10996588551 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell76_rightExp :
    Real.exp (77 / 800 : ℝ) ≤ (5505171441 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 800 : ℝ) (1003012340507 / 1000000000000 : ℝ)
    (5505171441 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell76_denomUpper :
    Real.exp (17176258062845513 / 5000000000000000 : ℝ) ≤ (310392214423 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17176258062845513 / 5000000000000000 : ℝ) (556662822659
    / 500000000000 : ℝ) (310392214423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell76_denomLower :
    (308956983389 / 10000000000 : ℝ) ≤ Real.exp (4288271202389149 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4288271202389149 / 1250000000000000 : ℝ) (222632882177 /
    200000000000 : ℝ) (308956983389 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell76_product_lower :
    (4318349327389149 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell76_leftExp
    (by norm_num : (0 : ℝ) ≤ (10996588551 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell76_product_upper :
    Real.pi * Real.exp (77 / 800 : ℝ) ≤ (17295008062845513 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell76_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell76_endpointLower :
    (17404537041 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 400 : ℝ) (77 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4318349327389149 / 1250000000000000 : ℝ) (Real.pi * Real.exp (19 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell76_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 800 : ℝ) - (19 / 800 : ℝ)) ≤
      (310392214423 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell76_denomUpper
    linarith [hpThetaJensenCell76_product_upper]
  have hi : (1 / (310392214423 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 800 : ℝ) - (19 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (310392214423 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (310392214423 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 800 : ℝ) - Real.pi * Real.exp (77 / 800 : ℝ)) := by
    rw [show (19 / 800 : ℝ) - Real.pi * Real.exp (77 / 800 : ℝ) =
      -(Real.pi * Real.exp (77 / 800 : ℝ) - (19 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 200 : ℝ)) := by
    have h := hpThetaJensenCell76_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (310392214423 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell76_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 400 : ℝ) (77 / 1600 : ℝ) ≤ (17592183737 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 800 : ℝ)) (17295008062845513 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell76_product_upper
  have hD : (308956983389 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 200 : ℝ) - (77 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell76_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell76_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 200 : ℝ) - (77 / 3200 : ℝ)) ≤
      (1 / (308956983389 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (308956983389 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 3200 : ℝ) - Real.pi * Real.exp (19 / 200 : ℝ)) ≤
      (2 / (308956983389 / 10000000000 : ℝ) : ℝ) := by
    rw [show (77 / 3200 : ℝ) - Real.pi * Real.exp (19 / 200 : ℝ) =
      -(Real.pi * Real.exp (19 / 200 : ℝ) - (77 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17295008062845513 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (17295008062845513 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell76_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 400 : ℝ) (77 / 1600 : ℝ)) :
    (17404537041 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17592183737 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell76_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell76_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell77_leftExp :
    (11010342881 / 10000000000 : ℝ) ≤ Real.exp (77 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 800 : ℝ) (501506170253 / 500000000000 : ℝ)
    (11010342881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell77_rightExp :
    Real.exp (39 / 400 : ℝ) ≤ (689007151 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 400 : ℝ) (501525760721 / 500000000000 : ℝ)
    (689007151 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell77_denomUpper :
    Real.exp (2149540980031543 / 625000000000000 : ℝ) ≤ (31164061879 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2149540980031543 / 625000000000000 : ℝ) (1113465305313 /
    1000000000000 : ℝ) (31164061879 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell77_denomLower :
    (77549484563 / 2500000000 : ℝ) ≤ Real.exp (4293281889025819 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4293281889025819 / 1250000000000000 : ℝ) (1113303862571
    / 1000000000000 : ℝ) (77549484563 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell77_product_lower :
    (4323750639025819 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell77_leftExp
    (by norm_num : (0 : ℝ) ≤ (11010342881 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell77_product_upper :
    Real.pi * Real.exp (39 / 400 : ℝ) ≤ (2164580042531543 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell77_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell77_endpointLower :
    (17394866679 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 1600 : ℝ) (39 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4323750639025819 / 1250000000000000 : ℝ) (Real.pi * Real.exp (77 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell77_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 400 : ℝ) - (77 / 3200 : ℝ)) ≤
      (31164061879 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell77_denomUpper
    linarith [hpThetaJensenCell77_product_upper]
  have hi : (1 / (31164061879 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 400 : ℝ) - (77 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31164061879 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31164061879 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 3200 : ℝ) - Real.pi * Real.exp (39 / 400 : ℝ)) := by
    rw [show (77 / 3200 : ℝ) - Real.pi * Real.exp (39 / 400 : ℝ) =
      -(Real.pi * Real.exp (39 / 400 : ℝ) - (77 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 800 : ℝ)) := by
    have h := hpThetaJensenCell77_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31164061879 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell77_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 1600 : ℝ) (39 / 800 : ℝ) ≤ (2197808377 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 400 : ℝ)) (2164580042531543 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell77_product_upper
  have hD : (77549484563 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 800 : ℝ) - (39 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell77_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell77_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 800 : ℝ) - (39 / 1600 : ℝ)) ≤
      (1 / (77549484563 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (77549484563 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 1600 : ℝ) - Real.pi * Real.exp (77 / 800 : ℝ)) ≤
      (2 / (77549484563 / 2500000000 : ℝ) : ℝ) := by
    rw [show (39 / 1600 : ℝ) - Real.pi * Real.exp (77 / 800 : ℝ) =
      -(Real.pi * Real.exp (77 / 800 : ℝ) - (39 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2164580042531543 / 625000000000000 : ℝ) ^ 2 - 6 *
      (2164580042531543 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell77_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 1600 : ℝ) (39 / 800 : ℝ)) :
    (17394866679 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2197808377 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell77_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell77_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell78_leftExp :
    (2204822883 / 2000000000 : ℝ) ≤ Real.exp (39 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 400 : ℝ) (1003051521441 / 1000000000000 : ℝ)
    (2204822883 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell78_rightExp :
    Real.exp (79 / 800 : ℝ) ≤ (441516127 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 800 : ℝ) (1003090703907 / 1000000000000 : ℝ)
    (441516127 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell78_denomUpper :
    Real.exp (1377313973970311 / 400000000000000 : ℝ) ≤ (156447868737 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1377313973970311 / 400000000000000 : ℝ) (556802585573 /
    500000000000 : ℝ) (156447868737 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell78_denomLower :
    (311445560811 / 10000000000 : ℝ) ≤ Real.exp (859659866331217 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (859659866331217 / 250000000000000 : ℝ) (556721759893 /
    500000000000 : ℝ) (311445560811 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell78_product_lower :
    (865831741331217 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell78_leftExp
    (by norm_num : (0 : ℝ) ≤ (2204822883 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell78_product_upper :
    Real.pi * Real.exp (79 / 800 : ℝ) ≤ (1387063973970311 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell78_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell78_endpointLower :
    (2173133861 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 800 : ℝ) (79 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (865831741331217 / 250000000000000 : ℝ) (Real.pi * Real.exp (39 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell78_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 800 : ℝ) - (39 / 1600 : ℝ)) ≤
      (156447868737 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell78_denomUpper
    linarith [hpThetaJensenCell78_product_upper]
  have hi : (1 / (156447868737 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 800 : ℝ) - (39 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (156447868737 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (156447868737 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 1600 : ℝ) - Real.pi * Real.exp (79 / 800 : ℝ)) := by
    rw [show (39 / 1600 : ℝ) - Real.pi * Real.exp (79 / 800 : ℝ) =
      -(Real.pi * Real.exp (79 / 800 : ℝ) - (39 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 400 : ℝ)) := by
    have h := hpThetaJensenCell78_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (156447868737 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell78_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 800 : ℝ) (79 / 1600 : ℝ) ≤ (17572623681 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 800 : ℝ)) (1387063973970311 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell78_product_upper
  have hD : (311445560811 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 400 : ℝ) - (79 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell78_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell78_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 400 : ℝ) - (79 / 3200 : ℝ)) ≤
      (1 / (311445560811 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (311445560811 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 3200 : ℝ) - Real.pi * Real.exp (39 / 400 : ℝ)) ≤
      (2 / (311445560811 / 10000000000 : ℝ) : ℝ) := by
    rw [show (79 / 3200 : ℝ) - Real.pi * Real.exp (39 / 400 : ℝ) =
      -(Real.pi * Real.exp (39 / 400 : ℝ) - (79 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1387063973970311 / 400000000000000 : ℝ) ^ 2 - 6 *
      (1387063973970311 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell78_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 800 : ℝ) (79 / 1600 : ℝ)) :
    (2173133861 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17572623681 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell78_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell78_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell79_leftExp :
    (5518951587 / 5000000000 : ℝ) ≤ Real.exp (79 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 800 : ℝ) (501545351953 / 500000000000 : ℝ)
    (5518951587 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell79_rightExp :
    Real.exp (1 / 10 : ℝ) ≤ (11051709181 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 10 : ℝ) (1003129887903 / 1000000000000 : ℝ)
    (11051709181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell79_denomUpper :
    Real.exp (34473097201065333 / 10000000000000000 : ℝ) ≤ (62831522657 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (34473097201065333 / 10000000000000000 : ℝ)
    (1113745243129 / 1000000000000 : ℝ) (62831522657 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell79_denomLower :
    (312699893473 / 10000000000 : ℝ) ≤ Real.exp (2151661769263313 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2151661769263313 / 625000000000000 : ℝ) (556791691417 /
    500000000000 : ℝ) (312699893473 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell79_product_lower :
    (2167286769263313 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell79_leftExp
    (by norm_num : (0 : ℝ) ≤ (5518951587 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell79_product_upper :
    Real.pi * Real.exp (1 / 10 : ℝ) ≤ (34719972201065333 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell79_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell79_endpointLower :
    (17375149879 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 1600 : ℝ) (1 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2167286769263313 / 625000000000000 : ℝ) (Real.pi * Real.exp (79 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell79_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 10 : ℝ) - (79 / 3200 : ℝ)) ≤
      (62831522657 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell79_denomUpper
    linarith [hpThetaJensenCell79_product_upper]
  have hi : (1 / (62831522657 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 10 : ℝ) - (79 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (62831522657 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (62831522657 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 3200 : ℝ) - Real.pi * Real.exp (1 / 10 : ℝ)) := by
    rw [show (79 / 3200 : ℝ) - Real.pi * Real.exp (1 / 10 : ℝ) =
      -(Real.pi * Real.exp (1 / 10 : ℝ) - (79 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 800 : ℝ)) := by
    have h := hpThetaJensenCell79_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (62831522657 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell79_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 1600 : ℝ) (1 / 20 : ℝ) ≤ (68604117 / 39062500 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 10 : ℝ)) (34719972201065333 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 20 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell79_product_upper
  have hD : (312699893473 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 800 : ℝ) - (1 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell79_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell79_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 800 : ℝ) - (1 / 40 : ℝ)) ≤
      (1 / (312699893473 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (312699893473 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 40 : ℝ) - Real.pi * Real.exp (79 / 800 : ℝ)) ≤
      (2 / (312699893473 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 40 : ℝ) - Real.pi * Real.exp (79 / 800 : ℝ) =
      -(Real.pi * Real.exp (79 / 800 : ℝ) - (1 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34719972201065333 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (34719972201065333 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell79_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 1600 : ℝ) (1 / 20 : ℝ)) :
    (17375149879 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (68604117 / 39062500 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell79_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell79_endpointUpper

def hpThetaJensenCellsBatch003Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (17542035589 / 10000000000 : ℝ)
  | 1 => (17534399871 / 10000000000 : ℝ)
  | 2 => (17526635541 / 10000000000 : ℝ)
  | 3 => (17518742783 / 10000000000 : ℝ)
  | 4 => (1094420111 / 625000000 : ℝ)
  | 5 => (218782159 / 125000000 : ℝ)
  | 6 => (8747147899 / 5000000000 : ℝ)
  | 7 => (2185736399 / 1250000000 : ℝ)
  | 8 => (17477359111 / 10000000000 : ℝ)
  | 9 => (545896867 / 312500000 : ℝ)
  | 10 => (17459913287 / 10000000000 : ℝ)
  | 11 => (17450999939 / 10000000000 : ℝ)
  | 12 => (17441959911 / 10000000000 : ℝ)
  | 13 => (8716396701 / 5000000000 : ℝ)
  | 14 => (17423500609 / 10000000000 : ℝ)
  | 15 => (17414081751 / 10000000000 : ℝ)
  | 16 => (17404537041 / 10000000000 : ℝ)
  | 17 => (17394866679 / 10000000000 : ℝ)
  | 18 => (2173133861 / 1250000000 : ℝ)
  | 19 => (17375149879 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch003Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17730263239 / 10000000000 : ℝ)
  | 1 => (17722600087 / 10000000000 : ℝ)
  | 2 => (8857403569 / 5000000000 : ℝ)
  | 3 => (553340143 / 312500000 : ℝ)
  | 4 => (17698832591 / 10000000000 : ℝ)
  | 5 => (17690651361 / 10000000000 : ℝ)
  | 6 => (17682341079 / 10000000000 : ℝ)
  | 7 => (17673901947 / 10000000000 : ℝ)
  | 8 => (8832667073 / 5000000000 : ℝ)
  | 9 => (17656637873 / 10000000000 : ℝ)
  | 10 => (17647813333 / 10000000000 : ℝ)
  | 11 => (705554429 / 400000000 : ℝ)
  | 12 => (8814890121 / 5000000000 : ℝ)
  | 13 => (17620572091 / 10000000000 : ℝ)
  | 14 => (1761123649 / 1000000000 : ℝ)
  | 15 => (17601773637 / 10000000000 : ℝ)
  | 16 => (17592183737 / 10000000000 : ℝ)
  | 17 => (2197808377 / 1250000000 : ℝ)
  | 18 => (17572623681 / 10000000000 : ℝ)
  | 19 => (68604117 / 39062500 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch003_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch003Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch003Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell60_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell61_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell62_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell63_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell64_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell65_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell66_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell67_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell68_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell69_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell70_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell71_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell72_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell73_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell74_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell75_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell76_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell77_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell78_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell79_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper] at h ⊢
    exact h

end HodgeProofHP
