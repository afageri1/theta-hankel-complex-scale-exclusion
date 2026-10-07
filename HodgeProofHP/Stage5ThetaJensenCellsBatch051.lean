import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1020_leftExp :
    (357870141 / 100000000 : ℝ) ≤ Real.exp (51 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 40 : ℝ) (1040648160213 / 1000000000000 : ℝ)
    (357870141 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1020_rightExp :
    Real.exp (1021 / 800 : ℝ) ≤ (223948599 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1021 / 800 : ℝ) (1040688811327 / 1000000000000 : ℝ)
    (223948599 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1020_denomUpper :
    Real.exp (683633475978207 / 62500000000000 : ℝ) ≤ (281411567025773 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (683633475978207 / 62500000000000 : ℝ) (140750233217 /
    100000000000 : ℝ) (281411567025773 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1020_denomLower :
    (277394270530867 / 5000000000 : ℝ) ≤ Real.exp (136546965250559 / 12500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (136546965250559 / 12500000000000 : ℝ) (703435024219 /
    500000000000 : ℝ) (277394270530867 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1020_product_lower :
    (140535246500559 / 12500000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1020_leftExp
    (by norm_num : (0 : ℝ) ≤ (357870141 / 100000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1020_product_upper :
    Real.pi * Real.exp (1021 / 800 : ℝ) ≤ (703555350978207 / 62500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1020_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1020_endpointLower :
    (7784809 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 80 : ℝ) (1021 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (140535246500559 / 12500000000000 : ℝ) (Real.pi * Real.exp (51 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1020_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1021 / 800 : ℝ) - (51 / 160 : ℝ)) ≤
      (281411567025773 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1020_denomUpper
    linarith [hpThetaJensenCell1020_product_upper]
  have hi : (1 / (281411567025773 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1021 / 800 : ℝ) - (51 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (281411567025773 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (281411567025773 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 160 : ℝ) - Real.pi * Real.exp (1021 / 800 : ℝ)) := by
    rw [show (51 / 160 : ℝ) - Real.pi * Real.exp (1021 / 800 : ℝ) =
      -(Real.pi * Real.exp (1021 / 800 : ℝ) - (51 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1020_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (281411567025773 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1020_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 80 : ℝ) (1021 / 1600 : ℝ) ≤ (158794039 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1021 / 800 : ℝ)) (703555350978207 / 62500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1021 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1020_product_upper
  have hD : (277394270530867 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 40 : ℝ) - (1021 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1020_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1020_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 40 : ℝ) - (1021 / 3200 : ℝ)) ≤
      (1 / (277394270530867 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (277394270530867 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1021 / 3200 : ℝ) - Real.pi * Real.exp (51 / 40 : ℝ)) ≤
      (2 / (277394270530867 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1021 / 3200 : ℝ) - Real.pi * Real.exp (51 / 40 : ℝ) =
      -(Real.pi * Real.exp (51 / 40 : ℝ) - (1021 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (703555350978207 / 62500000000000 : ℝ) ^ 2 - 6 *
      (703555350978207 / 62500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1020_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 80 : ℝ) (1021 / 1600 : ℝ)) :
    (7784809 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (158794039 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1020_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1020_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1021_leftExp :
    (17915887919 / 5000000000 : ℝ) ≤ Real.exp (1021 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1021 / 800 : ℝ) (520344405663 / 500000000000 : ℝ)
    (17915887919 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1021_rightExp :
    Real.exp (511 / 400 : ℝ) ≤ (7175318713 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (511 / 400 : ℝ) (1040729464027 / 1000000000000 : ℝ)
    (7175318713 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1021_denomUpper :
    Real.exp (21903806041529809 / 2000000000000000 : ℝ) ≤ (71328166615621 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21903806041529809 / 2000000000000000 : ℝ) (281621602833
    / 200000000000 : ℝ) (71328166615621 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1021_denomLower :
    (562469463699799 / 10000000000 : ℝ) ≤ Real.exp (6835941894903381 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6835941894903381 / 625000000000000 : ℝ) (1407474684529 /
    1000000000000 : ℝ) (562469463699799 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1021_product_lower :
    (7035551269903381 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1021 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1021_leftExp
    (by norm_num : (0 : ℝ) ≤ (17915887919 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1021_product_upper :
    Real.pi * Real.exp (511 / 400 : ℝ) ≤ (22541931041529809 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1021_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1021_endpointLower :
    (4811917 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (1021 / 1600 : ℝ) (511 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7035551269903381 / 625000000000000 : ℝ) (Real.pi * Real.exp (1021 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1021_product_lower
  have hD : Real.exp (Real.pi * Real.exp (511 / 400 : ℝ) - (1021 / 3200 : ℝ)) ≤
      (71328166615621 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1021_denomUpper
    linarith [hpThetaJensenCell1021_product_upper]
  have hi : (1 / (71328166615621 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (511 / 400 : ℝ) - (1021 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71328166615621 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71328166615621 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1021 / 3200 : ℝ) - Real.pi * Real.exp (511 / 400 : ℝ)) := by
    rw [show (1021 / 3200 : ℝ) - Real.pi * Real.exp (511 / 400 : ℝ) =
      -(Real.pi * Real.exp (511 / 400 : ℝ) - (1021 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1021 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1021 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1021_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71328166615621 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1021_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1021 / 1600 : ℝ) (511 / 800 : ℝ) ≤ (157047803 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (511 / 400 : ℝ)) (22541931041529809 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (511 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1021_product_upper
  have hD : (562469463699799 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1021 / 800 : ℝ) - (511 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1021_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1021_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1021 / 800 : ℝ) - (511 / 1600 : ℝ)) ≤
      (1 / (562469463699799 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (562469463699799 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((511 / 1600 : ℝ) - Real.pi * Real.exp (1021 / 800 : ℝ)) ≤
      (2 / (562469463699799 / 10000000000 : ℝ) : ℝ) := by
    rw [show (511 / 1600 : ℝ) - Real.pi * Real.exp (1021 / 800 : ℝ) =
      -(Real.pi * Real.exp (1021 / 800 : ℝ) - (511 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22541931041529809 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (22541931041529809 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1021_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1021 / 1600 : ℝ) (511 / 800 : ℝ)) :
    (4811917 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (157047803 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1021_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1021_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1022_leftExp :
    (17938296781 / 5000000000 : ℝ) ≤ Real.exp (511 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (511 / 400 : ℝ) (520364732013 / 500000000000 : ℝ)
    (17938296781 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1022_rightExp :
    Real.exp (1023 / 800 : ℝ) ≤ (35921467347 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1023 / 800 : ℝ) (260192529579 / 250000000000 : ℝ)
    (35921467347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1022_denomUpper :
    Real.exp (109656880367063771 / 10000000000000000 : ℝ) ≤ (289272939618869 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (109656880367063771 / 10000000000000000 : ℝ)
    (1408714732069 / 1000000000000 : ℝ) (289272939618869 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1022_denomLower :
    (114053351407303 / 2000000000 : ℝ) ≤ Real.exp (6844546520101919 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6844546520101919 / 625000000000000 : ℝ) (281616070883 /
    200000000000 : ℝ) (114053351407303 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1022_product_lower :
    (7044351207601919 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (511 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1022_leftExp
    (by norm_num : (0 : ℝ) ≤ (17938296781 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1022_product_upper :
    Real.pi * Real.exp (1023 / 800 : ℝ) ≤ (112850630367063771 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1022_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1022_endpointLower :
    (152282671 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (511 / 800 : ℝ) (1023 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7044351207601919 / 625000000000000 : ℝ) (Real.pi * Real.exp (511 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1022_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1023 / 800 : ℝ) - (511 / 1600 : ℝ)) ≤
      (289272939618869 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1022_denomUpper
    linarith [hpThetaJensenCell1022_product_upper]
  have hi : (1 / (289272939618869 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1023 / 800 : ℝ) - (511 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (289272939618869 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (289272939618869 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((511 / 1600 : ℝ) - Real.pi * Real.exp (1023 / 800 : ℝ)) := by
    rw [show (511 / 1600 : ℝ) - Real.pi * Real.exp (1023 / 800 : ℝ) =
      -(Real.pi * Real.exp (1023 / 800 : ℝ) - (511 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (511 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (511 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1022_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (289272939618869 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1022_endpointUpper :
    hpThetaJensenKernelEndpointUpper (511 / 800 : ℝ) (1023 / 1600 : ℝ) ≤ (77658997 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1023 / 800 : ℝ)) (112850630367063771 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1023 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1022_product_upper
  have hD : (114053351407303 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (511 / 400 : ℝ) - (1023 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1022_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1022_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (511 / 400 : ℝ) - (1023 / 3200 : ℝ)) ≤
      (1 / (114053351407303 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (114053351407303 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1023 / 3200 : ℝ) - Real.pi * Real.exp (511 / 400 : ℝ)) ≤
      (2 / (114053351407303 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1023 / 3200 : ℝ) - Real.pi * Real.exp (511 / 400 : ℝ) =
      -(Real.pi * Real.exp (511 / 400 : ℝ) - (1023 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (112850630367063771 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (112850630367063771 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1022_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (511 / 800 : ℝ) (1023 / 1600 : ℝ)) :
    (152282671 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (77658997 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1022_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1022_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1023_leftExp :
    (7184293469 / 2000000000 : ℝ) ≤ Real.exp (1023 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1023 / 800 : ℝ) (208154023663 / 200000000000 : ℝ)
    (7184293469 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1023_rightExp :
    Real.exp (32 / 25 : ℝ) ≤ (35966397257 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32 / 25 : ℝ) (1040810774193 / 1000000000000 : ℝ)
    (35966397257 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1023_denomUpper :
    Real.exp (109794906857810401 / 10000000000000000 : ℝ) ≤ (4582708669607 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109794906857810401 / 10000000000000000 : ℝ)
    (1409322487979 / 1000000000000 : ℝ) (4582708669607 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1023_denomLower :
    (7227279046791 / 125000000 : ℝ) ≤ Real.exp (2741264860982831 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2741264860982831 / 250000000000000 : ℝ) (704343530109 /
    500000000000 : ℝ) (7227279046791 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1023_product_lower :
    (2821264860982831 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1023 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1023_leftExp
    (by norm_num : (0 : ℝ) ≤ (7184293469 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1023_product_upper :
    Real.pi * Real.exp (32 / 25 : ℝ) ≤ (112991781857810401 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1023_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1023_endpointLower :
    (3765001 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1023 / 1600 : ℝ) (16 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2821264860982831 / 250000000000000 : ℝ) (Real.pi * Real.exp (1023 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1023_product_lower
  have hD : Real.exp (Real.pi * Real.exp (32 / 25 : ℝ) - (1023 / 3200 : ℝ)) ≤
      (4582708669607 / 78125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1023_denomUpper
    linarith [hpThetaJensenCell1023_product_upper]
  have hi : (1 / (4582708669607 / 78125000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (32 / 25 : ℝ) - (1023 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4582708669607 / 78125000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4582708669607 / 78125000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1023 / 3200 : ℝ) - Real.pi * Real.exp (32 / 25 : ℝ)) := by
    rw [show (1023 / 3200 : ℝ) - Real.pi * Real.exp (32 / 25 : ℝ) =
      -(Real.pi * Real.exp (32 / 25 : ℝ) - (1023 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1023 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1023 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1023_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4582708669607 / 78125000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1023_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1023 / 1600 : ℝ) (16 / 25 : ℝ) ≤ (153604491 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (32 / 25 : ℝ)) (112991781857810401 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (16 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1023_product_upper
  have hD : (7227279046791 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1023 / 800 : ℝ) - (8 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell1023_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1023_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1023 / 800 : ℝ) - (8 / 25 : ℝ)) ≤
      (1 / (7227279046791 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7227279046791 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((8 / 25 : ℝ) - Real.pi * Real.exp (1023 / 800 : ℝ)) ≤
      (2 / (7227279046791 / 125000000 : ℝ) : ℝ) := by
    rw [show (8 / 25 : ℝ) - Real.pi * Real.exp (1023 / 800 : ℝ) =
      -(Real.pi * Real.exp (1023 / 800 : ℝ) - (8 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (112991781857810401 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (112991781857810401 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1023_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1023 / 1600 : ℝ) (16 / 25 : ℝ)) :
    (3765001 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (153604491 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1023_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1023_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1024_leftExp :
    (7193279451 / 2000000000 : ℝ) ≤ Real.exp (32 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (32 / 25 : ℝ) (65050673387 / 62500000000 : ℝ) (7193279451
    / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1024_rightExp :
    Real.exp (41 / 32 : ℝ) ≤ (9002845841 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 32 : ℝ) (520425715829 / 500000000000 : ℝ)
    (9002845841 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1024_denomUpper :
    Real.exp (27483277474164713 / 2500000000000000 : ℝ) ≤ (594749794515779 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (27483277474164713 / 2500000000000000 : ℝ) (1409931283967
    / 1000000000000 : ℝ) (594749794515779 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1024_denomLower :
    (732772623439 / 12500000 : ℝ) ≤ Real.exp (2744715522128249 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2744715522128249 / 250000000000000 : ℝ) (1409294803991 /
    1000000000000 : ℝ) (732772623439 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1024_product_lower :
    (2824793647128249 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (32 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1024_leftExp
    (by norm_num : (0 : ℝ) ≤ (7193279451 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1024_product_upper :
    Real.pi * Real.exp (41 / 32 : ℝ) ≤ (28283277474164713 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1024_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1024_endpointLower :
    (14893333 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (16 / 25 : ℝ) (41 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2824793647128249 / 250000000000000 : ℝ) (Real.pi * Real.exp (32 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1024_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 32 : ℝ) - (8 / 25 : ℝ)) ≤
      (594749794515779 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1024_denomUpper
    linarith [hpThetaJensenCell1024_product_upper]
  have hi : (1 / (594749794515779 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 32 : ℝ) - (8 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (594749794515779 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (594749794515779 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((8 / 25 : ℝ) - Real.pi * Real.exp (41 / 32 : ℝ)) := by
    rw [show (8 / 25 : ℝ) - Real.pi * Real.exp (41 / 32 : ℝ) =
      -(Real.pi * Real.exp (41 / 32 : ℝ) - (8 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (32 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (32 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1024_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (594749794515779 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1024_endpointUpper :
    hpThetaJensenKernelEndpointUpper (16 / 25 : ℝ) (41 / 64 : ℝ) ≤ (151907171 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 32 : ℝ)) (28283277474164713 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1024_product_upper
  have hD : (732772623439 / 12500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (32 / 25 : ℝ) - (41 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1024_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1024_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (32 / 25 : ℝ) - (41 / 128 : ℝ)) ≤
      (1 / (732772623439 / 12500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (732772623439 / 12500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 128 : ℝ) - Real.pi * Real.exp (32 / 25 : ℝ)) ≤
      (2 / (732772623439 / 12500000 : ℝ) : ℝ) := by
    rw [show (41 / 128 : ℝ) - Real.pi * Real.exp (32 / 25 : ℝ) =
      -(Real.pi * Real.exp (32 / 25 : ℝ) - (41 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28283277474164713 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (28283277474164713 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1024_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (16 / 25 : ℝ) (41 / 64 : ℝ)) :
    (14893333 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (151907171 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1024_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1024_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1025_leftExp :
    (18005691681 / 5000000000 : ℝ) ≤ Real.exp (41 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 32 : ℝ) (1040851431657 / 1000000000000 : ℝ)
    (18005691681 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1025_rightExp :
    Real.exp (513 / 400 : ℝ) ≤ (36056425739 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (513 / 400 : ℝ) (1040892090711 / 1000000000000 : ℝ)
    (36056425739 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1025_denomUpper :
    Real.exp (110071489706662227 / 10000000000000000 : ℝ) ≤ (60303713867983 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (110071489706662227 / 10000000000000000 : ℝ)
    (705270561069 / 500000000000 : ℝ) (60303713867983 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1025_denomLower :
    (29718802560861 / 500000000 : ℝ) ≤ Real.exp (6870426492437019 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6870426492437019 / 625000000000000 : ℝ) (1409903587823 /
    1000000000000 : ℝ) (29718802560861 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1025_product_lower :
    (7070817117437019 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1025_leftExp
    (by norm_num : (0 : ℝ) ≤ (18005691681 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1025_product_upper :
    Real.pi * Real.exp (513 / 400 : ℝ) ≤ (113274614706662227 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1025_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1025_endpointLower :
    (73641211 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 64 : ℝ) (513 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7070817117437019 / 625000000000000 : ℝ) (Real.pi * Real.exp (41 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1025_product_lower
  have hD : Real.exp (Real.pi * Real.exp (513 / 400 : ℝ) - (41 / 128 : ℝ)) ≤
      (60303713867983 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1025_denomUpper
    linarith [hpThetaJensenCell1025_product_upper]
  have hi : (1 / (60303713867983 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (513 / 400 : ℝ) - (41 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (60303713867983 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (60303713867983 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 128 : ℝ) - Real.pi * Real.exp (513 / 400 : ℝ)) := by
    rw [show (41 / 128 : ℝ) - Real.pi * Real.exp (513 / 400 : ℝ) =
      -(Real.pi * Real.exp (513 / 400 : ℝ) - (41 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1025_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (60303713867983 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1025_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 64 : ℝ) (513 / 800 : ℝ) ≤ (150225913 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (513 / 400 : ℝ)) (113274614706662227 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (513 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1025_product_upper
  have hD : (29718802560861 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 32 : ℝ) - (513 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1025_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1025_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 32 : ℝ) - (513 / 1600 : ℝ)) ≤
      (1 / (29718802560861 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29718802560861 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((513 / 1600 : ℝ) - Real.pi * Real.exp (41 / 32 : ℝ)) ≤
      (2 / (29718802560861 / 500000000 : ℝ) : ℝ) := by
    rw [show (513 / 1600 : ℝ) - Real.pi * Real.exp (41 / 32 : ℝ) =
      -(Real.pi * Real.exp (41 / 32 : ℝ) - (513 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (113274614706662227 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (113274614706662227 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1025_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 64 : ℝ) (513 / 800 : ℝ)) :
    (73641211 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (150225913 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1025_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1025_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1026_leftExp :
    (4507053217 / 1250000000 : ℝ) ≤ Real.exp (513 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (513 / 400 : ℝ) (104089209071 / 100000000000 : ℝ)
    (4507053217 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1026_rightExp :
    Real.exp (1027 / 800 : ℝ) ≤ (36101524451 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1027 / 800 : ℝ) (130116593919 / 125000000000 : ℝ)
    (36101524451 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1026_denomUpper :
    Real.exp (110210046504590443 / 10000000000000000 : ℝ) ≤ (611450781949237 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (110210046504590443 / 10000000000000000 : ℝ)
    (1411152004573 / 1000000000000 : ℝ) (611450781949237 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1026_denomLower :
    (60265818467257 / 1000000000 : ℝ) ≤ Real.exp (1719768806887683 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1719768806887683 / 156250000000000 : ℝ) (705256706901 /
    500000000000 : ℝ) (60265818467257 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1026_product_lower :
    (1769915291262683 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (513 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1026_leftExp
    (by norm_num : (0 : ℝ) ≤ (4507053217 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1026_product_upper :
    Real.pi * Real.exp (1027 / 800 : ℝ) ≤ (113416296504590443 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1026_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1026_endpointLower :
    (36411799 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (513 / 800 : ℝ) (1027 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1769915291262683 / 156250000000000 : ℝ) (Real.pi * Real.exp (513 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1026_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1027 / 800 : ℝ) - (513 / 1600 : ℝ)) ≤
      (611450781949237 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1026_denomUpper
    linarith [hpThetaJensenCell1026_product_upper]
  have hi : (1 / (611450781949237 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1027 / 800 : ℝ) - (513 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (611450781949237 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (611450781949237 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((513 / 1600 : ℝ) - Real.pi * Real.exp (1027 / 800 : ℝ)) := by
    rw [show (513 / 1600 : ℝ) - Real.pi * Real.exp (1027 / 800 : ℝ) =
      -(Real.pi * Real.exp (1027 / 800 : ℝ) - (513 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (513 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (513 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1026_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (611450781949237 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1026_endpointUpper :
    hpThetaJensenKernelEndpointUpper (513 / 800 : ℝ) (1027 / 1600 : ℝ) ≤ (37140149 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1027 / 800 : ℝ)) (113416296504590443 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1027 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1026_product_upper
  have hD : (60265818467257 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (513 / 400 : ℝ) - (1027 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1026_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1026_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (513 / 400 : ℝ) - (1027 / 3200 : ℝ)) ≤
      (1 / (60265818467257 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (60265818467257 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1027 / 3200 : ℝ) - Real.pi * Real.exp (513 / 400 : ℝ)) ≤
      (2 / (60265818467257 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1027 / 3200 : ℝ) - Real.pi * Real.exp (513 / 400 : ℝ) =
      -(Real.pi * Real.exp (513 / 400 : ℝ) - (1027 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (113416296504590443 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (113416296504590443 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1026_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (513 / 800 : ℝ) (1027 / 1600 : ℝ)) :
    (36411799 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (37140149 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1026_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1026_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1027_leftExp :
    (36101524449 / 10000000000 : ℝ) ≤ Real.exp (1027 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1027 / 800 : ℝ) (1040932751351 / 1000000000000 : ℝ)
    (36101524449 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1027_rightExp :
    Real.exp (257 / 200 : ℝ) ≤ (36146679573 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (257 / 200 : ℝ) (520486706791 / 500000000000 : ℝ)
    (36146679573 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1027_denomUpper :
    Real.exp (110348780519779789 / 10000000000000000 : ℝ) ≤ (12399856011449 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (110348780519779789 / 10000000000000000 : ℝ)
    (1411763933411 / 1000000000000 : ℝ) (12399856011449 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1027_denomLower :
    (122213307633817 / 2000000000 : ℝ) ≤ Real.exp (13775470049597851 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13775470049597851 / 1250000000000000 : ℝ) (352781071013
    / 250000000000 : ℝ) (122213307633817 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1027_product_lower :
    (14177032549597851 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1027 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1027_leftExp
    (by norm_num : (0 : ℝ) ≤ (36101524449 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1027_product_upper :
    Real.pi * Real.exp (257 / 200 : ℝ) ≤ (113558155519779789 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1027_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1027_endpointLower :
    (144027533 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1027 / 1600 : ℝ) (257 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14177032549597851 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1027 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1027_product_lower
  have hD : Real.exp (Real.pi * Real.exp (257 / 200 : ℝ) - (1027 / 3200 : ℝ)) ≤
      (12399856011449 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1027_denomUpper
    linarith [hpThetaJensenCell1027_product_upper]
  have hi : (1 / (12399856011449 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (257 / 200 : ℝ) - (1027 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12399856011449 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12399856011449 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1027 / 3200 : ℝ) - Real.pi * Real.exp (257 / 200 : ℝ)) := by
    rw [show (1027 / 3200 : ℝ) - Real.pi * Real.exp (257 / 200 : ℝ) =
      -(Real.pi * Real.exp (257 / 200 : ℝ) - (1027 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1027 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1027 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1027_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12399856011449 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1027_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1027 / 1600 : ℝ) (257 / 400 : ℝ) ≤ (146911099 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (257 / 200 : ℝ)) (113558155519779789 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (257 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1027_product_upper
  have hD : (122213307633817 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1027 / 800 : ℝ) - (257 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1027_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1027_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1027 / 800 : ℝ) - (257 / 800 : ℝ)) ≤
      (1 / (122213307633817 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (122213307633817 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((257 / 800 : ℝ) - Real.pi * Real.exp (1027 / 800 : ℝ)) ≤
      (2 / (122213307633817 / 2000000000 : ℝ) : ℝ) := by
    rw [show (257 / 800 : ℝ) - Real.pi * Real.exp (1027 / 800 : ℝ) =
      -(Real.pi * Real.exp (1027 / 800 : ℝ) - (257 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (113558155519779789 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (113558155519779789 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1027_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1027 / 1600 : ℝ) (257 / 400 : ℝ)) :
    (144027533 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (146911099 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1027_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1027_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1028_leftExp :
    (36146679571 / 10000000000 : ℝ) ≤ Real.exp (257 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (257 / 200 : ℝ) (1040973413581 / 1000000000000 : ℝ)
    (36146679571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1028_rightExp :
    Real.exp (1029 / 800 : ℝ) ≤ (18095945587 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1029 / 800 : ℝ) (5205070387 / 5000000000 : ℝ)
    (18095945587 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1028_denomUpper :
    Real.exp (55243845984500091 / 5000000000000000 : ℝ) ≤ (157166326622421 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55243845984500091 / 5000000000000000 : ℝ) (706188455371
    / 500000000000 : ℝ) (157166326622421 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1028_denomLower :
    (619603186074937 / 10000000000 : ℝ) ≤ Real.exp (13792811795852129 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13792811795852129 / 1250000000000000 : ℝ) (141173620067
    / 100000000000 : ℝ) (619603186074937 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1028_product_lower :
    (14194764920852129 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (257 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1028_leftExp
    (by norm_num : (0 : ℝ) ≤ (36146679571 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1028_product_upper :
    Real.pi * Real.exp (1029 / 800 : ℝ) ≤ (56850095984500091 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1028_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1028_endpointLower :
    (28484663 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (257 / 400 : ℝ) (1029 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14194764920852129 / 1250000000000000 : ℝ) (Real.pi * Real.exp (257 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1028_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1029 / 800 : ℝ) - (257 / 800 : ℝ)) ≤
      (157166326622421 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1028_denomUpper
    linarith [hpThetaJensenCell1028_product_upper]
  have hi : (1 / (157166326622421 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1029 / 800 : ℝ) - (257 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (157166326622421 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (157166326622421 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((257 / 800 : ℝ) - Real.pi * Real.exp (1029 / 800 : ℝ)) := by
    rw [show (257 / 800 : ℝ) - Real.pi * Real.exp (1029 / 800 : ℝ) =
      -(Real.pi * Real.exp (1029 / 800 : ℝ) - (257 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (257 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (257 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1028_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (157166326622421 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1028_endpointUpper :
    hpThetaJensenKernelEndpointUpper (257 / 400 : ℝ) (1029 / 1600 : ℝ) ≤ (72638651 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1029 / 800 : ℝ)) (56850095984500091 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1029 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1028_product_upper
  have hD : (619603186074937 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (257 / 200 : ℝ) - (1029 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1028_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1028_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (257 / 200 : ℝ) - (1029 / 3200 : ℝ)) ≤
      (1 / (619603186074937 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (619603186074937 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1029 / 3200 : ℝ) - Real.pi * Real.exp (257 / 200 : ℝ)) ≤
      (2 / (619603186074937 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1029 / 3200 : ℝ) - Real.pi * Real.exp (257 / 200 : ℝ) =
      -(Real.pi * Real.exp (257 / 200 : ℝ) - (1029 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56850095984500091 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (56850095984500091 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1028_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (257 / 400 : ℝ) (1029 / 1600 : ℝ)) :
    (28484663 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (72638651 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1028_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1028_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1029_leftExp :
    (36191891171 / 10000000000 : ℝ) ≤ Real.exp (1029 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1029 / 800 : ℝ) (1041014077399 / 1000000000000 : ℝ)
    (36191891171 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1029_rightExp :
    Real.exp (103 / 80 : ℝ) ≤ (1449486373 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (103 / 80 : ℝ) (1041054742807 / 1000000000000 : ℝ)
    (1449486373 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1029_denomUpper :
    Real.exp (4425071243012189 / 400000000000000 : ℝ) ≤ (637470449071199 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4425071243012189 / 400000000000000 : ℝ) (353247734671 /
    250000000000 : ℝ) (637470449071199 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1029_denomLower :
    (25130809559759 / 400000000 : ℝ) ≤ Real.exp (13810175720960529 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13810175720960529 / 1250000000000000 : ℝ) (706174582873
    / 500000000000 : ℝ) (25130809559759 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1029_product_lower :
    (14212519470960529 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1029 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1029_leftExp
    (by norm_num : (0 : ℝ) ≤ (36191891171 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1029_product_upper :
    Real.pi * Real.exp (103 / 80 : ℝ) ≤ (4553696243012189 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1029_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1029_endpointLower :
    (5633377 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (1029 / 1600 : ℝ) (103 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14212519470960529 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1029 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1029_product_lower
  have hD : Real.exp (Real.pi * Real.exp (103 / 80 : ℝ) - (1029 / 3200 : ℝ)) ≤
      (637470449071199 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1029_denomUpper
    linarith [hpThetaJensenCell1029_product_upper]
  have hi : (1 / (637470449071199 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (103 / 80 : ℝ) - (1029 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (637470449071199 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (637470449071199 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1029 / 3200 : ℝ) - Real.pi * Real.exp (103 / 80 : ℝ)) := by
    rw [show (1029 / 3200 : ℝ) - Real.pi * Real.exp (103 / 80 : ℝ) =
      -(Real.pi * Real.exp (103 / 80 : ℝ) - (1029 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1029 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1029 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1029_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (637470449071199 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1029_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1029 / 1600 : ℝ) (103 / 160 : ℝ) ≤ (71829543 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (103 / 80 : ℝ)) (4553696243012189 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (103 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1029_product_upper
  have hD : (25130809559759 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1029 / 800 : ℝ) - (103 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1029_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1029_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1029 / 800 : ℝ) - (103 / 320 : ℝ)) ≤
      (1 / (25130809559759 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (25130809559759 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((103 / 320 : ℝ) - Real.pi * Real.exp (1029 / 800 : ℝ)) ≤
      (2 / (25130809559759 / 400000000 : ℝ) : ℝ) := by
    rw [show (103 / 320 : ℝ) - Real.pi * Real.exp (1029 / 800 : ℝ) =
      -(Real.pi * Real.exp (1029 / 800 : ℝ) - (103 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4553696243012189 / 400000000000000 : ℝ) ^ 2 - 6 *
      (4553696243012189 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1029_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1029 / 1600 : ℝ) (103 / 160 : ℝ)) :
    (5633377 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (71829543 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1029_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1029_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1030_leftExp :
    (36237159323 / 10000000000 : ℝ) ≤ Real.exp (103 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (103 / 80 : ℝ) (520527371403 / 500000000000 : ℝ)
    (36237159323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1030_rightExp :
    Real.exp (1031 / 800 : ℝ) ≤ (283456907 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1031 / 800 : ℝ) (520547704901 / 500000000000 : ℝ)
    (283456907 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1030_denomUpper :
    Real.exp (865359750457851 / 78125000000000 : ℝ) ≤ (25856416612731 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (865359750457851 / 78125000000000 : ℝ) (353401504837 /
    250000000000 : ℝ) (25856416612731 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1030_denomLower :
    (318534922771153 / 5000000000 : ℝ) ≤ Real.exp (13827561853982777 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13827561853982777 / 1250000000000000 : ℝ) (2207754971 /
    1562500000 : ℝ) (318534922771153 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1030_product_lower :
    (14230296228982777 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (103 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1030_leftExp
    (by norm_num : (0 : ℝ) ≤ (36237159323 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1030_product_upper :
    Real.pi * Real.exp (1031 / 800 : ℝ) ≤ (890506234832851 / 78125000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1030_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1030_endpointLower :
    (69630373 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (103 / 160 : ℝ) (1031 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14230296228982777 / 1250000000000000 : ℝ) (Real.pi * Real.exp (103 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1030_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1031 / 800 : ℝ) - (103 / 320 : ℝ)) ≤
      (25856416612731 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1030_denomUpper
    linarith [hpThetaJensenCell1030_product_upper]
  have hi : (1 / (25856416612731 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1031 / 800 : ℝ) - (103 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (25856416612731 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (25856416612731 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((103 / 320 : ℝ) - Real.pi * Real.exp (1031 / 800 : ℝ)) := by
    rw [show (103 / 320 : ℝ) - Real.pi * Real.exp (1031 / 800 : ℝ) =
      -(Real.pi * Real.exp (1031 / 800 : ℝ) - (103 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (103 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (103 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1030_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (25856416612731 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1030_endpointUpper :
    hpThetaJensenKernelEndpointUpper (103 / 160 : ℝ) (1031 / 1600 : ℝ) ≤ (142056333 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1031 / 800 : ℝ)) (890506234832851 / 78125000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1031 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1030_product_upper
  have hD : (318534922771153 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (103 / 80 : ℝ) - (1031 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1030_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1030_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (103 / 80 : ℝ) - (1031 / 3200 : ℝ)) ≤
      (1 / (318534922771153 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (318534922771153 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1031 / 3200 : ℝ) - Real.pi * Real.exp (103 / 80 : ℝ)) ≤
      (2 / (318534922771153 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1031 / 3200 : ℝ) - Real.pi * Real.exp (103 / 80 : ℝ) =
      -(Real.pi * Real.exp (103 / 80 : ℝ) - (1031 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (890506234832851 / 78125000000000 : ℝ) ^ 2 - 6 *
      (890506234832851 / 78125000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1030_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (103 / 160 : ℝ) (1031 / 1600 : ℝ)) :
    (69630373 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (142056333 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1030_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1030_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1031_leftExp :
    (18141242047 / 5000000000 : ℝ) ≤ Real.exp (1031 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1031 / 800 : ℝ) (1041095409801 / 1000000000000 : ℝ)
    (18141242047 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1031_rightExp :
    Real.exp (129 / 100 : ℝ) ≤ (36327865559 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (129 / 100 : ℝ) (520568039193 / 500000000000 : ℝ)
    (36327865559 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1031_denomUpper :
    Real.exp (110905493145095487 / 10000000000000000 : ℝ) ≤ (655487431119677 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (110905493145095487 / 10000000000000000 : ℝ)
    (353555538719 / 250000000000 : ℝ) (655487431119677 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1031_denomLower :
    (646004190747669 / 10000000000 : ℝ) ≤ Real.exp (6922485110614853 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6922485110614853 / 625000000000000 : ℝ) (1413578249821 /
    1000000000000 : ℝ) (646004190747669 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1031_product_lower :
    (7124047610614853 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1031 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1031_leftExp
    (by norm_num : (0 : ℝ) ≤ (18141242047 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1031_product_upper :
    Real.pi * Real.exp (129 / 100 : ℝ) ≤ (114127368145095487 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1031_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1031_endpointLower :
    (137702161 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1031 / 1600 : ℝ) (129 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7124047610614853 / 625000000000000 : ℝ) (Real.pi * Real.exp (1031 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1031_product_lower
  have hD : Real.exp (Real.pi * Real.exp (129 / 100 : ℝ) - (1031 / 3200 : ℝ)) ≤
      (655487431119677 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1031_denomUpper
    linarith [hpThetaJensenCell1031_product_upper]
  have hi : (1 / (655487431119677 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (129 / 100 : ℝ) - (1031 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (655487431119677 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (655487431119677 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1031 / 3200 : ℝ) - Real.pi * Real.exp (129 / 100 : ℝ)) := by
    rw [show (1031 / 3200 : ℝ) - Real.pi * Real.exp (129 / 100 : ℝ) =
      -(Real.pi * Real.exp (129 / 100 : ℝ) - (1031 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1031 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1031 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1031_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (655487431119677 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1031_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1031 / 1600 : ℝ) (129 / 200 : ℝ) ≤ (35117231 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (129 / 100 : ℝ)) (114127368145095487 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (129 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1031_product_upper
  have hD : (646004190747669 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1031 / 800 : ℝ) - (129 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1031_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1031_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1031 / 800 : ℝ) - (129 / 400 : ℝ)) ≤
      (1 / (646004190747669 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (646004190747669 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((129 / 400 : ℝ) - Real.pi * Real.exp (1031 / 800 : ℝ)) ≤
      (2 / (646004190747669 / 10000000000 : ℝ) : ℝ) := by
    rw [show (129 / 400 : ℝ) - Real.pi * Real.exp (1031 / 800 : ℝ) =
      -(Real.pi * Real.exp (1031 / 800 : ℝ) - (129 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (114127368145095487 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (114127368145095487 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1031_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1031 / 1600 : ℝ) (129 / 200 : ℝ)) :
    (137702161 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (35117231 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1031_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1031_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1032_leftExp :
    (36327865557 / 10000000000 : ℝ) ≤ Real.exp (129 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (129 / 100 : ℝ) (208227215677 / 200000000000 : ℝ)
    (36327865557 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1032_rightExp :
    Real.exp (1033 / 800 : ℝ) ≤ (36373303783 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1033 / 800 : ℝ) (520588374279 / 500000000000 : ℝ)
    (36373303783 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1032_denomUpper :
    Real.exp (111045116551546319 / 10000000000000000 : ℝ) ≤ (332351880486943 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (111045116551546319 / 10000000000000000 : ℝ)
    (1414839347373 / 1000000000000 : ℝ) (332351880486943 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1032_denomLower :
    (655075499298003 / 10000000000 : ℝ) ≤ Real.exp (13862400851368343 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13862400851368343 / 1250000000000000 : ℝ) (282838874609
    / 200000000000 : ℝ) (655075499298003 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1032_product_lower :
    (14265916476368343 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (129 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1032_leftExp
    (by norm_num : (0 : ℝ) ≤ (36327865557 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1032_product_upper :
    Real.pi * Real.exp (1033 / 800 : ℝ) ≤ (114270116551546319 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1032_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1032_endpointLower :
    (68079277 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (129 / 200 : ℝ) (1033 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14265916476368343 / 1250000000000000 : ℝ) (Real.pi * Real.exp (129 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1032_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1033 / 800 : ℝ) - (129 / 400 : ℝ)) ≤
      (332351880486943 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1032_denomUpper
    linarith [hpThetaJensenCell1032_product_upper]
  have hi : (1 / (332351880486943 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1033 / 800 : ℝ) - (129 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (332351880486943 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (332351880486943 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((129 / 400 : ℝ) - Real.pi * Real.exp (1033 / 800 : ℝ)) := by
    rw [show (129 / 400 : ℝ) - Real.pi * Real.exp (1033 / 800 : ℝ) =
      -(Real.pi * Real.exp (1033 / 800 : ℝ) - (129 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (129 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (129 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1032_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (332351880486943 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1032_endpointUpper :
    hpThetaJensenKernelEndpointUpper (129 / 200 : ℝ) (1033 / 1600 : ℝ) ≤ (69448371 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1033 / 800 : ℝ)) (114270116551546319 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1033 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1032_product_upper
  have hD : (655075499298003 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (129 / 100 : ℝ) - (1033 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1032_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1032_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (129 / 100 : ℝ) - (1033 / 3200 : ℝ)) ≤
      (1 / (655075499298003 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (655075499298003 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1033 / 3200 : ℝ) - Real.pi * Real.exp (129 / 100 : ℝ)) ≤
      (2 / (655075499298003 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1033 / 3200 : ℝ) - Real.pi * Real.exp (129 / 100 : ℝ) =
      -(Real.pi * Real.exp (129 / 100 : ℝ) - (1033 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (114270116551546319 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (114270116551546319 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1032_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (129 / 200 : ℝ) (1033 / 1600 : ℝ)) :
    (68079277 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (69448371 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1032_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1032_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1033_leftExp :
    (36373303781 / 10000000000 : ℝ) ≤ Real.exp (1033 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1033 / 800 : ℝ) (1041176748557 / 1000000000000 : ℝ)
    (36373303781 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1033_rightExp :
    Real.exp (517 / 400 : ℝ) ≤ (36418798841 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (517 / 400 : ℝ) (1041217420319 / 1000000000000 : ℝ)
    (36418798841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1033_denomUpper :
    Real.exp (111184918507293713 / 10000000000000000 : ℝ) ≤ (674061710111681 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (111184918507293713 / 10000000000000000 : ℝ)
    (1415457599001 / 1000000000000 : ℝ) (674061710111681 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1033_denomLower :
    (332143017126183 / 5000000000 : ℝ) ≤ Real.exp (13879853771494919 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13879853771494919 / 1250000000000000 : ℝ) (22106430519 /
    15625000000 : ℝ) (332143017126183 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1033_product_lower :
    (14283760021494919 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1033 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1033_leftExp
    (by norm_num : (0 : ℝ) ≤ (36373303781 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1033_product_upper :
    Real.pi * Real.exp (517 / 400 : ℝ) ≤ (114413043507293713 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1033_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1033_endpointLower :
    (13462981 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1033 / 1600 : ℝ) (517 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14283760021494919 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1033 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1033_product_lower
  have hD : Real.exp (Real.pi * Real.exp (517 / 400 : ℝ) - (1033 / 3200 : ℝ)) ≤
      (674061710111681 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1033_denomUpper
    linarith [hpThetaJensenCell1033_product_upper]
  have hi : (1 / (674061710111681 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (517 / 400 : ℝ) - (1033 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (674061710111681 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (674061710111681 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1033 / 3200 : ℝ) - Real.pi * Real.exp (517 / 400 : ℝ)) := by
    rw [show (1033 / 3200 : ℝ) - Real.pi * Real.exp (517 / 400 : ℝ) =
      -(Real.pi * Real.exp (517 / 400 : ℝ) - (1033 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1033 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1033 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1033_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (674061710111681 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1033_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1033 / 1600 : ℝ) (517 / 800 : ℝ) ≤ (13733967 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (517 / 400 : ℝ)) (114413043507293713 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (517 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1033_product_upper
  have hD : (332143017126183 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1033 / 800 : ℝ) - (517 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1033_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1033_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1033 / 800 : ℝ) - (517 / 1600 : ℝ)) ≤
      (1 / (332143017126183 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (332143017126183 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((517 / 1600 : ℝ) - Real.pi * Real.exp (1033 / 800 : ℝ)) ≤
      (2 / (332143017126183 / 5000000000 : ℝ) : ℝ) := by
    rw [show (517 / 1600 : ℝ) - Real.pi * Real.exp (1033 / 800 : ℝ) =
      -(Real.pi * Real.exp (1033 / 800 : ℝ) - (517 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (114413043507293713 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (114413043507293713 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1033_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1033 / 1600 : ℝ) (517 / 800 : ℝ)) :
    (13462981 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13733967 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1033_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1033_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1034_leftExp :
    (36418798839 / 10000000000 : ℝ) ≤ Real.exp (517 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (517 / 400 : ℝ) (520608710159 / 500000000000 : ℝ)
    (36418798839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1034_rightExp :
    Real.exp (207 / 160 : ℝ) ≤ (9116087701 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (207 / 160 : ℝ) (1041258093669 / 1000000000000 : ℝ)
    (9116087701 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1034_denomUpper :
    Real.exp (27831224808847693 / 2500000000000000 : ℝ) ≤ (341781812045843 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27831224808847693 / 2500000000000000 : ℝ) (1416076911901
    / 1000000000000 : ℝ) (341781812045843 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1034_denomLower :
    (67363809942139 / 1000000000 : ℝ) ≤ Real.exp (13897329010276461 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13897329010276461 / 1250000000000000 : ℝ) (707714896249
    / 500000000000 : ℝ) (67363809942139 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1034_product_lower :
    (14301625885276461 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (517 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1034_leftExp
    (by norm_num : (0 : ℝ) ≤ (36418798839 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1034_product_upper :
    Real.pi * Real.exp (207 / 160 : ℝ) ≤ (28639037308847693 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1034_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1034_endpointLower :
    (66557907 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (517 / 800 : ℝ) (207 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14301625885276461 / 1250000000000000 : ℝ) (Real.pi * Real.exp (517 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1034_product_lower
  have hD : Real.exp (Real.pi * Real.exp (207 / 160 : ℝ) - (517 / 1600 : ℝ)) ≤
      (341781812045843 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1034_denomUpper
    linarith [hpThetaJensenCell1034_product_upper]
  have hi : (1 / (341781812045843 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (207 / 160 : ℝ) - (517 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (341781812045843 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (341781812045843 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((517 / 1600 : ℝ) - Real.pi * Real.exp (207 / 160 : ℝ)) := by
    rw [show (517 / 1600 : ℝ) - Real.pi * Real.exp (207 / 160 : ℝ) =
      -(Real.pi * Real.exp (207 / 160 : ℝ) - (517 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (517 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (517 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1034_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (341781812045843 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1034_endpointUpper :
    hpThetaJensenKernelEndpointUpper (517 / 800 : ℝ) (207 / 320 : ℝ) ≤ (135797591 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (207 / 160 : ℝ)) (28639037308847693 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (207 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1034_product_upper
  have hD : (67363809942139 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (517 / 400 : ℝ) - (207 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1034_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1034_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (517 / 400 : ℝ) - (207 / 640 : ℝ)) ≤
      (1 / (67363809942139 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (67363809942139 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((207 / 640 : ℝ) - Real.pi * Real.exp (517 / 400 : ℝ)) ≤
      (2 / (67363809942139 / 1000000000 : ℝ) : ℝ) := by
    rw [show (207 / 640 : ℝ) - Real.pi * Real.exp (517 / 400 : ℝ) =
      -(Real.pi * Real.exp (517 / 400 : ℝ) - (207 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28639037308847693 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (28639037308847693 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1034_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (517 / 800 : ℝ) (207 / 320 : ℝ)) :
    (66557907 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (135797591 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1034_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1034_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1035_leftExp :
    (18232175401 / 5000000000 : ℝ) ≤ Real.exp (207 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (207 / 160 : ℝ) (260314523417 / 250000000000 : ℝ)
    (18232175401 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1035_rightExp :
    Real.exp (259 / 200 : ℝ) ≤ (18254979871 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (259 / 200 : ℝ) (32540586519 / 31250000000 : ℝ)
    (18254979871 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1035_denomUpper :
    Real.exp (55732529477874503 / 5000000000000000 : ℝ) ≤ (21662871552879 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55732529477874503 / 5000000000000000 : ℝ) (1416697288203
    / 1000000000000 : ℝ) (21662871552879 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1035_denomLower :
    (42695877428631 / 625000000 : ℝ) ≤ Real.exp (6957413297797299 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6957413297797299 / 625000000000000 : ℝ) (141604909303 /
    100000000000 : ℝ) (42695877428631 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1035_product_lower :
    (7159757047797299 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (207 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1035_leftExp
    (by norm_num : (0 : ℝ) ≤ (18232175401 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1035_product_upper :
    Real.pi * Real.exp (259 / 200 : ℝ) ≤ (57349716977874503 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1035_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1035_endpointLower :
    (131616453 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (207 / 320 : ℝ) (259 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7159757047797299 / 625000000000000 : ℝ) (Real.pi * Real.exp (207 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1035_product_lower
  have hD : Real.exp (Real.pi * Real.exp (259 / 200 : ℝ) - (207 / 640 : ℝ)) ≤
      (21662871552879 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1035_denomUpper
    linarith [hpThetaJensenCell1035_product_upper]
  have hi : (1 / (21662871552879 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (259 / 200 : ℝ) - (207 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (21662871552879 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (21662871552879 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((207 / 640 : ℝ) - Real.pi * Real.exp (259 / 200 : ℝ)) := by
    rw [show (207 / 640 : ℝ) - Real.pi * Real.exp (259 / 200 : ℝ) =
      -(Real.pi * Real.exp (259 / 200 : ℝ) - (207 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (207 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (207 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1035_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (21662871552879 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1035_endpointUpper :
    hpThetaJensenKernelEndpointUpper (207 / 320 : ℝ) (259 / 400 : ℝ) ≤ (134270391 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (259 / 200 : ℝ)) (57349716977874503 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (259 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1035_product_upper
  have hD : (42695877428631 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (207 / 160 : ℝ) - (259 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1035_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1035_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (207 / 160 : ℝ) - (259 / 800 : ℝ)) ≤
      (1 / (42695877428631 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (42695877428631 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((259 / 800 : ℝ) - Real.pi * Real.exp (207 / 160 : ℝ)) ≤
      (2 / (42695877428631 / 625000000 : ℝ) : ℝ) := by
    rw [show (259 / 800 : ℝ) - Real.pi * Real.exp (207 / 160 : ℝ) =
      -(Real.pi * Real.exp (207 / 160 : ℝ) - (259 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57349716977874503 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (57349716977874503 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1035_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (207 / 320 : ℝ) (259 / 400 : ℝ)) :
    (131616453 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (134270391 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1035_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1035_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1036_leftExp :
    (1825497987 / 500000000 : ℝ) ≤ Real.exp (259 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (259 / 200 : ℝ) (1041298768607 / 1000000000000 : ℝ)
    (1825497987 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1036_rightExp :
    Real.exp (1037 / 800 : ℝ) ≤ (142795413 / 39062500 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1037 / 800 : ℝ) (65083715321 / 62500000000 : ℝ)
    (142795413 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1036_denomUpper :
    Real.exp (435958585537909 / 39062500000000 : ℝ) ≤ (703008936575257 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (435958585537909 / 39062500000000 : ℝ) (1417318730083 /
    1000000000000 : ℝ) (703008936575257 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1036_denomLower :
    (692776237854463 / 10000000000 : ℝ) ≤ Real.exp (696617327746913 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (696617327746913 / 62500000000000 : ℝ) (1416669456943 /
    1000000000000 : ℝ) (692776237854463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1036_product_lower :
    (716871233996913 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (259 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1036_leftExp
    (by norm_num : (0 : ℝ) ≤ (1825497987 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1036_product_upper :
    Real.pi * Real.exp (1037 / 800 : ℝ) ≤ (448605069912909 / 39062500000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1036_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1036_endpointLower :
    (32532903 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (259 / 400 : ℝ) (1037 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (716871233996913 / 62500000000000 : ℝ) (Real.pi * Real.exp (259 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1036_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1037 / 800 : ℝ) - (259 / 800 : ℝ)) ≤
      (703008936575257 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1036_denomUpper
    linarith [hpThetaJensenCell1036_product_upper]
  have hi : (1 / (703008936575257 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1037 / 800 : ℝ) - (259 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (703008936575257 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (703008936575257 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((259 / 800 : ℝ) - Real.pi * Real.exp (1037 / 800 : ℝ)) := by
    rw [show (259 / 800 : ℝ) - Real.pi * Real.exp (1037 / 800 : ℝ) =
      -(Real.pi * Real.exp (1037 / 800 : ℝ) - (259 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (259 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (259 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1036_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (703008936575257 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1036_endpointUpper :
    hpThetaJensenKernelEndpointUpper (259 / 400 : ℝ) (1037 / 1600 : ℝ) ≤ (66378977 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1037 / 800 : ℝ)) (448605069912909 / 39062500000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1037 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1036_product_upper
  have hD : (692776237854463 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (259 / 200 : ℝ) - (1037 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1036_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1036_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (259 / 200 : ℝ) - (1037 / 3200 : ℝ)) ≤
      (1 / (692776237854463 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (692776237854463 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1037 / 3200 : ℝ) - Real.pi * Real.exp (259 / 200 : ℝ)) ≤
      (2 / (692776237854463 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1037 / 3200 : ℝ) - Real.pi * Real.exp (259 / 200 : ℝ) =
      -(Real.pi * Real.exp (259 / 200 : ℝ) - (1037 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (448605069912909 / 39062500000000 : ℝ) ^ 2 - 6 *
      (448605069912909 / 39062500000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1036_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (259 / 400 : ℝ) (1037 / 1600 : ℝ)) :
    (32532903 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (66378977 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1036_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1036_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1037_leftExp :
    (18277812863 / 5000000000 : ℝ) ≤ Real.exp (1037 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1037 / 800 : ℝ) (208267889027 / 200000000000 : ℝ)
    (18277812863 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1037_rightExp :
    Real.exp (519 / 400 : ℝ) ≤ (3660134883 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (519 / 400 : ℝ) (260345030813 / 250000000000 : ℝ)
    (3660134883 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1037_denomUpper :
    Real.exp (11174591627488619 / 1000000000000000 : ℝ) ≤ (28518289452861 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11174591627488619 / 1000000000000000 : ℝ) (1417941239651
    / 1000000000000 : ℝ) (28518289452861 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1037_denomLower :
    (175641781132167 / 2500000000 : ℝ) ≤ Real.exp (6974944458487237 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6974944458487237 / 625000000000000 : ℝ) (354322721603 /
    250000000000 : ℝ) (175641781132167 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1037_product_lower :
    (7177678833487237 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1037 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1037_leftExp
    (by norm_num : (0 : ℝ) ≤ (18277812863 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1037_product_upper :
    Real.pi * Real.exp (519 / 400 : ℝ) ≤ (11498654127488619 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1037_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1037_endpointLower :
    (128661179 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1037 / 1600 : ℝ) (519 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7177678833487237 / 625000000000000 : ℝ) (Real.pi * Real.exp (1037 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1037_product_lower
  have hD : Real.exp (Real.pi * Real.exp (519 / 400 : ℝ) - (1037 / 3200 : ℝ)) ≤
      (28518289452861 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1037_denomUpper
    linarith [hpThetaJensenCell1037_product_upper]
  have hi : (1 / (28518289452861 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (519 / 400 : ℝ) - (1037 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (28518289452861 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (28518289452861 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1037 / 3200 : ℝ) - Real.pi * Real.exp (519 / 400 : ℝ)) := by
    rw [show (1037 / 3200 : ℝ) - Real.pi * Real.exp (519 / 400 : ℝ) =
      -(Real.pi * Real.exp (519 / 400 : ℝ) - (1037 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1037 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1037 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1037_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (28518289452861 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1037_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1037 / 1600 : ℝ) (519 / 800 : ℝ) ≤ (26252033 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (519 / 400 : ℝ)) (11498654127488619 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (519 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1037_product_upper
  have hD : (175641781132167 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1037 / 800 : ℝ) - (519 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1037_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1037_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1037 / 800 : ℝ) - (519 / 1600 : ℝ)) ≤
      (1 / (175641781132167 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (175641781132167 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((519 / 1600 : ℝ) - Real.pi * Real.exp (1037 / 800 : ℝ)) ≤
      (2 / (175641781132167 / 2500000000 : ℝ) : ℝ) := by
    rw [show (519 / 1600 : ℝ) - Real.pi * Real.exp (1037 / 800 : ℝ) =
      -(Real.pi * Real.exp (1037 / 800 : ℝ) - (519 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11498654127488619 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (11498654127488619 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1037_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1037 / 1600 : ℝ) (519 / 800 : ℝ)) :
    (128661179 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (26252033 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1037_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1037_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1038_leftExp :
    (9150337207 / 2500000000 : ℝ) ≤ Real.exp (519 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (519 / 400 : ℝ) (1041380123251 / 1000000000000 : ℝ)
    (9150337207 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1038_rightExp :
    Real.exp (1039 / 800 : ℝ) ≤ (9161782281 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1039 / 800 : ℝ) (520710401479 / 500000000000 : ℝ)
    (9161782281 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1038_denomUpper :
    Real.exp (27971653581513633 / 2500000000000000 : ℝ) ≤ (90382413266047 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27971653581513633 / 2500000000000000 : ℝ) (1418564819133
    / 1000000000000 : ℝ) (90382413266047 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1038_denomLower :
    (178127292230501 / 2500000000 : ℝ) ≤ Real.exp (3491863427101693 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3491863427101693 / 312500000000000 : ℝ) (354478345887 /
    250000000000 : ℝ) (178127292230501 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1038_product_lower :
    (3593328270851693 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (519 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1038_leftExp
    (by norm_num : (0 : ℝ) ≤ (9150337207 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1038_product_upper :
    Real.pi * Real.exp (1039 / 800 : ℝ) ≤ (28782591081513633 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1038_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1038_endpointLower :
    (63602521 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (519 / 800 : ℝ) (1039 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3593328270851693 / 312500000000000 : ℝ) (Real.pi * Real.exp (519 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1038_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1039 / 800 : ℝ) - (519 / 1600 : ℝ)) ≤
      (90382413266047 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1038_denomUpper
    linarith [hpThetaJensenCell1038_product_upper]
  have hi : (1 / (90382413266047 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1039 / 800 : ℝ) - (519 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (90382413266047 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (90382413266047 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((519 / 1600 : ℝ) - Real.pi * Real.exp (1039 / 800 : ℝ)) := by
    rw [show (519 / 1600 : ℝ) - Real.pi * Real.exp (1039 / 800 : ℝ) =
      -(Real.pi * Real.exp (1039 / 800 : ℝ) - (519 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (519 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (519 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1038_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (90382413266047 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1038_endpointUpper :
    hpThetaJensenKernelEndpointUpper (519 / 800 : ℝ) (1039 / 1600 : ℝ) ≤ (12977691 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1039 / 800 : ℝ)) (28782591081513633 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1039 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1038_product_upper
  have hD : (178127292230501 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (519 / 400 : ℝ) - (1039 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1038_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1038_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (519 / 400 : ℝ) - (1039 / 3200 : ℝ)) ≤
      (1 / (178127292230501 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (178127292230501 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1039 / 3200 : ℝ) - Real.pi * Real.exp (519 / 400 : ℝ)) ≤
      (2 / (178127292230501 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1039 / 3200 : ℝ) - Real.pi * Real.exp (519 / 400 : ℝ) =
      -(Real.pi * Real.exp (519 / 400 : ℝ) - (1039 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28782591081513633 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (28782591081513633 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1038_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (519 / 800 : ℝ) (1039 / 1600 : ℝ)) :
    (63602521 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12977691 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1038_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1038_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1039_leftExp :
    (36647129121 / 10000000000 : ℝ) ≤ Real.exp (1039 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1039 / 800 : ℝ) (1041420802957 / 1000000000000 : ℝ)
    (36647129121 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1039_rightExp :
    Real.exp (13 / 10 : ℝ) ≤ (36692966677 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 10 : ℝ) (260365371063 / 250000000000 : ℝ)
    (36692966677 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1039_denomUpper :
    Real.exp (112027492261696461 / 10000000000000000 : ℝ) ≤ (366658852902527 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (112027492261696461 / 10000000000000000 : ℝ)
    (177398683829 / 125000000000 : ℝ) (366658852902527 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1039_denomLower :
    (361302443202087 / 5000000000 : ℝ) ≤ Real.exp (13985040958687579 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13985040958687579 / 1250000000000000 : ℝ) (709268475281
    / 500000000000 : ℝ) (361302443202087 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1039_product_lower :
    (14391290958687579 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1039 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1039_leftExp
    (by norm_num : (0 : ℝ) ≤ (36647129121 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1039_product_upper :
    Real.pi * Real.exp (13 / 10 : ℝ) ≤ (115274367261696461 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1039_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1039_endpointLower :
    (7860193 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1039 / 1600 : ℝ) (13 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14391290958687579 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1039 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1039_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 10 : ℝ) - (1039 / 3200 : ℝ)) ≤
      (366658852902527 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1039_denomUpper
    linarith [hpThetaJensenCell1039_product_upper]
  have hi : (1 / (366658852902527 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 10 : ℝ) - (1039 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (366658852902527 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (366658852902527 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1039 / 3200 : ℝ) - Real.pi * Real.exp (13 / 10 : ℝ)) := by
    rw [show (1039 / 3200 : ℝ) - Real.pi * Real.exp (13 / 10 : ℝ) =
      -(Real.pi * Real.exp (13 / 10 : ℝ) - (1039 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1039 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1039 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1039_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (366658852902527 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1039_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1039 / 1600 : ℝ) (13 / 20 : ℝ) ≤ (128308077 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 10 : ℝ)) (115274367261696461 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 20 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1039_product_upper
  have hD : (361302443202087 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1039 / 800 : ℝ) - (13 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell1039_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1039_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1039 / 800 : ℝ) - (13 / 40 : ℝ)) ≤
      (1 / (361302443202087 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (361302443202087 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 40 : ℝ) - Real.pi * Real.exp (1039 / 800 : ℝ)) ≤
      (2 / (361302443202087 / 5000000000 : ℝ) : ℝ) := by
    rw [show (13 / 40 : ℝ) - Real.pi * Real.exp (1039 / 800 : ℝ) =
      -(Real.pi * Real.exp (1039 / 800 : ℝ) - (13 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (115274367261696461 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (115274367261696461 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1039_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1039 / 1600 : ℝ) (13 / 20 : ℝ)) :
    (7860193 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (128308077 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1039_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1039_endpointUpper

def hpThetaJensenCellsBatch051Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7784809 / 500000000 : ℝ)
  | 1 => (4811917 / 312500000 : ℝ)
  | 2 => (152282671 / 10000000000 : ℝ)
  | 3 => (3765001 / 250000000 : ℝ)
  | 4 => (14893333 / 1000000000 : ℝ)
  | 5 => (73641211 / 5000000000 : ℝ)
  | 6 => (36411799 / 2500000000 : ℝ)
  | 7 => (144027533 / 10000000000 : ℝ)
  | 8 => (28484663 / 2000000000 : ℝ)
  | 9 => (5633377 / 400000000 : ℝ)
  | 10 => (69630373 / 5000000000 : ℝ)
  | 11 => (137702161 / 10000000000 : ℝ)
  | 12 => (68079277 / 5000000000 : ℝ)
  | 13 => (13462981 / 1000000000 : ℝ)
  | 14 => (66557907 / 5000000000 : ℝ)
  | 15 => (131616453 / 10000000000 : ℝ)
  | 16 => (32532903 / 2500000000 : ℝ)
  | 17 => (128661179 / 10000000000 : ℝ)
  | 18 => (63602521 / 5000000000 : ℝ)
  | 19 => (7860193 / 625000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch051Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (158794039 / 10000000000 : ℝ)
  | 1 => (157047803 / 10000000000 : ℝ)
  | 2 => (77658997 / 5000000000 : ℝ)
  | 3 => (153604491 / 10000000000 : ℝ)
  | 4 => (151907171 / 10000000000 : ℝ)
  | 5 => (150225913 / 10000000000 : ℝ)
  | 6 => (37140149 / 2500000000 : ℝ)
  | 7 => (146911099 / 10000000000 : ℝ)
  | 8 => (72638651 / 5000000000 : ℝ)
  | 9 => (71829543 / 5000000000 : ℝ)
  | 10 => (142056333 / 10000000000 : ℝ)
  | 11 => (35117231 / 2500000000 : ℝ)
  | 12 => (69448371 / 5000000000 : ℝ)
  | 13 => (13733967 / 1000000000 : ℝ)
  | 14 => (135797591 / 10000000000 : ℝ)
  | 15 => (134270391 / 10000000000 : ℝ)
  | 16 => (66378977 / 5000000000 : ℝ)
  | 17 => (26252033 / 2000000000 : ℝ)
  | 18 => (12977691 / 1000000000 : ℝ)
  | 19 => (128308077 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch051_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch051Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch051Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1020_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1021_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1022_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1023_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1024_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1025_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1026_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1027_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1028_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1029_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1030_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1031_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1032_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1033_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1034_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1035_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1036_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1037_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1038_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1039_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper] at h ⊢
    exact h

end HodgeProofHP
