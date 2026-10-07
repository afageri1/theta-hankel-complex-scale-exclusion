import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1560_leftExp :
    (70286875803 / 10000000000 : ℝ) ≤ Real.exp (39 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 20 : ℝ) (26570812127 / 25000000000 : ℝ)
    (70286875803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1560_rightExp :
    Real.exp (1561 / 800 : ℝ) ≤ (8796848667 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1561 / 800 : ℝ) (531437001393 / 500000000000 : ℝ)
    (8796848667 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1560_denomUpper :
    Real.exp (27026743194306531 / 1250000000000000 : ℝ) ≤ (196400384409134411 / 80000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (27026743194306531 / 1250000000000000 : ℝ) (1965346527917
    / 1000000000000 : ℝ) (196400384409134411 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1560_denomLower :
    (23873652106124490353 / 10000000000 : ℝ) ≤ Real.exp (26991820215962297 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26991820215962297 / 1250000000000000 : ℝ) (1963631382873
    / 1000000000000 : ℝ) (23873652106124490353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1560_product_lower :
    (27601585840962297 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1560_leftExp
    (by norm_num : (0 : ℝ) ≤ (70286875803 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1560_product_upper :
    Real.pi * Real.exp (1561 / 800 : ℝ) ≤ (27636118194306531 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1560_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1560_endpointLower :
    (14809 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 40 : ℝ) (1561 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27601585840962297 / 1250000000000000 : ℝ) (Real.pi * Real.exp (39 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell1560_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1561 / 800 : ℝ) - (39 / 80 : ℝ)) ≤
      (196400384409134411 / 80000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1560_denomUpper
    linarith [hpThetaJensenCell1560_product_upper]
  have hi : (1 / (196400384409134411 / 80000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1561 / 800 : ℝ) - (39 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (196400384409134411 / 80000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (196400384409134411 / 80000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 80 : ℝ) - Real.pi * Real.exp (1561 / 800 : ℝ)) := by
    rw [show (39 / 80 : ℝ) - Real.pi * Real.exp (1561 / 800 : ℝ) =
      -(Real.pi * Real.exp (1561 / 800 : ℝ) - (39 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 20 : ℝ)) := by
    have h := hpThetaJensenCell1560_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (196400384409134411 / 80000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1560_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 40 : ℝ) (1561 / 1600 : ℝ) ≤ (15309 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1561 / 800 : ℝ)) (27636118194306531 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1561 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1560_product_upper
  have hD : (23873652106124490353 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 20 : ℝ) - (1561 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1560_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1560_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 20 : ℝ) - (1561 / 3200 : ℝ)) ≤
      (1 / (23873652106124490353 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23873652106124490353 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1561 / 3200 : ℝ) - Real.pi * Real.exp (39 / 20 : ℝ)) ≤
      (2 / (23873652106124490353 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1561 / 3200 : ℝ) - Real.pi * Real.exp (39 / 20 : ℝ) =
      -(Real.pi * Real.exp (39 / 20 : ℝ) - (1561 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27636118194306531 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (27636118194306531 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1560_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 40 : ℝ) (1561 / 1600 : ℝ)) :
    (14809 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15309 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1560_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1560_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1561_leftExp :
    (70374789333 / 10000000000 : ℝ) ≤ Real.exp (1561 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1561 / 800 : ℝ) (212574800557 / 200000000000 : ℝ)
    (70374789333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1561_rightExp :
    Real.exp (781 / 400 : ℝ) ≤ (70462812827 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (781 / 400 : ℝ) (1062915522113 / 1000000000000 : ℝ)
    (70462812827 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1561_denomUpper :
    Real.exp (216487354537613411 / 10000000000000000 : ℝ) ≤ (25230528502805178353 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (216487354537613411 / 10000000000000000 : ℝ)
    (1967026443589 / 1000000000000 : ℝ) (25230528502805178353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1561_denomLower :
    (24534536371363313299 / 10000000000 : ℝ) ≤ Real.exp (27025953146279767 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27025953146279767 / 1250000000000000 : ℝ) (78612308413 /
    40000000000 : ℝ) (24534536371363313299 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1561_product_lower :
    (27636109396279767 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1561 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1561_leftExp
    (by norm_num : (0 : ℝ) ≤ (70374789333 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1561_product_upper :
    Real.pi * Real.exp (781 / 400 : ℝ) ≤ (221365479537613411 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1561_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1561_endpointLower :
    (14447 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1561 / 1600 : ℝ) (781 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27636109396279767 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1561 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1561_product_lower
  have hD : Real.exp (Real.pi * Real.exp (781 / 400 : ℝ) - (1561 / 3200 : ℝ)) ≤
      (25230528502805178353 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1561_denomUpper
    linarith [hpThetaJensenCell1561_product_upper]
  have hi : (1 / (25230528502805178353 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (781 / 400 : ℝ) - (1561 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (25230528502805178353 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (25230528502805178353 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1561 / 3200 : ℝ) - Real.pi * Real.exp (781 / 400 : ℝ)) := by
    rw [show (1561 / 3200 : ℝ) - Real.pi * Real.exp (781 / 400 : ℝ) =
      -(Real.pi * Real.exp (781 / 400 : ℝ) - (1561 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1561 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1561 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1561_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (25230528502805178353 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1561_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1561 / 1600 : ℝ) (781 / 800 : ℝ) ≤ (2987 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (781 / 400 : ℝ)) (221365479537613411 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (781 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1561_product_upper
  have hD : (24534536371363313299 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1561 / 800 : ℝ) - (781 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1561_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1561_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1561 / 800 : ℝ) - (781 / 1600 : ℝ)) ≤
      (1 / (24534536371363313299 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (24534536371363313299 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((781 / 1600 : ℝ) - Real.pi * Real.exp (1561 / 800 : ℝ)) ≤
      (2 / (24534536371363313299 / 10000000000 : ℝ) : ℝ) := by
    rw [show (781 / 1600 : ℝ) - Real.pi * Real.exp (1561 / 800 : ℝ) =
      -(Real.pi * Real.exp (1561 / 800 : ℝ) - (781 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (221365479537613411 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (221365479537613411 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1561_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1561 / 1600 : ℝ) (781 / 800 : ℝ)) :
    (14447 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2987 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1561_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1561_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1562_leftExp :
    (8807851603 / 1250000000 : ℝ) ≤ Real.exp (781 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (781 / 400 : ℝ) (16608055033 / 15625000000 : ℝ)
    (8807851603 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1562_rightExp :
    Real.exp (1563 / 800 : ℝ) ≤ (4409434151 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1563 / 800 : ℝ) (531478521531 / 500000000000 : ℝ)
    (4409434151 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1562_denomUpper :
    Real.exp (13547569337742543 / 625000000000000 : ℝ) ≤ (6482691864796667123 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (13547569337742543 / 625000000000000 : ℝ) (1968709923147
    / 1000000000000 : ℝ) (6482691864796667123 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1562_denomLower :
    (5042917329396182859 / 2000000000 : ℝ) ≤ Real.exp (3382516157271497 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3382516157271497 / 156250000000000 : ℝ) (491746898069 /
    250000000000 : ℝ) (5042917329396182859 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1562_product_lower :
    (3458834516646497 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (781 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1562_leftExp
    (by norm_num : (0 : ℝ) ≤ (8807851603 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1562_product_upper :
    Real.pi * Real.exp (1563 / 800 : ℝ) ≤ (13852647462742543 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1562_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1562_endpointLower :
    (14093 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (781 / 800 : ℝ) (1563 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3458834516646497 / 156250000000000 : ℝ) (Real.pi * Real.exp (781 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1562_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1563 / 800 : ℝ) - (781 / 1600 : ℝ)) ≤
      (6482691864796667123 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1562_denomUpper
    linarith [hpThetaJensenCell1562_product_upper]
  have hi : (1 / (6482691864796667123 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1563 / 800 : ℝ) - (781 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6482691864796667123 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6482691864796667123 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((781 / 1600 : ℝ) - Real.pi * Real.exp (1563 / 800 : ℝ)) := by
    rw [show (781 / 1600 : ℝ) - Real.pi * Real.exp (1563 / 800 : ℝ) =
      -(Real.pi * Real.exp (1563 / 800 : ℝ) - (781 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (781 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (781 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1562_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6482691864796667123 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1562_endpointUpper :
    hpThetaJensenKernelEndpointUpper (781 / 800 : ℝ) (1563 / 1600 : ℝ) ≤ (1457 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1563 / 800 : ℝ)) (13852647462742543 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1563 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1562_product_upper
  have hD : (5042917329396182859 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (781 / 400 : ℝ) - (1563 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1562_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1562_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (781 / 400 : ℝ) - (1563 / 3200 : ℝ)) ≤
      (1 / (5042917329396182859 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5042917329396182859 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1563 / 3200 : ℝ) - Real.pi * Real.exp (781 / 400 : ℝ)) ≤
      (2 / (5042917329396182859 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1563 / 3200 : ℝ) - Real.pi * Real.exp (781 / 400 : ℝ) =
      -(Real.pi * Real.exp (781 / 400 : ℝ) - (1563 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13852647462742543 / 625000000000000 : ℝ) ^ 2 - 6 *
      (13852647462742543 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1562_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (781 / 800 : ℝ) (1563 / 1600 : ℝ)) :
    (14093 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1457 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1562_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1562_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1563_leftExp :
    (70550946413 / 10000000000 : ℝ) ≤ Real.exp (1563 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1563 / 800 : ℝ) (1062957043061 / 1000000000000 : ℝ)
    (70550946413 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1563_rightExp :
    Real.exp (391 / 200 : ℝ) ≤ (70639190239 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (391 / 200 : ℝ) (4152338147 / 3906250000 : ℝ)
    (70639190239 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1563_denomUpper :
    Real.exp (217035210580510727 / 10000000000000000 : ℝ) ≤ (26651363542226287527 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (217035210580510727 / 10000000000000000 : ℝ)
    (246299621989 / 125000000000 : ℝ) (26651363542226287527 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1563_denomLower :
    (1295719146504736771 / 500000000 : ℝ) ≤ Real.exp (27094348605438687 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (27094348605438687 / 1250000000000000 : ℝ) (49216775951 /
    25000000000 : ℝ) (1295719146504736771 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1563_product_lower :
    (27705286105438687 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1563 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1563_leftExp
    (by norm_num : (0 : ℝ) ≤ (70550946413 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1563_product_upper :
    Real.pi * Real.exp (391 / 200 : ℝ) ≤ (221919585580510727 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1563_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1563_endpointLower :
    (3437 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1563 / 1600 : ℝ) (391 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27705286105438687 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1563 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1563_product_lower
  have hD : Real.exp (Real.pi * Real.exp (391 / 200 : ℝ) - (1563 / 3200 : ℝ)) ≤
      (26651363542226287527 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1563_denomUpper
    linarith [hpThetaJensenCell1563_product_upper]
  have hi : (1 / (26651363542226287527 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (391 / 200 : ℝ) - (1563 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26651363542226287527 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26651363542226287527 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1563 / 3200 : ℝ) - Real.pi * Real.exp (391 / 200 : ℝ)) := by
    rw [show (1563 / 3200 : ℝ) - Real.pi * Real.exp (391 / 200 : ℝ) =
      -(Real.pi * Real.exp (391 / 200 : ℝ) - (1563 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1563 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1563 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1563_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26651363542226287527 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1563_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1563 / 1600 : ℝ) (391 / 400 : ℝ) ≤ (7107 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (391 / 200 : ℝ)) (221919585580510727 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (391 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1563_product_upper
  have hD : (1295719146504736771 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1563 / 800 : ℝ) - (391 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1563_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1563_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1563 / 800 : ℝ) - (391 / 800 : ℝ)) ≤
      (1 / (1295719146504736771 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1295719146504736771 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((391 / 800 : ℝ) - Real.pi * Real.exp (1563 / 800 : ℝ)) ≤
      (2 / (1295719146504736771 / 500000000 : ℝ) : ℝ) := by
    rw [show (391 / 800 : ℝ) - Real.pi * Real.exp (1563 / 800 : ℝ) =
      -(Real.pi * Real.exp (1563 / 800 : ℝ) - (391 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (221919585580510727 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (221919585580510727 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1563_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1563 / 1600 : ℝ) (391 / 400 : ℝ)) :
    (3437 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7107 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1563_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1563_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1564_leftExp :
    (14127838047 / 2000000000 : ℝ) ≤ Real.exp (391 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (391 / 200 : ℝ) (1062998565631 / 1000000000000 : ℝ)
    (14127838047 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1564_rightExp :
    Real.exp (313 / 160 : ℝ) ≤ (14145508887 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (313 / 160 : ℝ) (33220002807 / 31250000000 : ℝ)
    (14145508887 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1564_denomUpper :
    Real.exp (43461931700836991 / 2000000000000000 : ℝ) ≤ (27392934261664891087 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (43461931700836991 / 2000000000000000 : ℝ) (1972087611291
    / 1000000000000 : ℝ) (27392934261664891087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1564_denomLower :
    (26634523456545011663 / 10000000000 : ℝ) ≤ Real.exp (5425722248218853 / 250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (5425722248218853 / 250000000000000 : ℝ) (1970358056921 /
    1000000000000 : ℝ) (26634523456545011663 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1564_product_lower :
    (5547987873218853 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (391 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1564_leftExp
    (by norm_num : (0 : ℝ) ≤ (14127838047 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1564_product_upper :
    Real.pi * Real.exp (313 / 160 : ℝ) ≤ (44439431700836991 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1564_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1564_endpointLower :
    (1341 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (391 / 400 : ℝ) (313 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5547987873218853 / 250000000000000 : ℝ) (Real.pi * Real.exp (391 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1564_product_lower
  have hD : Real.exp (Real.pi * Real.exp (313 / 160 : ℝ) - (391 / 800 : ℝ)) ≤
      (27392934261664891087 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1564_denomUpper
    linarith [hpThetaJensenCell1564_product_upper]
  have hi : (1 / (27392934261664891087 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (313 / 160 : ℝ) - (391 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27392934261664891087 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27392934261664891087 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((391 / 800 : ℝ) - Real.pi * Real.exp (313 / 160 : ℝ)) := by
    rw [show (391 / 800 : ℝ) - Real.pi * Real.exp (313 / 160 : ℝ) =
      -(Real.pi * Real.exp (313 / 160 : ℝ) - (391 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (391 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (391 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1564_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27392934261664891087 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1564_endpointUpper :
    hpThetaJensenKernelEndpointUpper (391 / 400 : ℝ) (313 / 320 : ℝ) ≤ (2773 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (313 / 160 : ℝ)) (44439431700836991 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (313 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1564_product_upper
  have hD : (26634523456545011663 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (391 / 200 : ℝ) - (313 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1564_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1564_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (391 / 200 : ℝ) - (313 / 640 : ℝ)) ≤
      (1 / (26634523456545011663 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26634523456545011663 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((313 / 640 : ℝ) - Real.pi * Real.exp (391 / 200 : ℝ)) ≤
      (2 / (26634523456545011663 / 10000000000 : ℝ) : ℝ) := by
    rw [show (313 / 640 : ℝ) - Real.pi * Real.exp (391 / 200 : ℝ) =
      -(Real.pi * Real.exp (391 / 200 : ℝ) - (313 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44439431700836991 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (44439431700836991 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1564_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (391 / 400 : ℝ) (313 / 320 : ℝ)) :
    (1341 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2773 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1564_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1564_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1565_leftExp :
    (4420471527 / 625000000 : ℝ) ≤ Real.exp (313 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (313 / 160 : ℝ) (1063040089823 / 1000000000000 : ℝ)
    (4420471527 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1565_rightExp :
    Real.exp (783 / 400 : ℝ) ≤ (35408004573 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (783 / 400 : ℝ) (1063081615639 / 1000000000000 : ℝ)
    (35408004573 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1565_denomUpper :
    Real.exp (108792226810504789 / 5000000000000000 : ℝ) ≤ (281561166344151191 / 100000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (108792226810504789 / 5000000000000000 : ℝ) (246722729847
    / 125000000000 : ℝ) (281561166344151191 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1565_denomLower :
    (27375625369214473529 / 10000000000 : ℝ) ≤ Real.exp (1697682326306373 / 78125000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1697682326306373 / 78125000000000 : ℝ) (1972048658381 /
    1000000000000 : ℝ) (27375625369214473529 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1565_product_lower :
    (1735914748181373 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (313 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1565_leftExp
    (by norm_num : (0 : ℝ) ≤ (4420471527 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1565_product_upper :
    Real.pi * Real.exp (783 / 400 : ℝ) ≤ (111237539310504789 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1565_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1565_endpointLower :
    (327 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (313 / 320 : ℝ) (783 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1735914748181373 / 78125000000000 : ℝ) (Real.pi * Real.exp (313 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1565_product_lower
  have hD : Real.exp (Real.pi * Real.exp (783 / 400 : ℝ) - (313 / 640 : ℝ)) ≤
      (281561166344151191 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1565_denomUpper
    linarith [hpThetaJensenCell1565_product_upper]
  have hi : (1 / (281561166344151191 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (783 / 400 : ℝ) - (313 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (281561166344151191 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (281561166344151191 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((313 / 640 : ℝ) - Real.pi * Real.exp (783 / 400 : ℝ)) := by
    rw [show (313 / 640 : ℝ) - Real.pi * Real.exp (783 / 400 : ℝ) =
      -(Real.pi * Real.exp (783 / 400 : ℝ) - (313 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (313 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (313 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1565_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (281561166344151191 / 100000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1565_endpointUpper :
    hpThetaJensenKernelEndpointUpper (313 / 320 : ℝ) (783 / 800 : ℝ) ≤ (541 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (783 / 400 : ℝ)) (111237539310504789 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (783 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1565_product_upper
  have hD : (27375625369214473529 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (313 / 160 : ℝ) - (783 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1565_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1565_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (313 / 160 : ℝ) - (783 / 1600 : ℝ)) ≤
      (1 / (27375625369214473529 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (27375625369214473529 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((783 / 1600 : ℝ) - Real.pi * Real.exp (313 / 160 : ℝ)) ≤
      (2 / (27375625369214473529 / 10000000000 : ℝ) : ℝ) := by
    rw [show (783 / 1600 : ℝ) - Real.pi * Real.exp (313 / 160 : ℝ) =
      -(Real.pi * Real.exp (313 / 160 : ℝ) - (783 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (111237539310504789 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (111237539310504789 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1565_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (313 / 320 : ℝ) (783 / 800 : ℝ)) :
    (327 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (541 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1565_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1565_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1566_leftExp :
    (70816009143 / 10000000000 : ℝ) ≤ Real.exp (783 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (783 / 400 : ℝ) (531540807819 / 500000000000 : ℝ)
    (70816009143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1566_rightExp :
    Real.exp (1567 / 800 : ℝ) ≤ (35452292253 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1567 / 800 : ℝ) (265780785769 / 250000000000 : ℝ)
    (35452292253 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1566_denomUpper :
    Real.exp (108929798175979029 / 5000000000000000 : ℝ) ≤ (28941567723724301581 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (108929798175979029 / 5000000000000000 : ℝ)
    (1975479667727 / 1000000000000 : ℝ) (28941567723724301581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1566_denomLower :
    (28138325257324715971 / 10000000000 : ℝ) ≤ Real.exp (27197266599446957 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27197266599446957 / 1250000000000000 : ℝ) (394748570371
    / 200000000000 : ℝ) (28138325257324715971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1566_product_lower :
    (27809375974446957 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (783 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1566_leftExp
    (by norm_num : (0 : ℝ) ≤ (70816009143 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1566_product_upper :
    Real.pi * Real.exp (1567 / 800 : ℝ) ≤ (111376673175979029 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1566_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1566_endpointLower :
    (6379 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (783 / 800 : ℝ) (1567 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27809375974446957 / 1250000000000000 : ℝ) (Real.pi * Real.exp (783 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1566_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1567 / 800 : ℝ) - (783 / 1600 : ℝ)) ≤
      (28941567723724301581 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1566_denomUpper
    linarith [hpThetaJensenCell1566_product_upper]
  have hi : (1 / (28941567723724301581 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1567 / 800 : ℝ) - (783 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (28941567723724301581 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (28941567723724301581 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((783 / 1600 : ℝ) - Real.pi * Real.exp (1567 / 800 : ℝ)) := by
    rw [show (783 / 1600 : ℝ) - Real.pi * Real.exp (1567 / 800 : ℝ) =
      -(Real.pi * Real.exp (1567 / 800 : ℝ) - (783 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (783 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (783 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1566_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (28941567723724301581 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1566_endpointUpper :
    hpThetaJensenKernelEndpointUpper (783 / 800 : ℝ) (1567 / 1600 : ℝ) ≤ (1649 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1567 / 800 : ℝ)) (111376673175979029 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1567 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1566_product_upper
  have hD : (28138325257324715971 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (783 / 400 : ℝ) - (1567 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1566_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1566_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (783 / 400 : ℝ) - (1567 / 3200 : ℝ)) ≤
      (1 / (28138325257324715971 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28138325257324715971 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1567 / 3200 : ℝ) - Real.pi * Real.exp (783 / 400 : ℝ)) ≤
      (2 / (28138325257324715971 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1567 / 3200 : ℝ) - Real.pi * Real.exp (783 / 400 : ℝ) =
      -(Real.pi * Real.exp (783 / 400 : ℝ) - (1567 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (111376673175979029 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (111376673175979029 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1566_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (783 / 800 : ℝ) (1567 / 1600 : ℝ)) :
    (6379 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1649 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1566_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1566_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1567_leftExp :
    (70904584503 / 10000000000 : ℝ) ≤ Real.exp (1567 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1567 / 800 : ℝ) (42524925723 / 40000000000 : ℝ)
    (70904584503 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1567_rightExp :
    Real.exp (49 / 25 : ℝ) ≤ (35496635327 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 25 : ℝ) (212632934427 / 200000000000 : ℝ)
    (35496635327 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1567_denomUpper :
    Real.exp (109067543566855911 / 5000000000000000 : ℝ) ≤ (29749965413852915087 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109067543566855911 / 5000000000000000 : ℝ)
    (1977181107633 / 1000000000000 : ℝ) (29749965413852915087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1567_denomLower :
    (28923279777091304947 / 10000000000 : ℝ) ≤ Real.exp (27231659429743597 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27231659429743597 / 1250000000000000 : ℝ) (1975440646723
    / 1000000000000 : ℝ) (28923279777091304947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1567_product_lower :
    (27844159429743597 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1567 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1567_leftExp
    (by norm_num : (0 : ℝ) ≤ (70904584503 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1567_product_upper :
    Real.pi * Real.exp (49 / 25 : ℝ) ≤ (111515981066855911 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1567_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1567_endpointLower :
    (3111 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1567 / 1600 : ℝ) (49 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27844159429743597 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1567 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1567_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 25 : ℝ) - (1567 / 3200 : ℝ)) ≤
      (29749965413852915087 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1567_denomUpper
    linarith [hpThetaJensenCell1567_product_upper]
  have hi : (1 / (29749965413852915087 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 25 : ℝ) - (1567 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29749965413852915087 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29749965413852915087 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1567 / 3200 : ℝ) - Real.pi * Real.exp (49 / 25 : ℝ)) := by
    rw [show (1567 / 3200 : ℝ) - Real.pi * Real.exp (49 / 25 : ℝ) =
      -(Real.pi * Real.exp (49 / 25 : ℝ) - (1567 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1567 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1567 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1567_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29749965413852915087 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1567_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1567 / 1600 : ℝ) (49 / 50 : ℝ) ≤ (3217 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 25 : ℝ)) (111515981066855911 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1567_product_upper
  have hD : (28923279777091304947 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1567 / 800 : ℝ) - (49 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell1567_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1567_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1567 / 800 : ℝ) - (49 / 100 : ℝ)) ≤
      (1 / (28923279777091304947 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28923279777091304947 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 100 : ℝ) - Real.pi * Real.exp (1567 / 800 : ℝ)) ≤
      (2 / (28923279777091304947 / 10000000000 : ℝ) : ℝ) := by
    rw [show (49 / 100 : ℝ) - Real.pi * Real.exp (1567 / 800 : ℝ) =
      -(Real.pi * Real.exp (1567 / 800 : ℝ) - (49 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (111515981066855911 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (111515981066855911 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1567_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1567 / 1600 : ℝ) (49 / 50 : ℝ)) :
    (3111 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3217 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1567_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1567_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1568_leftExp :
    (70993270651 / 10000000000 : ℝ) ≤ Real.exp (49 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 25 : ℝ) (531582336067 / 500000000000 : ℝ)
    (70993270651 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1568_rightExp :
    Real.exp (1569 / 800 : ℝ) ≤ (71082067729 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1569 / 800 : ℝ) (16612596919 / 15625000000 : ℝ)
    (71082067729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1568_denomUpper :
    Real.exp (218410926402952297 / 10000000000000000 : ℝ) ≤ (3058200904515498983 / 1000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (218410926402952297 / 10000000000000000 : ℝ)
    (989443084003 / 500000000000 : ℝ) (3058200904515498983 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1568_denomLower :
    (1858197898965057911 / 625000000 : ℝ) ≤ Real.exp (27266095766377049 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (27266095766377049 / 1250000000000000 : ℝ) (1977142052473
    / 1000000000000 : ℝ) (1858197898965057911 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1568_product_lower :
    (27878986391377049 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1568_leftExp
    (by norm_num : (0 : ℝ) ≤ (70993270651 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1568_product_upper :
    Real.pi * Real.exp (1569 / 800 : ℝ) ≤ (223310926402952297 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1568_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1568_endpointLower :
    (12137 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 50 : ℝ) (1569 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27878986391377049 / 1250000000000000 : ℝ) (Real.pi * Real.exp (49 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1568_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1569 / 800 : ℝ) - (49 / 100 : ℝ)) ≤
      (3058200904515498983 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1568_denomUpper
    linarith [hpThetaJensenCell1568_product_upper]
  have hi : (1 / (3058200904515498983 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1569 / 800 : ℝ) - (49 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3058200904515498983 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3058200904515498983 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 100 : ℝ) - Real.pi * Real.exp (1569 / 800 : ℝ)) := by
    rw [show (49 / 100 : ℝ) - Real.pi * Real.exp (1569 / 800 : ℝ) =
      -(Real.pi * Real.exp (1569 / 800 : ℝ) - (49 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1568_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3058200904515498983 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1568_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 50 : ℝ) (1569 / 1600 : ℝ) ≤ (251 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1569 / 800 : ℝ)) (223310926402952297 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1569 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1568_product_upper
  have hD : (1858197898965057911 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 25 : ℝ) - (1569 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1568_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1568_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 25 : ℝ) - (1569 / 3200 : ℝ)) ≤
      (1 / (1858197898965057911 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1858197898965057911 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1569 / 3200 : ℝ) - Real.pi * Real.exp (49 / 25 : ℝ)) ≤
      (2 / (1858197898965057911 / 625000000 : ℝ) : ℝ) := by
    rw [show (1569 / 3200 : ℝ) - Real.pi * Real.exp (49 / 25 : ℝ) =
      -(Real.pi * Real.exp (49 / 25 : ℝ) - (1569 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (223310926402952297 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (223310926402952297 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1568_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 50 : ℝ) (1569 / 1600 : ℝ)) :
    (12137 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (251 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1568_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1568_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1569_leftExp :
    (2843282709 / 400000000 : ℝ) ≤ Real.exp (1569 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1569 / 800 : ℝ) (212641240563 / 200000000000 : ℝ)
    (2843282709 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1569_rightExp :
    Real.exp (157 / 80 : ℝ) ≤ (17792743967 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (157 / 80 : ℝ) (1063247735119 / 1000000000000 : ℝ)
    (17792743967 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1569_denomUpper :
    Real.exp (54671778647519431 / 2500000000000000 : ℝ) ≤ (31438420101356087319 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (54671778647519431 / 2500000000000000 : ℝ) (495148714587
    / 250000000000 : ℝ) (31438420101356087319 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1569_denomLower :
    (3820335495547415071 / 1250000000 : ℝ) ≤ Real.exp (1092023026541591 / 50000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1092023026541591 / 50000000000000 : ℝ) (1978847078597 /
    1000000000000 : ℝ) (3820335495547415071 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1569_product_lower :
    (1116554276541591 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1569 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1569_leftExp
    (by norm_num : (0 : ℝ) ≤ (2843282709 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1569_product_upper :
    Real.pi * Real.exp (157 / 80 : ℝ) ≤ (55897559897519431 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1569_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1569_endpointLower :
    (11837 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1569 / 1600 : ℝ) (157 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1116554276541591 / 50000000000000 : ℝ) (Real.pi * Real.exp (1569 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1569_product_lower
  have hD : Real.exp (Real.pi * Real.exp (157 / 80 : ℝ) - (1569 / 3200 : ℝ)) ≤
      (31438420101356087319 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1569_denomUpper
    linarith [hpThetaJensenCell1569_product_upper]
  have hi : (1 / (31438420101356087319 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (157 / 80 : ℝ) - (1569 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31438420101356087319 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31438420101356087319 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1569 / 3200 : ℝ) - Real.pi * Real.exp (157 / 80 : ℝ)) := by
    rw [show (1569 / 3200 : ℝ) - Real.pi * Real.exp (157 / 80 : ℝ) =
      -(Real.pi * Real.exp (157 / 80 : ℝ) - (1569 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1569 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1569 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1569_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31438420101356087319 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1569_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1569 / 1600 : ℝ) (157 / 160 : ℝ) ≤ (12241 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (157 / 80 : ℝ)) (55897559897519431 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (157 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1569_product_upper
  have hD : (3820335495547415071 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1569 / 800 : ℝ) - (157 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1569_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1569_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1569 / 800 : ℝ) - (157 / 320 : ℝ)) ≤
      (1 / (3820335495547415071 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3820335495547415071 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((157 / 320 : ℝ) - Real.pi * Real.exp (1569 / 800 : ℝ)) ≤
      (2 / (3820335495547415071 / 1250000000 : ℝ) : ℝ) := by
    rw [show (157 / 320 : ℝ) - Real.pi * Real.exp (1569 / 800 : ℝ) =
      -(Real.pi * Real.exp (1569 / 800 : ℝ) - (157 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (55897559897519431 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (55897559897519431 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1569_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1569 / 1600 : ℝ) (157 / 160 : ℝ)) :
    (11837 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12241 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1569_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1569_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1570_leftExp :
    (14234195173 / 2000000000 : ℝ) ≤ Real.exp (157 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157 / 80 : ℝ) (531623867559 / 500000000000 : ℝ)
    (14234195173 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1570_rightExp :
    Real.exp (1571 / 800 : ℝ) ≤ (35629997607 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1571 / 800 : ℝ) (212657853809 / 200000000000 : ℝ)
    (35629997607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1570_denomUpper :
    Real.exp (109481826072167951 / 5000000000000000 : ℝ) ≤ (32319943015030069693 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109481826072167951 / 5000000000000000 : ℝ) (123894199269
    / 62500000000 : ℝ) (32319943015030069693 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1570_denomLower :
    (31418553576305477149 / 10000000000 : ℝ) ≤ Real.exp (5467019835241927 / 250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (5467019835241927 / 250000000000000 : ℝ) (15473091677 /
    7812500000 : ℝ) (31418553576305477149 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1570_product_lower :
    (5589754210241927 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (157 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1570_leftExp
    (by norm_num : (0 : ℝ) ≤ (14234195173 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1570_product_upper :
    Real.pi * Real.exp (1571 / 800 : ℝ) ≤ (111934951072167951 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1570_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1570_endpointLower :
    (1443 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (157 / 160 : ℝ) (1571 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5589754210241927 / 250000000000000 : ℝ) (Real.pi * Real.exp (157 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1570_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1571 / 800 : ℝ) - (157 / 320 : ℝ)) ≤
      (32319943015030069693 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1570_denomUpper
    linarith [hpThetaJensenCell1570_product_upper]
  have hi : (1 / (32319943015030069693 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1571 / 800 : ℝ) - (157 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32319943015030069693 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32319943015030069693 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((157 / 320 : ℝ) - Real.pi * Real.exp (1571 / 800 : ℝ)) := by
    rw [show (157 / 320 : ℝ) - Real.pi * Real.exp (1571 / 800 : ℝ) =
      -(Real.pi * Real.exp (1571 / 800 : ℝ) - (157 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (157 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (157 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1570_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32319943015030069693 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1570_endpointUpper :
    hpThetaJensenKernelEndpointUpper (157 / 160 : ℝ) (1571 / 1600 : ℝ) ≤ (5969 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1571 / 800 : ℝ)) (111934951072167951 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1571 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1570_product_upper
  have hD : (31418553576305477149 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (157 / 80 : ℝ) - (1571 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1570_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1570_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (157 / 80 : ℝ) - (1571 / 3200 : ℝ)) ≤
      (1 / (31418553576305477149 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31418553576305477149 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1571 / 3200 : ℝ) - Real.pi * Real.exp (157 / 80 : ℝ)) ≤
      (2 / (31418553576305477149 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1571 / 3200 : ℝ) - Real.pi * Real.exp (157 / 80 : ℝ) =
      -(Real.pi * Real.exp (157 / 80 : ℝ) - (1571 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (111934951072167951 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (111934951072167951 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1570_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (157 / 160 : ℝ) (1571 / 1600 : ℝ)) :
    (1443 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5969 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1570_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1570_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1571_leftExp :
    (71259995211 / 10000000000 : ℝ) ≤ Real.exp (1571 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1571 / 800 : ℝ) (265822317261 / 250000000000 : ℝ)
    (71259995211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1571_rightExp :
    Real.exp (393 / 200 : ℝ) ≤ (35674562951 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (393 / 200 : ℝ) (1063330804593 / 1000000000000 : ℝ)
    (35674562951 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1571_denomUpper :
    Real.exp (109620269744920943 / 5000000000000000 : ℝ) ≤ (33227345782860012061 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109620269744920943 / 5000000000000000 : ℝ) (198402316739
    / 100000000000 : ℝ) (33227345782860012061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1571_denomLower :
    (32299519151108518637 / 10000000000 : ℝ) ≤ Real.exp (27369666359364489 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27369666359364489 / 1250000000000000 : ℝ) (396453606047
    / 200000000000 : ℝ) (32299519151108518637 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1571_product_lower :
    (27983728859364489 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1571 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1571_leftExp
    (by norm_num : (0 : ℝ) ≤ (71259995211 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1571_product_upper :
    Real.pi * Real.exp (393 / 200 : ℝ) ≤ (112074957244920943 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1571_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1571_endpointLower :
    (5629 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1571 / 1600 : ℝ) (393 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (27983728859364489 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1571 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1571_product_lower
  have hD : Real.exp (Real.pi * Real.exp (393 / 200 : ℝ) - (1571 / 3200 : ℝ)) ≤
      (33227345782860012061 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1571_denomUpper
    linarith [hpThetaJensenCell1571_product_upper]
  have hi : (1 / (33227345782860012061 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (393 / 200 : ℝ) - (1571 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (33227345782860012061 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (33227345782860012061 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1571 / 3200 : ℝ) - Real.pi * Real.exp (393 / 200 : ℝ)) := by
    rw [show (1571 / 3200 : ℝ) - Real.pi * Real.exp (393 / 200 : ℝ) =
      -(Real.pi * Real.exp (393 / 200 : ℝ) - (1571 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1571 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1571 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1571_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (33227345782860012061 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1571_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1571 / 1600 : ℝ) (393 / 400 : ℝ) ≤ (11643 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (393 / 200 : ℝ)) (112074957244920943 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (393 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1571_product_upper
  have hD : (32299519151108518637 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1571 / 800 : ℝ) - (393 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1571_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1571_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1571 / 800 : ℝ) - (393 / 800 : ℝ)) ≤
      (1 / (32299519151108518637 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (32299519151108518637 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((393 / 800 : ℝ) - Real.pi * Real.exp (1571 / 800 : ℝ)) ≤
      (2 / (32299519151108518637 / 10000000000 : ℝ) : ℝ) := by
    rw [show (393 / 800 : ℝ) - Real.pi * Real.exp (1571 / 800 : ℝ) =
      -(Real.pi * Real.exp (1571 / 800 : ℝ) - (393 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (112074957244920943 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (112074957244920943 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1571_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1571 / 1600 : ℝ) (393 / 400 : ℝ)) :
    (5629 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11643 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1571_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1571_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1572_leftExp :
    (71349125899 / 10000000000 : ℝ) ≤ Real.exp (393 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (393 / 200 : ℝ) (66458175287 / 62500000000 : ℝ)
    (71349125899 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1572_rightExp :
    Real.exp (1573 / 800 : ℝ) ≤ (2857534723 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1573 / 800 : ℝ) (265843085441 / 250000000000 : ℝ)
    (2857534723 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1572_denomUpper :
    Real.exp (8780711083033739 / 400000000000000 : ℝ) ≤ (1067544403295205579 / 312500000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (8780711083033739 / 400000000000000 : ℝ) (992871402653 /
    500000000000 : ℝ) (1067544403295205579 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1572_denomLower :
    (16603174104974891243 / 5000000000 : ℝ) ≤ Real.exp (27404277266411401 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27404277266411401 / 1250000000000000 : ℝ) (1983983974871
    / 1000000000000 : ℝ) (16603174104974891243 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1572_product_lower :
    (28018730391411401 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (393 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1572_leftExp
    (by norm_num : (0 : ℝ) ≤ (71349125899 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1572_product_upper :
    Real.pi * Real.exp (1573 / 800 : ℝ) ≤ (8977211083033739 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1572_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1572_endpointLower :
    (5489 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (393 / 400 : ℝ) (1573 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (28018730391411401 / 1250000000000000 : ℝ) (Real.pi * Real.exp (393 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1572_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1573 / 800 : ℝ) - (393 / 800 : ℝ)) ≤
      (1067544403295205579 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1572_denomUpper
    linarith [hpThetaJensenCell1572_product_upper]
  have hi : (1 / (1067544403295205579 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1573 / 800 : ℝ) - (393 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1067544403295205579 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1067544403295205579 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((393 / 800 : ℝ) - Real.pi * Real.exp (1573 / 800 : ℝ)) := by
    rw [show (393 / 800 : ℝ) - Real.pi * Real.exp (1573 / 800 : ℝ) =
      -(Real.pi * Real.exp (1573 / 800 : ℝ) - (393 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (393 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (393 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1572_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1067544403295205579 / 312500000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1572_endpointUpper :
    hpThetaJensenKernelEndpointUpper (393 / 400 : ℝ) (1573 / 1600 : ℝ) ≤ (5677 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1573 / 800 : ℝ)) (8977211083033739 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1573 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1572_product_upper
  have hD : (16603174104974891243 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (393 / 200 : ℝ) - (1573 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1572_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1572_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (393 / 200 : ℝ) - (1573 / 3200 : ℝ)) ≤
      (1 / (16603174104974891243 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16603174104974891243 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1573 / 3200 : ℝ) - Real.pi * Real.exp (393 / 200 : ℝ)) ≤
      (2 / (16603174104974891243 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1573 / 3200 : ℝ) - Real.pi * Real.exp (393 / 200 : ℝ) =
      -(Real.pi * Real.exp (393 / 200 : ℝ) - (1573 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8977211083033739 / 400000000000000 : ℝ) ^ 2 - 6 *
      (8977211083033739 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1572_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (393 / 400 : ℝ) (1573 / 1600 : ℝ)) :
    (5489 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5677 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1572_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1572_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1573_leftExp :
    (8929796009 / 1250000000 : ℝ) ≤ Real.exp (1573 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1573 / 800 : ℝ) (1063372341763 / 1000000000000 : ℝ)
    (8929796009 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1573_rightExp :
    Real.exp (787 / 400 : ℝ) ≤ (71527721871 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (787 / 400 : ℝ) (531706940279 / 500000000000 : ℝ)
    (71527721871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1573_denomUpper :
    Real.exp (219795365335880503 / 10000000000000000 : ℝ) ≤ (35122986060773602169 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (219795365335880503 / 10000000000000000 : ℝ)
    (1987466111683 / 1000000000000 : ℝ) (35122986060773602169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1573_denomLower :
    (34139832751479458007 / 10000000000 : ℝ) ≤ Real.exp (3429866494188291 / 156250000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (3429866494188291 / 156250000000000 : ℝ) (1985703578263 /
    1000000000000 : ℝ) (34139832751479458007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1573_product_lower :
    (3506721962938291 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1573 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1573_leftExp
    (by norm_num : (0 : ℝ) ≤ (8929796009 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1573_product_upper :
    Real.pi * Real.exp (787 / 400 : ℝ) ≤ (224710990335880503 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1573_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1573_endpointLower :
    (2141 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1573 / 1600 : ℝ) (787 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3506721962938291 / 156250000000000 : ℝ) (Real.pi * Real.exp (1573 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1573_product_lower
  have hD : Real.exp (Real.pi * Real.exp (787 / 400 : ℝ) - (1573 / 3200 : ℝ)) ≤
      (35122986060773602169 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1573_denomUpper
    linarith [hpThetaJensenCell1573_product_upper]
  have hi : (1 / (35122986060773602169 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (787 / 400 : ℝ) - (1573 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (35122986060773602169 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (35122986060773602169 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1573 / 3200 : ℝ) - Real.pi * Real.exp (787 / 400 : ℝ)) := by
    rw [show (1573 / 3200 : ℝ) - Real.pi * Real.exp (787 / 400 : ℝ) =
      -(Real.pi * Real.exp (787 / 400 : ℝ) - (1573 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1573 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1573 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1573_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (35122986060773602169 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1573_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1573 / 1600 : ℝ) (787 / 800 : ℝ) ≤ (173 / 156250000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (787 / 400 : ℝ)) (224710990335880503 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (787 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1573_product_upper
  have hD : (34139832751479458007 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1573 / 800 : ℝ) - (787 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1573_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1573_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1573 / 800 : ℝ) - (787 / 1600 : ℝ)) ≤
      (1 / (34139832751479458007 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (34139832751479458007 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((787 / 1600 : ℝ) - Real.pi * Real.exp (1573 / 800 : ℝ)) ≤
      (2 / (34139832751479458007 / 10000000000 : ℝ) : ℝ) := by
    rw [show (787 / 1600 : ℝ) - Real.pi * Real.exp (1573 / 800 : ℝ) =
      -(Real.pi * Real.exp (1573 / 800 : ℝ) - (787 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (224710990335880503 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (224710990335880503 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1573_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1573 / 1600 : ℝ) (787 / 800 : ℝ)) :
    (2141 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (173 / 156250000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1573_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1573_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1574_leftExp :
    (17881930467 / 2500000000 : ℝ) ≤ Real.exp (787 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (787 / 400 : ℝ) (1063413880557 / 1000000000000 : ℝ)
    (17881930467 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1574_rightExp :
    Real.exp (63 / 32 : ℝ) ≤ (71617187427 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 32 : ℝ) (531727710487 / 500000000000 : ℝ)
    (71617187427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1574_denomUpper :
    Real.exp (220073304700351211 / 10000000000000000 : ℝ) ≤ (1128527655395331079 / 312500000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (220073304700351211 / 10000000000000000 : ℝ)
    (1989193096157 / 1000000000000 : ℝ) (1128527655395331079 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1574_denomLower :
    (35100789936307887113 / 10000000000 : ℝ) ≤ Real.exp (6868407618710433 / 312500000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (6868407618710433 / 312500000000000 : ℝ) (993713425021 /
    500000000000 : ℝ) (35100789936307887113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1574_product_lower :
    (7022216212460433 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (787 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1574_leftExp
    (by norm_num : (0 : ℝ) ≤ (17881930467 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1574_product_upper :
    Real.pi * Real.exp (63 / 32 : ℝ) ≤ (224992054700351211 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1574_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1574_endpointLower :
    (10439 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (787 / 800 : ℝ) (63 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7022216212460433 / 312500000000000 : ℝ) (Real.pi * Real.exp (787 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1574_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 32 : ℝ) - (787 / 1600 : ℝ)) ≤
      (1128527655395331079 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1574_denomUpper
    linarith [hpThetaJensenCell1574_product_upper]
  have hi : (1 / (1128527655395331079 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 32 : ℝ) - (787 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1128527655395331079 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1128527655395331079 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((787 / 1600 : ℝ) - Real.pi * Real.exp (63 / 32 : ℝ)) := by
    rw [show (787 / 1600 : ℝ) - Real.pi * Real.exp (63 / 32 : ℝ) =
      -(Real.pi * Real.exp (63 / 32 : ℝ) - (787 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (787 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (787 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1574_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1128527655395331079 / 312500000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1574_endpointUpper :
    hpThetaJensenKernelEndpointUpper (787 / 800 : ℝ) (63 / 64 : ℝ) ≤ (10797 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 32 : ℝ)) (224992054700351211 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1574_product_upper
  have hD : (35100789936307887113 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (787 / 400 : ℝ) - (63 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1574_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1574_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (787 / 400 : ℝ) - (63 / 128 : ℝ)) ≤
      (1 / (35100789936307887113 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35100789936307887113 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 128 : ℝ) - Real.pi * Real.exp (787 / 400 : ℝ)) ≤
      (2 / (35100789936307887113 / 10000000000 : ℝ) : ℝ) := by
    rw [show (63 / 128 : ℝ) - Real.pi * Real.exp (787 / 400 : ℝ) =
      -(Real.pi * Real.exp (787 / 400 : ℝ) - (63 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (224992054700351211 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (224992054700351211 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1574_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (787 / 800 : ℝ) (63 / 64 : ℝ)) :
    (10439 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10797 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1574_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1574_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1575_leftExp :
    (2238037107 / 312500000 : ℝ) ≤ Real.exp (63 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 32 : ℝ) (1063455420973 / 1000000000000 : ℝ)
    (2238037107 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1575_rightExp :
    Real.exp (197 / 100 : ℝ) ≤ (17926691221 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (197 / 100 : ℝ) (265874240753 / 250000000000 : ℝ)
    (17926691221 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1575_denomUpper :
    Real.exp (55087898903055053 / 2500000000000000 : ℝ) ≤ (9282997082826595089 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (55087898903055053 / 2500000000000000 : ℝ) (248865471059
    / 125000000000 : ℝ) (9282997082826595089 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1575_denomLower :
    (18045031476905683787 / 5000000000 : ℝ) ≤ Real.exp (859636652631793 / 39062500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (859636652631793 / 39062500000000 : ℝ) (1989153799843 /
    1000000000000 : ℝ) (18045031476905683787 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1575_product_lower :
    (878874933881793 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (63 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1575_leftExp
    (by norm_num : (0 : ℝ) ≤ (2238037107 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1575_product_upper :
    Real.pi * Real.exp (197 / 100 : ℝ) ≤ (56318367653055053 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1575_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1575_endpointLower :
    (10179 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 64 : ℝ) (197 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (878874933881793 / 39062500000000 : ℝ) (Real.pi * Real.exp (63 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1575_product_lower
  have hD : Real.exp (Real.pi * Real.exp (197 / 100 : ℝ) - (63 / 128 : ℝ)) ≤
      (9282997082826595089 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1575_denomUpper
    linarith [hpThetaJensenCell1575_product_upper]
  have hi : (1 / (9282997082826595089 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (197 / 100 : ℝ) - (63 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9282997082826595089 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9282997082826595089 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 128 : ℝ) - Real.pi * Real.exp (197 / 100 : ℝ)) := by
    rw [show (63 / 128 : ℝ) - Real.pi * Real.exp (197 / 100 : ℝ) =
      -(Real.pi * Real.exp (197 / 100 : ℝ) - (63 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1575_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9282997082826595089 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1575_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 64 : ℝ) (197 / 200 : ℝ) ≤ (329 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (197 / 100 : ℝ)) (56318367653055053 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (197 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1575_product_upper
  have hD : (18045031476905683787 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 32 : ℝ) - (197 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1575_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1575_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 32 : ℝ) - (197 / 400 : ℝ)) ≤
      (1 / (18045031476905683787 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18045031476905683787 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((197 / 400 : ℝ) - Real.pi * Real.exp (63 / 32 : ℝ)) ≤
      (2 / (18045031476905683787 / 5000000000 : ℝ) : ℝ) := by
    rw [show (197 / 400 : ℝ) - Real.pi * Real.exp (63 / 32 : ℝ) =
      -(Real.pi * Real.exp (63 / 32 : ℝ) - (197 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56318367653055053 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (56318367653055053 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1575_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 64 : ℝ) (197 / 200 : ℝ)) :
    (10179 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (329 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1575_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1575_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1576_leftExp :
    (71706764881 / 10000000000 : ℝ) ≤ Real.exp (197 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (197 / 100 : ℝ) (1063496963011 / 1000000000000 : ℝ)
    (71706764881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1576_rightExp :
    Real.exp (1577 / 800 : ℝ) ≤ (35898227193 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1577 / 800 : ℝ) (531769253337 / 500000000000 : ℝ)
    (35898227193 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1576_denomUpper :
    Real.exp (110315119261938449 / 5000000000000000 : ℝ) ≤ (3818119467668741241 / 1000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (110315119261938449 / 5000000000000000 : ℝ) (996329069229
    / 500000000000 : ℝ) (3818119467668741241 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1576_denomLower :
    (3710852194445130817 / 1000000000 : ℝ) ≤ Real.exp (27543159237003819 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27543159237003819 / 1250000000000000 : ℝ) (497721109353
    / 250000000000 : ℝ) (3710852194445130817 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1576_product_lower :
    (28159174862003819 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (197 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1576_leftExp
    (by norm_num : (0 : ℝ) ≤ (71706764881 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1576_product_upper :
    Real.pi * Real.exp (1577 / 800 : ℝ) ≤ (112777619261938449 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1576_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1576_endpointLower :
    (397 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (197 / 200 : ℝ) (1577 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (28159174862003819 / 1250000000000000 : ℝ) (Real.pi * Real.exp (197 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1576_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1577 / 800 : ℝ) - (197 / 400 : ℝ)) ≤
      (3818119467668741241 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1576_denomUpper
    linarith [hpThetaJensenCell1576_product_upper]
  have hi : (1 / (3818119467668741241 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1577 / 800 : ℝ) - (197 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3818119467668741241 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3818119467668741241 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((197 / 400 : ℝ) - Real.pi * Real.exp (1577 / 800 : ℝ)) := by
    rw [show (197 / 400 : ℝ) - Real.pi * Real.exp (1577 / 800 : ℝ) =
      -(Real.pi * Real.exp (1577 / 800 : ℝ) - (197 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (197 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (197 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1576_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3818119467668741241 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1576_endpointUpper :
    hpThetaJensenKernelEndpointUpper (197 / 200 : ℝ) (1577 / 1600 : ℝ) ≤ (5133 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1577 / 800 : ℝ)) (112777619261938449 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1577 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1576_product_upper
  have hD : (3710852194445130817 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (197 / 100 : ℝ) - (1577 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1576_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1576_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (197 / 100 : ℝ) - (1577 / 3200 : ℝ)) ≤
      (1 / (3710852194445130817 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3710852194445130817 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1577 / 3200 : ℝ) - Real.pi * Real.exp (197 / 100 : ℝ)) ≤
      (2 / (3710852194445130817 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1577 / 3200 : ℝ) - Real.pi * Real.exp (197 / 100 : ℝ) =
      -(Real.pi * Real.exp (197 / 100 : ℝ) - (1577 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (112777619261938449 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (112777619261938449 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1576_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (197 / 200 : ℝ) (1577 / 1600 : ℝ)) :
    (397 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5133 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1576_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1576_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1577_leftExp :
    (35898227191 / 5000000000 : ℝ) ≤ Real.exp (1577 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1577 / 800 : ℝ) (1063538506673 / 1000000000000 : ℝ)
    (35898227191 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1577_rightExp :
    Real.exp (789 / 400 : ℝ) ≤ (71886256067 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (789 / 400 : ℝ) (531790025979 / 500000000000 : ℝ)
    (71886256067 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1577_denomUpper :
    Real.exp (220909233856294731 / 10000000000000000 : ℝ) ≤ (39261431165026866813 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (220909233856294731 / 10000000000000000 : ℝ)
    (997198107889 / 500000000000 : ℝ) (39261431165026866813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1577_denomLower :
    (38157064866209162869 / 10000000000 : ℝ) ≤ Real.exp (13788994794678509 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (13788994794678509 / 625000000000000 : ℝ) (1992618772557
    / 1000000000000 : ℝ) (38157064866209162869 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1577_product_lower :
    (14097197919678509 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1577 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1577_leftExp
    (by norm_num : (0 : ℝ) ≤ (35898227191 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1577_product_upper :
    Real.pi * Real.exp (789 / 400 : ℝ) ≤ (225837358856294731 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1577_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1577_endpointLower :
    (9677 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1577 / 1600 : ℝ) (789 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14097197919678509 / 625000000000000 : ℝ) (Real.pi * Real.exp (1577 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1577_product_lower
  have hD : Real.exp (Real.pi * Real.exp (789 / 400 : ℝ) - (1577 / 3200 : ℝ)) ≤
      (39261431165026866813 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1577_denomUpper
    linarith [hpThetaJensenCell1577_product_upper]
  have hi : (1 / (39261431165026866813 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (789 / 400 : ℝ) - (1577 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (39261431165026866813 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (39261431165026866813 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1577 / 3200 : ℝ) - Real.pi * Real.exp (789 / 400 : ℝ)) := by
    rw [show (1577 / 3200 : ℝ) - Real.pi * Real.exp (789 / 400 : ℝ) =
      -(Real.pi * Real.exp (789 / 400 : ℝ) - (1577 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1577 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1577 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1577_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (39261431165026866813 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1577_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1577 / 1600 : ℝ) (789 / 800 : ℝ) ≤ (1001 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (789 / 400 : ℝ)) (225837358856294731 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (789 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1577_product_upper
  have hD : (38157064866209162869 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1577 / 800 : ℝ) - (789 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1577_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1577_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1577 / 800 : ℝ) - (789 / 1600 : ℝ)) ≤
      (1 / (38157064866209162869 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (38157064866209162869 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((789 / 1600 : ℝ) - Real.pi * Real.exp (1577 / 800 : ℝ)) ≤
      (2 / (38157064866209162869 / 10000000000 : ℝ) : ℝ) := by
    rw [show (789 / 1600 : ℝ) - Real.pi * Real.exp (1577 / 800 : ℝ) =
      -(Real.pi * Real.exp (1577 / 800 : ℝ) - (789 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (225837358856294731 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (225837358856294731 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1577_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1577 / 1600 : ℝ) (789 / 800 : ℝ)) :
    (9677 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1001 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1577_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1577_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1578_leftExp :
    (1123222751 / 156250000 : ℝ) ≤ Real.exp (789 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (789 / 400 : ℝ) (1063580051957 / 1000000000000 : ℝ)
    (1123222751 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1578_rightExp :
    Real.exp (1579 / 800 : ℝ) ≤ (71976170071 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1579 / 800 : ℝ) (212724319773 / 200000000000 : ℝ)
    (71976170071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1578_denomUpper :
    Real.exp (221188582061863103 / 10000000000000000 : ℝ) ≤ (40373654756015830849 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (221188582061863103 / 10000000000000000 : ℝ)
    (499034502579 / 250000000000 : ℝ) (40373654756015830849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1578_denomLower :
    (19618309162068426849 / 5000000000 : ℝ) ≤ Real.exp (215725499961537 / 9765625000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (215725499961537 / 9765625000000 : ℝ) (1994356814999 /
    1000000000000 : ℝ) (19618309162068426849 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1578_product_lower :
    (441088451094949 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (789 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1578_leftExp
    (by norm_num : (0 : ℝ) ≤ (1123222751 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1578_product_upper :
    Real.pi * Real.exp (1579 / 800 : ℝ) ≤ (226119832061863103 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1578_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1578_endpointLower :
    (4717 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (789 / 800 : ℝ) (1579 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (441088451094949 / 19531250000000 : ℝ) (Real.pi * Real.exp (789 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1578_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1579 / 800 : ℝ) - (789 / 1600 : ℝ)) ≤
      (40373654756015830849 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1578_denomUpper
    linarith [hpThetaJensenCell1578_product_upper]
  have hi : (1 / (40373654756015830849 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1579 / 800 : ℝ) - (789 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (40373654756015830849 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (40373654756015830849 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((789 / 1600 : ℝ) - Real.pi * Real.exp (1579 / 800 : ℝ)) := by
    rw [show (789 / 1600 : ℝ) - Real.pi * Real.exp (1579 / 800 : ℝ) =
      -(Real.pi * Real.exp (1579 / 800 : ℝ) - (789 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (789 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (789 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1578_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (40373654756015830849 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1578_endpointUpper :
    hpThetaJensenKernelEndpointUpper (789 / 800 : ℝ) (1579 / 1600 : ℝ) ≤ (61 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1579 / 800 : ℝ)) (226119832061863103 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1579 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1578_product_upper
  have hD : (19618309162068426849 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (789 / 400 : ℝ) - (1579 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1578_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1578_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (789 / 400 : ℝ) - (1579 / 3200 : ℝ)) ≤
      (1 / (19618309162068426849 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19618309162068426849 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1579 / 3200 : ℝ) - Real.pi * Real.exp (789 / 400 : ℝ)) ≤
      (2 / (19618309162068426849 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1579 / 3200 : ℝ) - Real.pi * Real.exp (789 / 400 : ℝ) =
      -(Real.pi * Real.exp (789 / 400 : ℝ) - (1579 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (226119832061863103 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (226119832061863103 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1578_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (789 / 800 : ℝ) (1579 / 1600 : ℝ)) :
    (4717 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (61 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1578_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1578_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1579_leftExp :
    (17994042517 / 2500000000 : ℝ) ≤ Real.exp (1579 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1579 / 800 : ℝ) (66476349929 / 62500000000 : ℝ)
    (17994042517 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1579_rightExp :
    Real.exp (79 / 40 : ℝ) ≤ (3603309827 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 40 : ℝ) (265915786849 / 250000000000 : ℝ)
    (3603309827 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1579_denomUpper :
    Real.exp (11073414179334411 / 500000000000000 : ℝ) ≤ (41518853062270010571 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (11073414179334411 / 500000000000000 : ℝ) (499470882987 /
    250000000000 : ℝ) (41518853062270010571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1579_denomLower :
    (1260879332440580221 / 312500000 : ℝ) ≤ Real.exp (6911945627383383 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6911945627383383 / 312500000000000 : ℝ) (998049287283 /
    500000000000 : ℝ) (1260879332440580221 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1579_product_lower :
    (7066242502383383 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1579 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1579_leftExp
    (by norm_num : (0 : ℝ) ≤ (17994042517 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1579_product_upper :
    Real.pi * Real.exp (79 / 40 : ℝ) ≤ (11320132929334411 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1579_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1579_endpointLower :
    (4599 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1579 / 1600 : ℝ) (79 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7066242502383383 / 312500000000000 : ℝ) (Real.pi * Real.exp (1579 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1579_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 40 : ℝ) - (1579 / 3200 : ℝ)) ≤
      (41518853062270010571 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1579_denomUpper
    linarith [hpThetaJensenCell1579_product_upper]
  have hi : (1 / (41518853062270010571 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 40 : ℝ) - (1579 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (41518853062270010571 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (41518853062270010571 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1579 / 3200 : ℝ) - Real.pi * Real.exp (79 / 40 : ℝ)) := by
    rw [show (1579 / 3200 : ℝ) - Real.pi * Real.exp (79 / 40 : ℝ) =
      -(Real.pi * Real.exp (79 / 40 : ℝ) - (1579 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1579 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1579 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1579_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (41518853062270010571 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1579_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1579 / 1600 : ℝ) (79 / 80 : ℝ) ≤ (1903 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 40 : ℝ)) (11320132929334411 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1579_product_upper
  have hD : (1260879332440580221 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1579 / 800 : ℝ) - (79 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1579_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1579_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1579 / 800 : ℝ) - (79 / 160 : ℝ)) ≤
      (1 / (1260879332440580221 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1260879332440580221 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 160 : ℝ) - Real.pi * Real.exp (1579 / 800 : ℝ)) ≤
      (2 / (1260879332440580221 / 312500000 : ℝ) : ℝ) := by
    rw [show (79 / 160 : ℝ) - Real.pi * Real.exp (1579 / 800 : ℝ) =
      -(Real.pi * Real.exp (1579 / 800 : ℝ) - (79 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11320132929334411 / 500000000000000 : ℝ) ^ 2 - 6 *
      (11320132929334411 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1579_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1579 / 1600 : ℝ) (79 / 80 : ℝ)) :
    (4599 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1903 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1579_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1579_endpointUpper

def hpThetaJensenCellsBatch078Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (14809 / 10000000000 : ℝ)
  | 1 => (14447 / 10000000000 : ℝ)
  | 2 => (14093 / 10000000000 : ℝ)
  | 3 => (3437 / 2500000000 : ℝ)
  | 4 => (1341 / 1000000000 : ℝ)
  | 5 => (327 / 250000000 : ℝ)
  | 6 => (6379 / 5000000000 : ℝ)
  | 7 => (3111 / 2500000000 : ℝ)
  | 8 => (12137 / 10000000000 : ℝ)
  | 9 => (11837 / 10000000000 : ℝ)
  | 10 => (1443 / 1250000000 : ℝ)
  | 11 => (5629 / 5000000000 : ℝ)
  | 12 => (5489 / 5000000000 : ℝ)
  | 13 => (2141 / 2000000000 : ℝ)
  | 14 => (10439 / 10000000000 : ℝ)
  | 15 => (10179 / 10000000000 : ℝ)
  | 16 => (397 / 400000000 : ℝ)
  | 17 => (9677 / 10000000000 : ℝ)
  | 18 => (4717 / 5000000000 : ℝ)
  | 19 => (4599 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch078Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (15309 / 10000000000 : ℝ)
  | 1 => (2987 / 2000000000 : ℝ)
  | 2 => (1457 / 1000000000 : ℝ)
  | 3 => (7107 / 5000000000 : ℝ)
  | 4 => (2773 / 2000000000 : ℝ)
  | 5 => (541 / 400000000 : ℝ)
  | 6 => (1649 / 1250000000 : ℝ)
  | 7 => (3217 / 2500000000 : ℝ)
  | 8 => (251 / 200000000 : ℝ)
  | 9 => (12241 / 10000000000 : ℝ)
  | 10 => (5969 / 5000000000 : ℝ)
  | 11 => (11643 / 10000000000 : ℝ)
  | 12 => (5677 / 5000000000 : ℝ)
  | 13 => (173 / 156250000 : ℝ)
  | 14 => (10797 / 10000000000 : ℝ)
  | 15 => (329 / 312500000 : ℝ)
  | 16 => (5133 / 5000000000 : ℝ)
  | 17 => (1001 / 1000000000 : ℝ)
  | 18 => (61 / 62500000 : ℝ)
  | 19 => (1903 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch078_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch078Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch078Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1560_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1561_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1562_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1563_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1564_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1565_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1566_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1567_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1568_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1569_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1570_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1571_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1572_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1573_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1574_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1575_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1576_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1577_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1578_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1579_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper] at h ⊢
    exact h

end HodgeProofHP
