import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1580_leftExp :
    (72066196537 / 10000000000 : ℝ) ≤ Real.exp (79 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 40 : ℝ) (212732629479 / 200000000000 : ℝ)
    (72066196537 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1580_rightExp :
    Real.exp (1581 / 800 : ℝ) ≤ (72156335611 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1581 / 800 : ℝ) (1063704697549 / 1000000000000 : ℝ)
    (72156335611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1580_denomUpper :
    Real.exp (221748338861168323 / 10000000000000000 : ℝ) ≤ (42698045321662018617 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (221748338861168323 / 10000000000000000 : ℝ)
    (999816395239 / 500000000000 : ℝ) (42698045321662018617 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1580_denomLower :
    (41492612806135652913 / 10000000000 : ℝ) ≤ Real.exp (27682745188883363 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27682745188883363 / 1250000000000000 : ℝ) (1997844061151
    / 1000000000000 : ℝ) (41492612806135652913 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1580_product_lower :
    (28300323313883363 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1580_leftExp
    (by norm_num : (0 : ℝ) ≤ (72066196537 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1580_product_upper :
    Real.pi * Real.exp (1581 / 800 : ℝ) ≤ (226685838861168323 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1580_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1580_endpointLower :
    (8967 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 80 : ℝ) (1581 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (28300323313883363 / 1250000000000000 : ℝ) (Real.pi * Real.exp (79 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1580_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1581 / 800 : ℝ) - (79 / 160 : ℝ)) ≤
      (42698045321662018617 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1580_denomUpper
    linarith [hpThetaJensenCell1580_product_upper]
  have hi : (1 / (42698045321662018617 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1581 / 800 : ℝ) - (79 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (42698045321662018617 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (42698045321662018617 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 160 : ℝ) - Real.pi * Real.exp (1581 / 800 : ℝ)) := by
    rw [show (79 / 160 : ℝ) - Real.pi * Real.exp (1581 / 800 : ℝ) =
      -(Real.pi * Real.exp (1581 / 800 : ℝ) - (79 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1580_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (42698045321662018617 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1580_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 80 : ℝ) (1581 / 1600 : ℝ) ≤ (9277 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1581 / 800 : ℝ)) (226685838861168323 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1581 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1580_product_upper
  have hD : (41492612806135652913 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 40 : ℝ) - (1581 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1580_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1580_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 40 : ℝ) - (1581 / 3200 : ℝ)) ≤
      (1 / (41492612806135652913 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (41492612806135652913 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1581 / 3200 : ℝ) - Real.pi * Real.exp (79 / 40 : ℝ)) ≤
      (2 / (41492612806135652913 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1581 / 3200 : ℝ) - Real.pi * Real.exp (79 / 40 : ℝ) =
      -(Real.pi * Real.exp (79 / 40 : ℝ) - (1581 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (226685838861168323 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (226685838861168323 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1580_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 80 : ℝ) (1581 / 1600 : ℝ)) :
    (8967 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9277 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1580_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1580_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1581_leftExp :
    (9019541951 / 1250000000 : ℝ) ≤ Real.exp (1581 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1581 / 800 : ℝ) (265926174387 / 250000000000 : ℝ)
    (9019541951 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1581_rightExp :
    Real.exp (791 / 400 : ℝ) ≤ (2889863497 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (791 / 400 : ℝ) (42549849973 / 40000000000 : ℝ)
    (2889863497 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1581_denomUpper :
    Real.exp (8881149933130721 / 400000000000000 : ℝ) ≤ (137225886153700991 / 31250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8881149933130721 / 400000000000000 : ℝ) (2001385795819 /
    1000000000000 : ℝ) (137225886153700991 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1581_denomLower :
    (21335529710898824591 / 5000000000 : ℝ) ≤ Real.exp (3464719010865749 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3464719010865749 / 156250000000000 : ℝ) (1999593284559 /
    1000000000000 : ℝ) (21335529710898824591 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1581_product_lower :
    (3541965104615749 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1581 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1581_leftExp
    (by norm_num : (0 : ℝ) ≤ (9019541951 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1581_product_upper :
    Real.pi * Real.exp (791 / 400 : ℝ) ≤ (9078774933130721 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1581_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1581_endpointLower :
    (4371 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1581 / 1600 : ℝ) (791 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3541965104615749 / 156250000000000 : ℝ) (Real.pi * Real.exp (1581 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1581_product_lower
  have hD : Real.exp (Real.pi * Real.exp (791 / 400 : ℝ) - (1581 / 3200 : ℝ)) ≤
      (137225886153700991 / 31250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1581_denomUpper
    linarith [hpThetaJensenCell1581_product_upper]
  have hi : (1 / (137225886153700991 / 31250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (791 / 400 : ℝ) - (1581 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (137225886153700991 / 31250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (137225886153700991 / 31250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1581 / 3200 : ℝ) - Real.pi * Real.exp (791 / 400 : ℝ)) := by
    rw [show (1581 / 3200 : ℝ) - Real.pi * Real.exp (791 / 400 : ℝ) =
      -(Real.pi * Real.exp (791 / 400 : ℝ) - (1581 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1581 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1581 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1581_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (137225886153700991 / 31250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1581_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1581 / 1600 : ℝ) (791 / 800 : ℝ) ≤ (2261 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (791 / 400 : ℝ)) (9078774933130721 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (791 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1581_product_upper
  have hD : (21335529710898824591 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1581 / 800 : ℝ) - (791 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1581_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1581_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1581 / 800 : ℝ) - (791 / 1600 : ℝ)) ≤
      (1 / (21335529710898824591 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21335529710898824591 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((791 / 1600 : ℝ) - Real.pi * Real.exp (1581 / 800 : ℝ)) ≤
      (2 / (21335529710898824591 / 5000000000 : ℝ) : ℝ) := by
    rw [show (791 / 1600 : ℝ) - Real.pi * Real.exp (1581 / 800 : ℝ) =
      -(Real.pi * Real.exp (1581 / 800 : ℝ) - (791 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9078774933130721 / 400000000000000 : ℝ) ^ 2 - 6 *
      (9078774933130721 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1581_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1581 / 1600 : ℝ) (791 / 800 : ℝ)) :
    (4371 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2261 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1581_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1581_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1582_leftExp :
    (36123293711 / 5000000000 : ℝ) ≤ Real.exp (791 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (791 / 400 : ℝ) (265936562331 / 250000000000 : ℝ)
    (36123293711 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1582_rightExp :
    Real.exp (1583 / 800 : ℝ) ≤ (72336952127 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1583 / 800 : ℝ) (42551512109 / 40000000000 : ℝ)
    (72336952127 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1582_denomUpper :
    Real.exp (222309512443518311 / 10000000000000000 : ℝ) ≤ (45162653731081923071 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (222309512443518311 / 10000000000000000 : ℝ)
    (500785639497 / 250000000000 : ℝ) (45162653731081923071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1582_denomLower :
    (8776905970594161147 / 2000000000 : ℝ) ≤ Real.exp (13876401629515989 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (13876401629515989 / 625000000000000 : ℝ) (2001346254701
    / 1000000000000 : ℝ) (8776905970594161147 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1582_product_lower :
    (14185581317015989 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (791 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1582_leftExp
    (by norm_num : (0 : ℝ) ≤ (36123293711 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1582_product_upper :
    Real.pi * Real.exp (1583 / 800 : ℝ) ≤ (227253262443518311 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1582_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1582_endpointLower :
    (4261 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (791 / 800 : ℝ) (1583 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14185581317015989 / 625000000000000 : ℝ) (Real.pi * Real.exp (791 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1582_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1583 / 800 : ℝ) - (791 / 1600 : ℝ)) ≤
      (45162653731081923071 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1582_denomUpper
    linarith [hpThetaJensenCell1582_product_upper]
  have hi : (1 / (45162653731081923071 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1583 / 800 : ℝ) - (791 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (45162653731081923071 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (45162653731081923071 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((791 / 1600 : ℝ) - Real.pi * Real.exp (1583 / 800 : ℝ)) := by
    rw [show (791 / 1600 : ℝ) - Real.pi * Real.exp (1583 / 800 : ℝ) =
      -(Real.pi * Real.exp (1583 / 800 : ℝ) - (791 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (791 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (791 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1582_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (45162653731081923071 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1582_endpointUpper :
    hpThetaJensenKernelEndpointUpper (791 / 800 : ℝ) (1583 / 1600 : ℝ) ≤ (8817 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1583 / 800 : ℝ)) (227253262443518311 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1583 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1582_product_upper
  have hD : (8776905970594161147 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (791 / 400 : ℝ) - (1583 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1582_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1582_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (791 / 400 : ℝ) - (1583 / 3200 : ℝ)) ≤
      (1 / (8776905970594161147 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8776905970594161147 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1583 / 3200 : ℝ) - Real.pi * Real.exp (791 / 400 : ℝ)) ≤
      (2 / (8776905970594161147 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1583 / 3200 : ℝ) - Real.pi * Real.exp (791 / 400 : ℝ) =
      -(Real.pi * Real.exp (791 / 400 : ℝ) - (1583 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (227253262443518311 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (227253262443518311 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1582_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (791 / 800 : ℝ) (1583 / 1600 : ℝ)) :
    (4261 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8817 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1582_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1582_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1583_leftExp :
    (18084238031 / 2500000000 : ℝ) ≤ Real.exp (1583 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1583 / 800 : ℝ) (265946950681 / 250000000000 : ℝ)
    (18084238031 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1583_rightExp :
    Real.exp (99 / 50 : ℝ) ≤ (72427429853 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (99 / 50 : ℝ) (1063829357747 / 1000000000000 : ℝ)
    (72427429853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1583_denomUpper :
    Real.exp (222590631634175829 / 10000000000000000 : ℝ) ≤ (46450276574934506087 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (222590631634175829 / 10000000000000000 : ℝ)
    (250612885857 / 125000000000 : ℝ) (46450276574934506087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1583_denomLower :
    (45134109340081184543 / 10000000000 : ℝ) ≤ Real.exp (6946974690535669 / 312500000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (6946974690535669 / 312500000000000 : ℝ) (500775745399 /
    250000000000 : ℝ) (45134109340081184543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1583_product_lower :
    (7101662190535669 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1583 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1583_leftExp
    (by norm_num : (0 : ℝ) ≤ (18084238031 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1583_product_upper :
    Real.pi * Real.exp (99 / 50 : ℝ) ≤ (227537506634175829 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1583_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1583_endpointLower :
    (8307 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1583 / 1600 : ℝ) (99 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7101662190535669 / 312500000000000 : ℝ) (Real.pi * Real.exp (1583 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1583_product_lower
  have hD : Real.exp (Real.pi * Real.exp (99 / 50 : ℝ) - (1583 / 3200 : ℝ)) ≤
      (46450276574934506087 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1583_denomUpper
    linarith [hpThetaJensenCell1583_product_upper]
  have hi : (1 / (46450276574934506087 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (99 / 50 : ℝ) - (1583 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (46450276574934506087 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (46450276574934506087 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1583 / 3200 : ℝ) - Real.pi * Real.exp (99 / 50 : ℝ)) := by
    rw [show (1583 / 3200 : ℝ) - Real.pi * Real.exp (99 / 50 : ℝ) =
      -(Real.pi * Real.exp (99 / 50 : ℝ) - (1583 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1583 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1583 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1583_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (46450276574934506087 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1583_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1583 / 1600 : ℝ) (99 / 100 : ℝ) ≤ (1719 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (99 / 50 : ℝ)) (227537506634175829 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (99 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1583_product_upper
  have hD : (45134109340081184543 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1583 / 800 : ℝ) - (99 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1583_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1583_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1583 / 800 : ℝ) - (99 / 200 : ℝ)) ≤
      (1 / (45134109340081184543 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (45134109340081184543 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((99 / 200 : ℝ) - Real.pi * Real.exp (1583 / 800 : ℝ)) ≤
      (2 / (45134109340081184543 / 10000000000 : ℝ) : ℝ) := by
    rw [show (99 / 200 : ℝ) - Real.pi * Real.exp (1583 / 800 : ℝ) =
      -(Real.pi * Real.exp (1583 / 800 : ℝ) - (99 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (227537506634175829 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (227537506634175829 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1583_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1583 / 1600 : ℝ) (99 / 100 : ℝ)) :
    (8307 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1719 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1583_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1583_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1584_leftExp :
    (72427429849 / 10000000000 : ℝ) ≤ Real.exp (99 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (99 / 50 : ℝ) (531914678873 / 500000000000 : ℝ)
    (72427429849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1584_rightExp :
    Real.exp (317 / 160 : ℝ) ≤ (18129505187 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (317 / 160 : ℝ) (1063870914393 / 1000000000000 : ℝ)
    (18129505187 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1584_denomUpper :
    Real.exp (55718026588942891 / 2500000000000000 : ℝ) ≤ (23888154562824280369 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (55718026588942891 / 2500000000000000 : ℝ) (1003333696249
    / 500000000000 : ℝ) (23888154562824280369 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1584_denomLower :
    (5802614740651647721 / 1250000000 : ℝ) ≤ Real.exp (27823038649272451 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27823038649272451 / 1250000000000000 : ℝ) (2004863475093
    / 1000000000000 : ℝ) (5802614740651647721 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1584_product_lower :
    (28442179274272451 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (99 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1584_leftExp
    (by norm_num : (0 : ℝ) ≤ (72427429849 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1584_product_upper :
    Real.pi * Real.exp (317 / 160 : ℝ) ≤ (56955526588942891 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1584_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1584_endpointLower :
    (8097 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 100 : ℝ) (317 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (28442179274272451 / 1250000000000000 : ℝ) (Real.pi * Real.exp (99 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1584_product_lower
  have hD : Real.exp (Real.pi * Real.exp (317 / 160 : ℝ) - (99 / 200 : ℝ)) ≤
      (23888154562824280369 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1584_denomUpper
    linarith [hpThetaJensenCell1584_product_upper]
  have hi : (1 / (23888154562824280369 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (317 / 160 : ℝ) - (99 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23888154562824280369 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23888154562824280369 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((99 / 200 : ℝ) - Real.pi * Real.exp (317 / 160 : ℝ)) := by
    rw [show (99 / 200 : ℝ) - Real.pi * Real.exp (317 / 160 : ℝ) =
      -(Real.pi * Real.exp (317 / 160 : ℝ) - (99 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (99 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (99 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1584_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23888154562824280369 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1584_endpointUpper :
    hpThetaJensenKernelEndpointUpper (99 / 100 : ℝ) (317 / 320 : ℝ) ≤ (4189 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (317 / 160 : ℝ)) (56955526588942891 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (317 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1584_product_upper
  have hD : (5802614740651647721 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (99 / 50 : ℝ) - (317 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1584_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1584_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (99 / 50 : ℝ) - (317 / 640 : ℝ)) ≤
      (1 / (5802614740651647721 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5802614740651647721 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((317 / 640 : ℝ) - Real.pi * Real.exp (99 / 50 : ℝ)) ≤
      (2 / (5802614740651647721 / 1250000000 : ℝ) : ℝ) := by
    rw [show (317 / 640 : ℝ) - Real.pi * Real.exp (99 / 50 : ℝ) =
      -(Real.pi * Real.exp (99 / 50 : ℝ) - (317 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (56955526588942891 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (56955526588942891 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1584_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (99 / 100 : ℝ) (317 / 320 : ℝ)) :
    (8097 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4189 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1584_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1584_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1585_leftExp :
    (9064752593 / 1250000000 : ℝ) ≤ Real.exp (317 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (317 / 160 : ℝ) (132983864299 / 125000000000 : ℝ)
    (9064752593 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1585_rightExp :
    Real.exp (793 / 400 : ℝ) ≤ (72608724953 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (793 / 400 : ℝ) (1063912472663 / 1000000000000 : ℝ)
    (72608724953 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1585_denomUpper :
    Real.exp (223153937051270129 / 10000000000000000 : ℝ) ≤ (49141945692328399143 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (223153937051270129 / 10000000000000000 : ℝ)
    (100421774247 / 50000000000 : ℝ) (49141945692328399143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1585_denomLower :
    (9549222386353828729 / 2000000000 : ℝ) ≤ Real.exp (3482277872268507 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3482277872268507 / 156250000000000 : ℝ) (2006627745309 /
    1000000000000 : ℝ) (9549222386353828729 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1585_product_lower :
    (3559719278518507 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (317 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1585_leftExp
    (by norm_num : (0 : ℝ) ≤ (9064752593 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1585_product_upper :
    Real.pi * Real.exp (793 / 400 : ℝ) ≤ (228107062051270129 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1585_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1585_endpointLower :
    (7893 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (317 / 320 : ℝ) (793 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3559719278518507 / 156250000000000 : ℝ) (Real.pi * Real.exp (317 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1585_product_lower
  have hD : Real.exp (Real.pi * Real.exp (793 / 400 : ℝ) - (317 / 640 : ℝ)) ≤
      (49141945692328399143 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1585_denomUpper
    linarith [hpThetaJensenCell1585_product_upper]
  have hi : (1 / (49141945692328399143 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (793 / 400 : ℝ) - (317 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (49141945692328399143 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (49141945692328399143 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((317 / 640 : ℝ) - Real.pi * Real.exp (793 / 400 : ℝ)) := by
    rw [show (317 / 640 : ℝ) - Real.pi * Real.exp (793 / 400 : ℝ) =
      -(Real.pi * Real.exp (793 / 400 : ℝ) - (317 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (317 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (317 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1585_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (49141945692328399143 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1585_endpointUpper :
    hpThetaJensenKernelEndpointUpper (317 / 320 : ℝ) (793 / 800 : ℝ) ≤ (8167 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (793 / 400 : ℝ)) (228107062051270129 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (793 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1585_product_upper
  have hD : (9549222386353828729 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (317 / 160 : ℝ) - (793 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1585_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1585_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (317 / 160 : ℝ) - (793 / 1600 : ℝ)) ≤
      (1 / (9549222386353828729 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9549222386353828729 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((793 / 1600 : ℝ) - Real.pi * Real.exp (317 / 160 : ℝ)) ≤
      (2 / (9549222386353828729 / 2000000000 : ℝ) : ℝ) := by
    rw [show (793 / 1600 : ℝ) - Real.pi * Real.exp (317 / 160 : ℝ) =
      -(Real.pi * Real.exp (317 / 160 : ℝ) - (793 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (228107062051270129 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (228107062051270129 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1585_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (317 / 320 : ℝ) (793 / 800 : ℝ)) :
    (7893 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8167 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1585_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1585_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1586_leftExp :
    (1452174499 / 200000000 : ℝ) ≤ Real.exp (793 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (793 / 400 : ℝ) (531956236331 / 500000000000 : ℝ)
    (1452174499 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1586_rightExp :
    Real.exp (1587 / 800 : ℝ) ≤ (72699542607 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1587 / 800 : ℝ) (212790806511 / 200000000000 : ℝ)
    (72699542607 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1586_denomUpper :
    Real.exp (223436124157352951 / 10000000000000000 : ℝ) ≤ (394909524540896909 / 78125000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (223436124157352951 / 10000000000000000 : ℝ)
    (2010207374199 / 1000000000000 : ℝ) (394909524540896909 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1586_denomLower :
    (24555442456395994557 / 5000000000 : ℝ) ≤ Real.exp (557869036082801 / 25000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (557869036082801 / 25000000000000 : ℝ) (502098950567 /
    250000000000 : ℝ) (24555442456395994557 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1586_product_lower :
    (570267473582801 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (793 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1586_leftExp
    (by norm_num : (0 : ℝ) ≤ (1452174499 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1586_product_upper :
    Real.pi * Real.exp (1587 / 800 : ℝ) ≤ (228392374157352951 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1586_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1586_endpointLower :
    (7693 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (793 / 800 : ℝ) (1587 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (570267473582801 / 25000000000000 : ℝ) (Real.pi * Real.exp (793 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1586_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1587 / 800 : ℝ) - (793 / 1600 : ℝ)) ≤
      (394909524540896909 / 78125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1586_denomUpper
    linarith [hpThetaJensenCell1586_product_upper]
  have hi : (1 / (394909524540896909 / 78125000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1587 / 800 : ℝ) - (793 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (394909524540896909 / 78125000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (394909524540896909 / 78125000 : ℝ) : ℝ) ≤
      2 * Real.exp ((793 / 1600 : ℝ) - Real.pi * Real.exp (1587 / 800 : ℝ)) := by
    rw [show (793 / 1600 : ℝ) - Real.pi * Real.exp (1587 / 800 : ℝ) =
      -(Real.pi * Real.exp (1587 / 800 : ℝ) - (793 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (793 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (793 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1586_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (394909524540896909 / 78125000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1586_endpointUpper :
    hpThetaJensenKernelEndpointUpper (793 / 800 : ℝ) (1587 / 1600 : ℝ) ≤ (7961 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1587 / 800 : ℝ)) (228392374157352951 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1587 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1586_product_upper
  have hD : (24555442456395994557 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (793 / 400 : ℝ) - (1587 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1586_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1586_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (793 / 400 : ℝ) - (1587 / 3200 : ℝ)) ≤
      (1 / (24555442456395994557 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (24555442456395994557 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1587 / 3200 : ℝ) - Real.pi * Real.exp (793 / 400 : ℝ)) ≤
      (2 / (24555442456395994557 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1587 / 3200 : ℝ) - Real.pi * Real.exp (793 / 400 : ℝ) =
      -(Real.pi * Real.exp (793 / 400 : ℝ) - (1587 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (228392374157352951 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (228392374157352951 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1586_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (793 / 800 : ℝ) (1587 / 1600 : ℝ)) :
    (7693 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7961 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1586_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1586_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1587_leftExp :
    (18174885651 / 2500000000 : ℝ) ≤ Real.exp (1587 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1587 / 800 : ℝ) (531977016277 / 500000000000 : ℝ)
    (18174885651 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1587_rightExp :
    Real.exp (397 / 200 : ℝ) ≤ (14558094771 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (397 / 200 : ℝ) (1063995594071 / 1000000000000 : ℝ)
    (14558094771 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1587_denomUpper :
    Real.exp (44743733625910203 / 2000000000000000 : ℝ) ≤ (51997002309191553667 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (44743733625910203 / 2000000000000000 : ℝ) (402396614087
    / 200000000000 : ℝ) (51997002309191553667 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1587_denomLower :
    (50516468923426291459 / 10000000000 : ℝ) ≤ Real.exp (6982181295262049 / 312500000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (6982181295262049 / 312500000000000 : ℝ) (2010167655947 /
    1000000000000 : ℝ) (50516468923426291459 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1587_product_lower :
    (7137259420262049 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1587 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1587_leftExp
    (by norm_num : (0 : ℝ) ≤ (18174885651 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1587_product_upper :
    Real.pi * Real.exp (397 / 200 : ℝ) ≤ (45735608625910203 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1587_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1587_endpointLower :
    (3749 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1587 / 1600 : ℝ) (397 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7137259420262049 / 312500000000000 : ℝ) (Real.pi * Real.exp (1587 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1587_product_lower
  have hD : Real.exp (Real.pi * Real.exp (397 / 200 : ℝ) - (1587 / 3200 : ℝ)) ≤
      (51997002309191553667 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1587_denomUpper
    linarith [hpThetaJensenCell1587_product_upper]
  have hi : (1 / (51997002309191553667 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (397 / 200 : ℝ) - (1587 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51997002309191553667 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51997002309191553667 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1587 / 3200 : ℝ) - Real.pi * Real.exp (397 / 200 : ℝ)) := by
    rw [show (1587 / 3200 : ℝ) - Real.pi * Real.exp (397 / 200 : ℝ) =
      -(Real.pi * Real.exp (397 / 200 : ℝ) - (1587 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1587 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1587 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1587_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51997002309191553667 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1587_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1587 / 1600 : ℝ) (397 / 400 : ℝ) ≤ (7759 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (397 / 200 : ℝ)) (45735608625910203 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (397 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1587_product_upper
  have hD : (50516468923426291459 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1587 / 800 : ℝ) - (397 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1587_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1587_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1587 / 800 : ℝ) - (397 / 800 : ℝ)) ≤
      (1 / (50516468923426291459 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (50516468923426291459 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((397 / 800 : ℝ) - Real.pi * Real.exp (1587 / 800 : ℝ)) ≤
      (2 / (50516468923426291459 / 10000000000 : ℝ) : ℝ) := by
    rw [show (397 / 800 : ℝ) - Real.pi * Real.exp (1587 / 800 : ℝ) =
      -(Real.pi * Real.exp (1587 / 800 : ℝ) - (397 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45735608625910203 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (45735608625910203 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1587_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1587 / 1600 : ℝ) (397 / 400 : ℝ)) :
    (3749 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7759 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1587_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1587_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1588_leftExp :
    (18197618463 / 2500000000 : ℝ) ≤ Real.exp (397 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (397 / 200 : ℝ) (106399559407 / 100000000000 : ℝ)
    (18197618463 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1588_rightExp :
    Real.exp (1589 / 800 : ℝ) ≤ (1822037971 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1589 / 800 : ℝ) (1064037157211 / 1000000000000 : ℝ)
    (1822037971 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1588_denomUpper :
    Real.exp (5600039235427803 / 250000000000000 : ℝ) ≤ (6686126153306158591 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (5600039235427803 / 250000000000000 : ℝ) (1006881291901 /
    500000000000 : ℝ) (6686126153306158591 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1588_denomLower :
    (51964136010180713867 / 10000000000 : ℝ) ≤ Real.exp (6991010791551637 / 312500000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (6991010791551637 / 312500000000000 : ℝ) (1005971658263 /
    500000000000 : ℝ) (51964136010180713867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1588_product_lower :
    (7146186572801637 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (397 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1588_leftExp
    (by norm_num : (0 : ℝ) ≤ (18197618463 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1588_product_upper :
    Real.pi * Real.exp (1589 / 800 : ℝ) ≤ (5724101735427803 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1588_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1588_endpointLower :
    (1827 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (397 / 400 : ℝ) (1589 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7146186572801637 / 312500000000000 : ℝ) (Real.pi * Real.exp (397 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1588_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1589 / 800 : ℝ) - (397 / 800 : ℝ)) ≤
      (6686126153306158591 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1588_denomUpper
    linarith [hpThetaJensenCell1588_product_upper]
  have hi : (1 / (6686126153306158591 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1589 / 800 : ℝ) - (397 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6686126153306158591 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6686126153306158591 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((397 / 800 : ℝ) - Real.pi * Real.exp (1589 / 800 : ℝ)) := by
    rw [show (397 / 800 : ℝ) - Real.pi * Real.exp (1589 / 800 : ℝ) =
      -(Real.pi * Real.exp (1589 / 800 : ℝ) - (397 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (397 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (397 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1588_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6686126153306158591 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1588_endpointUpper :
    hpThetaJensenKernelEndpointUpper (397 / 400 : ℝ) (1589 / 1600 : ℝ) ≤ (7563 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1589 / 800 : ℝ)) (5724101735427803 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1589 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1588_product_upper
  have hD : (51964136010180713867 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (397 / 200 : ℝ) - (1589 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1588_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1588_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (397 / 200 : ℝ) - (1589 / 3200 : ℝ)) ≤
      (1 / (51964136010180713867 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (51964136010180713867 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1589 / 3200 : ℝ) - Real.pi * Real.exp (397 / 200 : ℝ)) ≤
      (2 / (51964136010180713867 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1589 / 3200 : ℝ) - Real.pi * Real.exp (397 / 200 : ℝ) =
      -(Real.pi * Real.exp (397 / 200 : ℝ) - (1589 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5724101735427803 / 250000000000000 : ℝ) ^ 2 - 6 *
      (5724101735427803 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1588_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (397 / 400 : ℝ) (1589 / 1600 : ℝ)) :
    (1827 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7563 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1588_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1588_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1589_leftExp :
    (72881518837 / 10000000000 : ℝ) ≤ Real.exp (1589 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1589 / 800 : ℝ) (106403715721 / 100000000000 : ℝ)
    (72881518837 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1589_rightExp :
    Real.exp (159 / 80 : ℝ) ≤ (729726777 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (159 / 80 : ℝ) (532039360987 / 500000000000 : ℝ)
    (729726777 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1589_denomUpper :
    Real.exp (2242848284535761 / 100000000000000 : ℝ) ≤ (11005159287671617683 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (2242848284535761 / 100000000000000 : ℝ) (1007772962191 /
    500000000000 : ℝ) (11005159287671617683 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1589_denomLower :
    (10691039874338639659 / 2000000000 : ℝ) ≤ Real.exp (27999405815771063 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (27999405815771063 / 1250000000000000 : ℝ) (2013722794159
    / 1000000000000 : ℝ) (10691039874338639659 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1589_product_lower :
    (28620499565771063 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1589 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1589_leftExp
    (by norm_num : (0 : ℝ) ≤ (72881518837 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1589_product_upper :
    Real.pi * Real.exp (159 / 80 : ℝ) ≤ (2292504534535761 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1589_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1589_endpointLower :
    (3561 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1589 / 1600 : ℝ) (159 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (28620499565771063 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1589 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1589_product_lower
  have hD : Real.exp (Real.pi * Real.exp (159 / 80 : ℝ) - (1589 / 3200 : ℝ)) ≤
      (11005159287671617683 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1589_denomUpper
    linarith [hpThetaJensenCell1589_product_upper]
  have hi : (1 / (11005159287671617683 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (159 / 80 : ℝ) - (1589 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11005159287671617683 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11005159287671617683 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1589 / 3200 : ℝ) - Real.pi * Real.exp (159 / 80 : ℝ)) := by
    rw [show (1589 / 3200 : ℝ) - Real.pi * Real.exp (159 / 80 : ℝ) =
      -(Real.pi * Real.exp (159 / 80 : ℝ) - (1589 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1589 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1589 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1589_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11005159287671617683 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1589_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1589 / 1600 : ℝ) (159 / 160 : ℝ) ≤ (7371 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (159 / 80 : ℝ)) (2292504534535761 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (159 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1589_product_upper
  have hD : (10691039874338639659 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1589 / 800 : ℝ) - (159 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1589_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1589_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1589 / 800 : ℝ) - (159 / 320 : ℝ)) ≤
      (1 / (10691039874338639659 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10691039874338639659 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((159 / 320 : ℝ) - Real.pi * Real.exp (1589 / 800 : ℝ)) ≤
      (2 / (10691039874338639659 / 2000000000 : ℝ) : ℝ) := by
    rw [show (159 / 320 : ℝ) - Real.pi * Real.exp (1589 / 800 : ℝ) =
      -(Real.pi * Real.exp (1589 / 800 : ℝ) - (159 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2292504534535761 / 100000000000000 : ℝ) ^ 2 - 6 *
      (2292504534535761 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1589_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1589 / 1600 : ℝ) (159 / 160 : ℝ)) :
    (3561 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7371 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1589_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1589_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1590_leftExp :
    (72972677697 / 10000000000 : ℝ) ≤ Real.exp (159 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (159 / 80 : ℝ) (1064078721973 / 1000000000000 : ℝ)
    (72972677697 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1590_rightExp :
    Real.exp (1591 / 800 : ℝ) ≤ (73063950581 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1591 / 800 : ℝ) (1064120288361 / 1000000000000 : ℝ)
    (73063950581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1590_denomUpper :
    Real.exp (224568445697615533 / 10000000000000000 : ℝ) ≤ (14152191164442804551 / 2500000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (224568445697615533 / 10000000000000000 : ℝ)
    (403466620489 / 200000000000 : ℝ) (14152191164442804551 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1590_denomLower :
    (54991014694794653541 / 10000000000 : ℝ) ≤ Real.exp (28034813183934203 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (28034813183934203 / 1250000000000000 : ℝ) (125969131183
    / 62500000000 : ℝ) (54991014694794653541 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1590_product_lower :
    (28656297558934203 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (159 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1590_leftExp
    (by norm_num : (0 : ℝ) ≤ (72972677697 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1590_product_upper :
    Real.pi * Real.exp (1591 / 800 : ℝ) ≤ (229537195697615533 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1590_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1590_endpointLower :
    (6941 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (159 / 160 : ℝ) (1591 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (28656297558934203 / 1250000000000000 : ℝ) (Real.pi * Real.exp (159 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1590_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1591 / 800 : ℝ) - (159 / 320 : ℝ)) ≤
      (14152191164442804551 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1590_denomUpper
    linarith [hpThetaJensenCell1590_product_upper]
  have hi : (1 / (14152191164442804551 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1591 / 800 : ℝ) - (159 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14152191164442804551 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14152191164442804551 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((159 / 320 : ℝ) - Real.pi * Real.exp (1591 / 800 : ℝ)) := by
    rw [show (159 / 320 : ℝ) - Real.pi * Real.exp (1591 / 800 : ℝ) =
      -(Real.pi * Real.exp (1591 / 800 : ℝ) - (159 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (159 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (159 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1590_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14152191164442804551 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1590_endpointUpper :
    hpThetaJensenKernelEndpointUpper (159 / 160 : ℝ) (1591 / 1600 : ℝ) ≤ (7183 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1591 / 800 : ℝ)) (229537195697615533 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1591 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1590_product_upper
  have hD : (54991014694794653541 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (159 / 80 : ℝ) - (1591 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1590_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1590_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (159 / 80 : ℝ) - (1591 / 3200 : ℝ)) ≤
      (1 / (54991014694794653541 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (54991014694794653541 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1591 / 3200 : ℝ) - Real.pi * Real.exp (159 / 80 : ℝ)) ≤
      (2 / (54991014694794653541 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1591 / 3200 : ℝ) - Real.pi * Real.exp (159 / 80 : ℝ) =
      -(Real.pi * Real.exp (159 / 80 : ℝ) - (1591 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (229537195697615533 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (229537195697615533 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1590_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (159 / 160 : ℝ) (1591 / 1600 : ℝ)) :
    (6941 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7183 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1590_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1590_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1591_leftExp :
    (36531975289 / 5000000000 : ℝ) ≤ Real.exp (1591 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1591 / 800 : ℝ) (26603007209 / 25000000000 : ℝ)
    (36531975289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1591_rightExp :
    Real.exp (199 / 100 : ℝ) ≤ (585242701 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (199 / 100 : ℝ) (266040464093 / 250000000000 : ℝ)
    (585242701 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1591_denomUpper :
    Real.exp (1798819372762693 / 80000000000000 : ℝ) ≤ (58239360045486603521 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (1798819372762693 / 80000000000000 : ℝ) (2019124128211 /
    1000000000000 : ℝ) (58239360045486603521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1591_denomLower :
    (11314596360994870759 / 2000000000 : ℝ) ≤ Real.exp (14035132664015011 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (14035132664015011 / 625000000000000 : ℝ) (1008646620551
    / 500000000000 : ℝ) (11314596360994870759 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1591_product_lower :
    (14346070164015011 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1591 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1591_leftExp
    (by norm_num : (0 : ℝ) ≤ (36531975289 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1591_product_upper :
    Real.pi * Real.exp (199 / 100 : ℝ) ≤ (1838594372762693 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1591_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1591_endpointLower :
    (1691 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1591 / 1600 : ℝ) (199 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14346070164015011 / 625000000000000 : ℝ) (Real.pi * Real.exp (1591 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1591_product_lower
  have hD : Real.exp (Real.pi * Real.exp (199 / 100 : ℝ) - (1591 / 3200 : ℝ)) ≤
      (58239360045486603521 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1591_denomUpper
    linarith [hpThetaJensenCell1591_product_upper]
  have hi : (1 / (58239360045486603521 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (199 / 100 : ℝ) - (1591 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (58239360045486603521 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (58239360045486603521 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1591 / 3200 : ℝ) - Real.pi * Real.exp (199 / 100 : ℝ)) := by
    rw [show (1591 / 3200 : ℝ) - Real.pi * Real.exp (199 / 100 : ℝ) =
      -(Real.pi * Real.exp (199 / 100 : ℝ) - (1591 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1591 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1591 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1591_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (58239360045486603521 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1591_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1591 / 1600 : ℝ) (199 / 200 : ℝ) ≤ (7001 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (199 / 100 : ℝ)) (1838594372762693 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (199 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1591_product_upper
  have hD : (11314596360994870759 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1591 / 800 : ℝ) - (199 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1591_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1591_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1591 / 800 : ℝ) - (199 / 400 : ℝ)) ≤
      (1 / (11314596360994870759 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11314596360994870759 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((199 / 400 : ℝ) - Real.pi * Real.exp (1591 / 800 : ℝ)) ≤
      (2 / (11314596360994870759 / 2000000000 : ℝ) : ℝ) := by
    rw [show (199 / 400 : ℝ) - Real.pi * Real.exp (1591 / 800 : ℝ) =
      -(Real.pi * Real.exp (1591 / 800 : ℝ) - (199 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1838594372762693 / 80000000000000 : ℝ) ^ 2 - 6 *
      (1838594372762693 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1591_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1591 / 1600 : ℝ) (199 / 200 : ℝ)) :
    (1691 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7001 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1591_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1591_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1592_leftExp :
    (36577668811 / 5000000000 : ℝ) ≤ Real.exp (199 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (199 / 100 : ℝ) (1064161856371 / 1000000000000 : ℝ)
    (36577668811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1592_rightExp :
    Real.exp (1593 / 800 : ℝ) ≤ (73246838973 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1593 / 800 : ℝ) (532101713003 / 500000000000 : ℝ)
    (73246838973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1592_denomUpper :
    Real.exp (225136756589703989 / 10000000000000000 : ℝ) ≤ (59919075790743161009 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (225136756589703989 / 10000000000000000 : ℝ)
    (2020919011911 / 1000000000000 : ℝ) (59919075790743161009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1592_denomLower :
    (5820254594772738511 / 1000000000 : ℝ) ≤ Real.exp (14052881151910889 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14052881151910889 / 625000000000000 : ℝ) (2019084230901
    / 1000000000000 : ℝ) (5820254594772738511 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1592_product_lower :
    (14364013964410889 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (199 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1592_leftExp
    (by norm_num : (0 : ℝ) ≤ (36577668811 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1592_product_upper :
    Real.pi * Real.exp (1593 / 800 : ℝ) ≤ (230111756589703989 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1592_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1592_endpointLower :
    (6591 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (199 / 200 : ℝ) (1593 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14364013964410889 / 625000000000000 : ℝ) (Real.pi * Real.exp (199 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1592_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1593 / 800 : ℝ) - (199 / 400 : ℝ)) ≤
      (59919075790743161009 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1592_denomUpper
    linarith [hpThetaJensenCell1592_product_upper]
  have hi : (1 / (59919075790743161009 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1593 / 800 : ℝ) - (199 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (59919075790743161009 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (59919075790743161009 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((199 / 400 : ℝ) - Real.pi * Real.exp (1593 / 800 : ℝ)) := by
    rw [show (199 / 400 : ℝ) - Real.pi * Real.exp (1593 / 800 : ℝ) =
      -(Real.pi * Real.exp (1593 / 800 : ℝ) - (199 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (199 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (199 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1592_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (59919075790743161009 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1592_endpointUpper :
    hpThetaJensenKernelEndpointUpper (199 / 200 : ℝ) (1593 / 1600 : ℝ) ≤ (3411 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1593 / 800 : ℝ)) (230111756589703989 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1593 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1592_product_upper
  have hD : (5820254594772738511 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (199 / 100 : ℝ) - (1593 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1592_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1592_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (199 / 100 : ℝ) - (1593 / 3200 : ℝ)) ≤
      (1 / (5820254594772738511 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5820254594772738511 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1593 / 3200 : ℝ) - Real.pi * Real.exp (199 / 100 : ℝ)) ≤
      (2 / (5820254594772738511 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1593 / 3200 : ℝ) - Real.pi * Real.exp (199 / 100 : ℝ) =
      -(Real.pi * Real.exp (199 / 100 : ℝ) - (1593 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (230111756589703989 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (230111756589703989 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1592_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (199 / 200 : ℝ) (1593 / 1600 : ℝ)) :
    (6591 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3411 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1592_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1592_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1593_leftExp :
    (73246838969 / 10000000000 : ℝ) ≤ Real.exp (1593 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1593 / 800 : ℝ) (212840685201 / 200000000000 : ℝ)
    (73246838969 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1593_rightExp :
    Real.exp (797 / 400 : ℝ) ≤ (73338454769 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (797 / 400 : ℝ) (66515312329 / 62500000000 : ℝ)
    (73338454769 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1593_denomUpper :
    Real.exp (225421451133107017 / 10000000000000000 : ℝ) ≤ (12329890753897490657 / 2000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (225421451133107017 / 10000000000000000 : ℝ)
    (252839720483 / 125000000000 : ℝ) (12329890753897490657 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1593_denomLower :
    (59881199349209669351 / 10000000000 : ℝ) ≤ Real.exp (28141304166287331 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (28141304166287331 / 1250000000000000 : ℝ) (2020879078537
    / 1000000000000 : ℝ) (59881199349209669351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1593_product_lower :
    (28763960416287331 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1593 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1593_leftExp
    (by norm_num : (0 : ℝ) ≤ (73246838969 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1593_product_upper :
    Real.pi * Real.exp (797 / 400 : ℝ) ≤ (230399576133107017 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1593_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1593_endpointLower :
    (6423 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1593 / 1600 : ℝ) (797 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (28763960416287331 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1593 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1593_product_lower
  have hD : Real.exp (Real.pi * Real.exp (797 / 400 : ℝ) - (1593 / 3200 : ℝ)) ≤
      (12329890753897490657 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1593_denomUpper
    linarith [hpThetaJensenCell1593_product_upper]
  have hi : (1 / (12329890753897490657 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (797 / 400 : ℝ) - (1593 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12329890753897490657 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12329890753897490657 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1593 / 3200 : ℝ) - Real.pi * Real.exp (797 / 400 : ℝ)) := by
    rw [show (1593 / 3200 : ℝ) - Real.pi * Real.exp (797 / 400 : ℝ) =
      -(Real.pi * Real.exp (797 / 400 : ℝ) - (1593 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1593 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1593 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1593_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12329890753897490657 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1593_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1593 / 1600 : ℝ) (797 / 800 : ℝ) ≤ (831 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (797 / 400 : ℝ)) (230399576133107017 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (797 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1593_product_upper
  have hD : (59881199349209669351 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1593 / 800 : ℝ) - (797 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1593_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1593_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1593 / 800 : ℝ) - (797 / 1600 : ℝ)) ≤
      (1 / (59881199349209669351 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (59881199349209669351 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((797 / 1600 : ℝ) - Real.pi * Real.exp (1593 / 800 : ℝ)) ≤
      (2 / (59881199349209669351 / 10000000000 : ℝ) : ℝ) := by
    rw [show (797 / 1600 : ℝ) - Real.pi * Real.exp (1593 / 800 : ℝ) =
      -(Real.pi * Real.exp (1593 / 800 : ℝ) - (797 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (230399576133107017 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (230399576133107017 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1593_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1593 / 1600 : ℝ) (797 / 800 : ℝ)) :
    (6423 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (831 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1593_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1593_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1594_leftExp :
    (36669227383 / 5000000000 : ℝ) ≤ Real.exp (797 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (797 / 400 : ℝ) (1064244997263 / 1000000000000 : ℝ)
    (36669227383 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1594_rightExp :
    Real.exp (319 / 160 : ℝ) ≤ (73430185159 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (319 / 160 : ℝ) (1064286570147 / 1000000000000 : ℝ)
    (73430185159 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1594_denomUpper :
    Real.exp (225706505684218287 / 10000000000000000 : ℝ) ≤ (63432086174022353273 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (225706505684218287 / 10000000000000000 : ℝ)
    (1012260197229 / 500000000000 : ℝ) (63432086174022353273 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1594_denomLower :
    (15402620740884022183 / 2500000000 : ℝ) ≤ Real.exp (14088445486576717 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (14088445486576717 / 625000000000000 : ℝ) (1011338897193
    / 500000000000 : ℝ) (15402620740884022183 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1594_product_lower :
    (14399968924076717 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (797 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1594_leftExp
    (by norm_num : (0 : ℝ) ≤ (36669227383 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1594_product_upper :
    Real.pi * Real.exp (319 / 160 : ℝ) ≤ (230687755684218287 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1594_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1594_endpointLower :
    (6259 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (797 / 800 : ℝ) (319 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14399968924076717 / 625000000000000 : ℝ) (Real.pi * Real.exp (797 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1594_product_lower
  have hD : Real.exp (Real.pi * Real.exp (319 / 160 : ℝ) - (797 / 1600 : ℝ)) ≤
      (63432086174022353273 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1594_denomUpper
    linarith [hpThetaJensenCell1594_product_upper]
  have hi : (1 / (63432086174022353273 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (319 / 160 : ℝ) - (797 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (63432086174022353273 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (63432086174022353273 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((797 / 1600 : ℝ) - Real.pi * Real.exp (319 / 160 : ℝ)) := by
    rw [show (797 / 1600 : ℝ) - Real.pi * Real.exp (319 / 160 : ℝ) =
      -(Real.pi * Real.exp (319 / 160 : ℝ) - (797 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (797 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (797 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1594_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (63432086174022353273 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1594_endpointUpper :
    hpThetaJensenKernelEndpointUpper (797 / 800 : ℝ) (319 / 320 : ℝ) ≤ (3239 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (319 / 160 : ℝ)) (230687755684218287 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (319 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1594_product_upper
  have hD : (15402620740884022183 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (797 / 400 : ℝ) - (319 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1594_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1594_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (797 / 400 : ℝ) - (319 / 640 : ℝ)) ≤
      (1 / (15402620740884022183 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15402620740884022183 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((319 / 640 : ℝ) - Real.pi * Real.exp (797 / 400 : ℝ)) ≤
      (2 / (15402620740884022183 / 2500000000 : ℝ) : ℝ) := by
    rw [show (319 / 640 : ℝ) - Real.pi * Real.exp (797 / 400 : ℝ) =
      -(Real.pi * Real.exp (797 / 400 : ℝ) - (319 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (230687755684218287 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (230687755684218287 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1594_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (797 / 800 : ℝ) (319 / 320 : ℝ)) :
    (6259 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3239 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1594_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1594_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1595_leftExp :
    (14686037031 / 2000000000 : ℝ) ≤ Real.exp (319 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (319 / 160 : ℝ) (532143285073 / 500000000000 : ℝ)
    (14686037031 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1595_rightExp :
    Real.exp (399 / 200 : ℝ) ≤ (73522030281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (399 / 200 : ℝ) (1064328144653 / 1000000000000 : ℝ)
    (73522030281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1595_denomUpper :
    Real.exp (225991920676577633 / 10000000000000000 : ℝ) ≤ (65268617013892057379 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (225991920676577633 / 10000000000000000 : ℝ)
    (2026326913953 / 1000000000000 : ℝ) (65268617013892057379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1595_denomLower :
    (6339198790119977421 / 1000000000 : ℝ) ≤ Real.exp (5642504556036669 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5642504556036669 / 250000000000000 : ℝ) (2024480388759 /
    1000000000000 : ℝ) (6339198790119977421 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1595_product_lower :
    (5767192056036669 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (319 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1595_leftExp
    (by norm_num : (0 : ℝ) ≤ (14686037031 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1595_product_upper :
    Real.pi * Real.exp (399 / 200 : ℝ) ≤ (230976295676577633 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1595_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1595_endpointLower :
    (3049 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (319 / 320 : ℝ) (399 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5767192056036669 / 250000000000000 : ℝ) (Real.pi * Real.exp (319 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1595_product_lower
  have hD : Real.exp (Real.pi * Real.exp (399 / 200 : ℝ) - (319 / 640 : ℝ)) ≤
      (65268617013892057379 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1595_denomUpper
    linarith [hpThetaJensenCell1595_product_upper]
  have hi : (1 / (65268617013892057379 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (399 / 200 : ℝ) - (319 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65268617013892057379 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65268617013892057379 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((319 / 640 : ℝ) - Real.pi * Real.exp (399 / 200 : ℝ)) := by
    rw [show (319 / 640 : ℝ) - Real.pi * Real.exp (399 / 200 : ℝ) =
      -(Real.pi * Real.exp (399 / 200 : ℝ) - (319 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (319 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (319 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1595_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65268617013892057379 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1595_endpointUpper :
    hpThetaJensenKernelEndpointUpper (319 / 320 : ℝ) (399 / 400 : ℝ) ≤ (6313 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (399 / 200 : ℝ)) (230976295676577633 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (399 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1595_product_upper
  have hD : (6339198790119977421 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (319 / 160 : ℝ) - (399 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1595_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1595_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (319 / 160 : ℝ) - (399 / 800 : ℝ)) ≤
      (1 / (6339198790119977421 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6339198790119977421 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((399 / 800 : ℝ) - Real.pi * Real.exp (319 / 160 : ℝ)) ≤
      (2 / (6339198790119977421 / 1000000000 : ℝ) : ℝ) := by
    rw [show (399 / 800 : ℝ) - Real.pi * Real.exp (319 / 160 : ℝ) =
      -(Real.pi * Real.exp (319 / 160 : ℝ) - (399 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (230976295676577633 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (230976295676577633 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1595_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (319 / 320 : ℝ) (399 / 400 : ℝ)) :
    (3049 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6313 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1595_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1595_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1596_leftExp :
    (36761015139 / 5000000000 : ℝ) ≤ Real.exp (399 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (399 / 200 : ℝ) (266082036163 / 250000000000 : ℝ)
    (36761015139 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1596_rightExp :
    Real.exp (1597 / 800 : ℝ) ≤ (73613990281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1597 / 800 : ℝ) (1064369720783 / 1000000000000 : ℝ)
    (73613990281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1596_denomUpper :
    Real.exp (226277696568857633 / 10000000000000000 : ℝ) ≤ (33580372093508535519 / 5000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (226277696568857633 / 10000000000000000 : ℝ)
    (1014068666399 / 500000000000 : ℝ) (33580372093508535519 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1596_denomLower :
    (6522735720833237759 / 1000000000 : ℝ) ≤ Real.exp (14124099821570161 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14124099821570161 / 625000000000000 : ℝ) (1013143435997
    / 500000000000 : ℝ) (6522735720833237759 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1596_product_lower :
    (14436013884070161 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (399 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1596_leftExp
    (by norm_num : (0 : ℝ) ≤ (36761015139 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1596_product_upper :
    Real.pi * Real.exp (1597 / 800 : ℝ) ≤ (231265196568857633 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1596_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1596_endpointLower :
    (2971 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (399 / 400 : ℝ) (1597 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14436013884070161 / 625000000000000 : ℝ) (Real.pi * Real.exp (399 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1596_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1597 / 800 : ℝ) - (399 / 800 : ℝ)) ≤
      (33580372093508535519 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1596_denomUpper
    linarith [hpThetaJensenCell1596_product_upper]
  have hi : (1 / (33580372093508535519 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1597 / 800 : ℝ) - (399 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (33580372093508535519 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (33580372093508535519 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((399 / 800 : ℝ) - Real.pi * Real.exp (1597 / 800 : ℝ)) := by
    rw [show (399 / 800 : ℝ) - Real.pi * Real.exp (1597 / 800 : ℝ) =
      -(Real.pi * Real.exp (1597 / 800 : ℝ) - (399 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (399 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (399 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1596_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (33580372093508535519 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1596_endpointUpper :
    hpThetaJensenKernelEndpointUpper (399 / 400 : ℝ) (1597 / 1600 : ℝ) ≤ (6151 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1597 / 800 : ℝ)) (231265196568857633 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1597 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1596_product_upper
  have hD : (6522735720833237759 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (399 / 200 : ℝ) - (1597 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1596_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1596_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (399 / 200 : ℝ) - (1597 / 3200 : ℝ)) ≤
      (1 / (6522735720833237759 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6522735720833237759 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1597 / 3200 : ℝ) - Real.pi * Real.exp (399 / 200 : ℝ)) ≤
      (2 / (6522735720833237759 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1597 / 3200 : ℝ) - Real.pi * Real.exp (399 / 200 : ℝ) =
      -(Real.pi * Real.exp (399 / 200 : ℝ) - (1597 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (231265196568857633 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (231265196568857633 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1596_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (399 / 400 : ℝ) (1597 / 1600 : ℝ)) :
    (2971 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6151 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1596_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1596_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1597_leftExp :
    (36806995139 / 5000000000 : ℝ) ≤ Real.exp (1597 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1597 / 800 : ℝ) (532184860391 / 500000000000 : ℝ)
    (36806995139 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1597_rightExp :
    Real.exp (799 / 400 : ℝ) ≤ (9213258163 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (799 / 400 : ℝ) (1064411298537 / 1000000000000 : ℝ)
    (9213258163 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1597_denomUpper :
    Real.exp (28320479227073659 / 1250000000000000 : ℝ) ≤ (17277555281638050229 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (28320479227073659 / 1250000000000000 : ℝ) (507487915363
    / 250000000000 : ℝ) (17277555281638050229 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1597_denomLower :
    (16779571912007062333 / 2500000000 : ℝ) ≤ Real.exp (14141960809090161 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (14141960809090161 / 625000000000000 : ℝ) (25351215681 /
    12500000000 : ℝ) (16779571912007062333 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1597_product_lower :
    (14454070184090161 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1597 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1597_leftExp
    (by norm_num : (0 : ℝ) ≤ (36806995139 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1597_product_upper :
    Real.pi * Real.exp (799 / 400 : ℝ) ≤ (28944307352073659 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1597_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1597_endpointLower :
    (5789 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1597 / 1600 : ℝ) (799 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14454070184090161 / 625000000000000 : ℝ) (Real.pi * Real.exp (1597 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1597_product_lower
  have hD : Real.exp (Real.pi * Real.exp (799 / 400 : ℝ) - (1597 / 3200 : ℝ)) ≤
      (17277555281638050229 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1597_denomUpper
    linarith [hpThetaJensenCell1597_product_upper]
  have hi : (1 / (17277555281638050229 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (799 / 400 : ℝ) - (1597 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17277555281638050229 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17277555281638050229 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1597 / 3200 : ℝ) - Real.pi * Real.exp (799 / 400 : ℝ)) := by
    rw [show (1597 / 3200 : ℝ) - Real.pi * Real.exp (799 / 400 : ℝ) =
      -(Real.pi * Real.exp (799 / 400 : ℝ) - (1597 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1597 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1597 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1597_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17277555281638050229 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1597_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1597 / 1600 : ℝ) (799 / 800 : ℝ) ≤ (5993 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (799 / 400 : ℝ)) (28944307352073659 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (799 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1597_product_upper
  have hD : (16779571912007062333 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1597 / 800 : ℝ) - (799 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1597_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1597_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1597 / 800 : ℝ) - (799 / 1600 : ℝ)) ≤
      (1 / (16779571912007062333 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16779571912007062333 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((799 / 1600 : ℝ) - Real.pi * Real.exp (1597 / 800 : ℝ)) ≤
      (2 / (16779571912007062333 / 2500000000 : ℝ) : ℝ) := by
    rw [show (799 / 1600 : ℝ) - Real.pi * Real.exp (1597 / 800 : ℝ) =
      -(Real.pi * Real.exp (1597 / 800 : ℝ) - (799 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28944307352073659 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (28944307352073659 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1597_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1597 / 1600 : ℝ) (799 / 800 : ℝ)) :
    (5789 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5993 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1597_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1597_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1598_leftExp :
    (737060653 / 100000000 : ℝ) ≤ Real.exp (799 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (799 / 400 : ℝ) (133051412317 / 125000000000 : ℝ)
    (737060653 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1598_rightExp :
    Real.exp (1599 / 800 : ℝ) ≤ (73798255493 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1599 / 800 : ℝ) (266113219479 / 250000000000 : ℝ)
    (73798255493 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1598_denomUpper :
    Real.exp (226850332869020349 / 10000000000000000 : ℝ) ≤ (35559429329295216133 / 5000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (226850332869020349 / 10000000000000000 : ℝ)
    (507942477591 / 250000000000 : ℝ) (35559429329295216133 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1598_denomLower :
    (4316658221433698099 / 625000000 : ℝ) ≤ Real.exp (283196887622447 / 12500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (283196887622447 / 12500000000000 : ℝ) (2029911546677 /
    1000000000000 : ℝ) (4316658221433698099 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1598_product_lower :
    (289442981372447 / 12500000000000 : ℝ) ≤ Real.pi * Real.exp (799 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1598_leftExp
    (by norm_num : (0 : ℝ) ≤ (737060653 / 100000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1598_product_upper :
    Real.pi * Real.exp (1599 / 800 : ℝ) ≤ (231844082869020349 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1598_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1598_endpointLower :
    (141 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (799 / 800 : ℝ) (1599 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (289442981372447 / 12500000000000 : ℝ) (Real.pi * Real.exp (799 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1598_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1599 / 800 : ℝ) - (799 / 1600 : ℝ)) ≤
      (35559429329295216133 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1598_denomUpper
    linarith [hpThetaJensenCell1598_product_upper]
  have hi : (1 / (35559429329295216133 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1599 / 800 : ℝ) - (799 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (35559429329295216133 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (35559429329295216133 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((799 / 1600 : ℝ) - Real.pi * Real.exp (1599 / 800 : ℝ)) := by
    rw [show (799 / 1600 : ℝ) - Real.pi * Real.exp (1599 / 800 : ℝ) =
      -(Real.pi * Real.exp (1599 / 800 : ℝ) - (799 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (799 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (799 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1598_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (35559429329295216133 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1598_endpointUpper :
    hpThetaJensenKernelEndpointUpper (799 / 800 : ℝ) (1599 / 1600 : ℝ) ≤ (5839 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1599 / 800 : ℝ)) (231844082869020349 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1599 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1598_product_upper
  have hD : (4316658221433698099 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (799 / 400 : ℝ) - (1599 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1598_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1598_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (799 / 400 : ℝ) - (1599 / 3200 : ℝ)) ≤
      (1 / (4316658221433698099 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4316658221433698099 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1599 / 3200 : ℝ) - Real.pi * Real.exp (799 / 400 : ℝ)) ≤
      (2 / (4316658221433698099 / 625000000 : ℝ) : ℝ) := by
    rw [show (1599 / 3200 : ℝ) - Real.pi * Real.exp (799 / 400 : ℝ) =
      -(Real.pi * Real.exp (799 / 400 : ℝ) - (1599 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (231844082869020349 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (231844082869020349 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1598_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (799 / 800 : ℝ) (1599 / 1600 : ℝ)) :
    (141 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5839 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1598_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1598_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1599_leftExp :
    (7379825549 / 1000000000 : ℝ) ≤ Real.exp (1599 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1599 / 800 : ℝ) (212890575583 / 200000000000 : ℝ)
    (7379825549 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1599_rightExp :
    Real.exp (2 / 1 : ℝ) ≤ (7389056099 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2 / 1 : ℝ) (532247229459 / 500000000000 : ℝ)
    (7389056099 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1599_denomUpper :
    Real.exp (22713719417225707 / 1000000000000000 : ℝ) ≤ (73188526970144869623 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (22713719417225707 / 1000000000000000 : ℝ) (406718417999
    / 200000000000 : ℝ) (73188526970144869623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1599_denomLower :
    (71073898636155317803 / 10000000000 : ℝ) ≤ Real.exp (2835550113266751 / 125000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (2835550113266751 / 125000000000000 : ℝ) (507932439773 /
    250000000000 : ℝ) (71073898636155317803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1599_product_lower :
    (2898050113266751 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1599 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1599_leftExp
    (by norm_num : (0 : ℝ) ≤ (7379825549 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1599_product_upper :
    Real.pi * Real.exp (2 / 1 : ℝ) ≤ (23213406917225707 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1599_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1599_endpointLower :
    (1099 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1599 / 1600 : ℝ) (1 / 1 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2898050113266751 / 125000000000000 : ℝ) (Real.pi * Real.exp (1599 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1599_product_lower
  have hD : Real.exp (Real.pi * Real.exp (2 / 1 : ℝ) - (1599 / 3200 : ℝ)) ≤
      (73188526970144869623 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1599_denomUpper
    linarith [hpThetaJensenCell1599_product_upper]
  have hi : (1 / (73188526970144869623 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (2 / 1 : ℝ) - (1599 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (73188526970144869623 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (73188526970144869623 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1599 / 3200 : ℝ) - Real.pi * Real.exp (2 / 1 : ℝ)) := by
    rw [show (1599 / 3200 : ℝ) - Real.pi * Real.exp (2 / 1 : ℝ) =
      -(Real.pi * Real.exp (2 / 1 : ℝ) - (1599 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1599 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1599 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1599_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (73188526970144869623 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1599_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1599 / 1600 : ℝ) (1 / 1 : ℝ) ≤ (5689 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (2 / 1 : ℝ)) (23213406917225707 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 1 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1599_product_upper
  have hD : (71073898636155317803 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1599 / 800 : ℝ) - (1 / 2 : ℝ)) := by
    apply le_trans hpThetaJensenCell1599_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1599_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1599 / 800 : ℝ) - (1 / 2 : ℝ)) ≤
      (1 / (71073898636155317803 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (71073898636155317803 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 2 : ℝ) - Real.pi * Real.exp (1599 / 800 : ℝ)) ≤
      (2 / (71073898636155317803 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1 / 2 : ℝ) - Real.pi * Real.exp (1599 / 800 : ℝ) =
      -(Real.pi * Real.exp (1599 / 800 : ℝ) - (1 / 2 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23213406917225707 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (23213406917225707 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1599_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1599 / 1600 : ℝ) (1 / 1 : ℝ)) :
    (1099 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5689 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1599_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1599_endpointUpper

def hpThetaJensenCellsBatch079Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8967 / 10000000000 : ℝ)
  | 1 => (4371 / 5000000000 : ℝ)
  | 2 => (4261 / 5000000000 : ℝ)
  | 3 => (8307 / 10000000000 : ℝ)
  | 4 => (8097 / 10000000000 : ℝ)
  | 5 => (7893 / 10000000000 : ℝ)
  | 6 => (7693 / 10000000000 : ℝ)
  | 7 => (3749 / 5000000000 : ℝ)
  | 8 => (1827 / 2500000000 : ℝ)
  | 9 => (3561 / 5000000000 : ℝ)
  | 10 => (6941 / 10000000000 : ℝ)
  | 11 => (1691 / 2500000000 : ℝ)
  | 12 => (6591 / 10000000000 : ℝ)
  | 13 => (6423 / 10000000000 : ℝ)
  | 14 => (6259 / 10000000000 : ℝ)
  | 15 => (3049 / 5000000000 : ℝ)
  | 16 => (2971 / 5000000000 : ℝ)
  | 17 => (5789 / 10000000000 : ℝ)
  | 18 => (141 / 250000000 : ℝ)
  | 19 => (1099 / 2000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch079Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9277 / 10000000000 : ℝ)
  | 1 => (2261 / 2500000000 : ℝ)
  | 2 => (8817 / 10000000000 : ℝ)
  | 3 => (1719 / 2000000000 : ℝ)
  | 4 => (4189 / 5000000000 : ℝ)
  | 5 => (8167 / 10000000000 : ℝ)
  | 6 => (7961 / 10000000000 : ℝ)
  | 7 => (7759 / 10000000000 : ℝ)
  | 8 => (7563 / 10000000000 : ℝ)
  | 9 => (7371 / 10000000000 : ℝ)
  | 10 => (7183 / 10000000000 : ℝ)
  | 11 => (7001 / 10000000000 : ℝ)
  | 12 => (3411 / 5000000000 : ℝ)
  | 13 => (831 / 1250000000 : ℝ)
  | 14 => (3239 / 5000000000 : ℝ)
  | 15 => (6313 / 10000000000 : ℝ)
  | 16 => (6151 / 10000000000 : ℝ)
  | 17 => (5993 / 10000000000 : ℝ)
  | 18 => (5839 / 10000000000 : ℝ)
  | 19 => (5689 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch079_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch079Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch079Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1580_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1581_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1582_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1583_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1584_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1585_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1586_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1587_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1588_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1589_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1590_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1591_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1592_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1593_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1594_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1595_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1596_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1597_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1598_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1599_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper] at h ⊢
    exact h

end HodgeProofHP
