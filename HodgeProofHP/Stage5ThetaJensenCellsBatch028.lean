import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell560_leftExp :
    (10068763537 / 5000000000 : ℝ) ≤ Real.exp (7 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 10 : ℝ) (1022116011983 / 1000000000000 : ℝ)
    (10068763537 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell560_rightExp :
    Real.exp (561 / 800 : ℝ) ≤ (20162714723 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (561 / 800 : ℝ) (102215593917 / 100000000000 : ℝ)
    (20162714723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell560_denomUpper :
    Real.exp (61593043434773739 / 10000000000000000 : ℝ) ≤ (236549423023 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61593043434773739 / 10000000000000000 : ℝ)
    (1212250149993 / 1000000000000 : ℝ) (236549423023 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell560_denomLower :
    (469222418329 / 1000000000 : ℝ) ≤ Real.exp (3844423059716363 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3844423059716363 / 625000000000000 : ℝ) (24238770223 /
    20000000000 : ℝ) (469222418329 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell560_product_lower :
    (3953993372216363 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell560_leftExp
    (by norm_num : (0 : ℝ) ≤ (10068763537 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell560_product_upper :
    Real.pi * Real.exp (561 / 800 : ℝ) ≤ (63343043434773739 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell560_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell560_endpointLower :
    (5163169421 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 20 : ℝ) (561 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3953993372216363 / 625000000000000 : ℝ) (Real.pi * Real.exp (7 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell560_product_lower
  have hD : Real.exp (Real.pi * Real.exp (561 / 800 : ℝ) - (7 / 40 : ℝ)) ≤
      (236549423023 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell560_denomUpper
    linarith [hpThetaJensenCell560_product_upper]
  have hi : (1 / (236549423023 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (561 / 800 : ℝ) - (7 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (236549423023 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (236549423023 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 40 : ℝ) - Real.pi * Real.exp (561 / 800 : ℝ)) := by
    rw [show (7 / 40 : ℝ) - Real.pi * Real.exp (561 / 800 : ℝ) =
      -(Real.pi * Real.exp (561 / 800 : ℝ) - (7 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 10 : ℝ)) := by
    have h := hpThetaJensenCell560_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (236549423023 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell560_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 20 : ℝ) (561 / 1600 : ℝ) ≤ (5234634593 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (561 / 800 : ℝ)) (63343043434773739 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (561 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell560_product_upper
  have hD : (469222418329 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 10 : ℝ) - (561 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell560_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell560_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 10 : ℝ) - (561 / 3200 : ℝ)) ≤
      (1 / (469222418329 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (469222418329 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((561 / 3200 : ℝ) - Real.pi * Real.exp (7 / 10 : ℝ)) ≤
      (2 / (469222418329 / 1000000000 : ℝ) : ℝ) := by
    rw [show (561 / 3200 : ℝ) - Real.pi * Real.exp (7 / 10 : ℝ) =
      -(Real.pi * Real.exp (7 / 10 : ℝ) - (561 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (63343043434773739 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (63343043434773739 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell560_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 20 : ℝ) (561 / 1600 : ℝ)) :
    (5163169421 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5234634593 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell560_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell560_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell561_leftExp :
    (10081357361 / 5000000000 : ℝ) ≤ Real.exp (561 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (561 / 800 : ℝ) (1022155939169 / 1000000000000 : ℝ)
    (10081357361 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell561_rightExp :
    Real.exp (281 / 400 : ℝ) ≤ (5046983469 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (281 / 400 : ℝ) (1022195867917 / 1000000000000 : ℝ)
    (5046983469 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell561_denomUpper :
    Real.exp (15417286687326117 / 2500000000000000 : ℝ) ≤ (953426040321 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15417286687326117 / 2500000000000000 : ℝ) (1212538485073
    / 1000000000000 : ℝ) (953426040321 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell561_denomLower :
    (4728022981899 / 10000000000 : ℝ) ≤ Real.exp (3849173329307339 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3849173329307339 / 625000000000000 : ℝ) (121222639707 /
    100000000000 : ℝ) (4728022981899 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell561_product_lower :
    (3958938954307339 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (561 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell561_leftExp
    (by norm_num : (0 : ℝ) ≤ (10081357361 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell561_product_upper :
    Real.pi * Real.exp (281 / 400 : ℝ) ≤ (15855567937326117 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell561_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell561_endpointLower :
    (5138845583 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (561 / 1600 : ℝ) (281 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3958938954307339 / 625000000000000 : ℝ) (Real.pi * Real.exp (561 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell561_product_lower
  have hD : Real.exp (Real.pi * Real.exp (281 / 400 : ℝ) - (561 / 3200 : ℝ)) ≤
      (953426040321 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell561_denomUpper
    linarith [hpThetaJensenCell561_product_upper]
  have hi : (1 / (953426040321 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (281 / 400 : ℝ) - (561 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (953426040321 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (953426040321 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((561 / 3200 : ℝ) - Real.pi * Real.exp (281 / 400 : ℝ)) := by
    rw [show (561 / 3200 : ℝ) - Real.pi * Real.exp (281 / 400 : ℝ) =
      -(Real.pi * Real.exp (281 / 400 : ℝ) - (561 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (561 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (561 / 800 : ℝ)) := by
    have h := hpThetaJensenCell561_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (953426040321 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell561_endpointUpper :
    hpThetaJensenKernelEndpointUpper (561 / 1600 : ℝ) (281 / 800 : ℝ) ≤ (104200447 / 200000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (281 / 400 : ℝ)) (15855567937326117 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (281 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell561_product_upper
  have hD : (4728022981899 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (561 / 800 : ℝ) - (281 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell561_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell561_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (561 / 800 : ℝ) - (281 / 1600 : ℝ)) ≤
      (1 / (4728022981899 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4728022981899 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((281 / 1600 : ℝ) - Real.pi * Real.exp (561 / 800 : ℝ)) ≤
      (2 / (4728022981899 / 10000000000 : ℝ) : ℝ) := by
    rw [show (281 / 1600 : ℝ) - Real.pi * Real.exp (561 / 800 : ℝ) =
      -(Real.pi * Real.exp (561 / 800 : ℝ) - (281 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15855567937326117 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (15855567937326117 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell561_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (561 / 1600 : ℝ) (281 / 800 : ℝ)) :
    (5138845583 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (104200447 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell561_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell561_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell562_leftExp :
    (10093966937 / 5000000000 : ℝ) ≤ Real.exp (281 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (281 / 400 : ℝ) (255548966979 / 250000000000 : ℝ)
    (10093966937 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell562_rightExp :
    Real.exp (563 / 800 : ℝ) ≤ (20213184571 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (563 / 800 : ℝ) (1022235798223 / 1000000000000 : ℝ)
    (20213184571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell562_denomUpper :
    Real.exp (61745349155961603 / 10000000000000000 : ℝ) ≤ (4803595642221 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61745349155961603 / 10000000000000000 : ℝ)
    (1212827264301 / 1000000000000 : ℝ) (4803595642221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell562_denomLower :
    (238207102759 / 500000000 : ℝ) ≤ Real.exp (3853929784692963 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3853929784692963 / 625000000000000 : ℝ) (1212514726393 /
    1000000000000 : ℝ) (238207102759 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell562_product_lower :
    (3963890722192963 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (281 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell562_leftExp
    (by norm_num : (0 : ℝ) ≤ (10093966937 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell562_product_upper :
    Real.pi * Real.exp (563 / 800 : ℝ) ≤ (63501599155961603 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell562_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell562_endpointLower :
    (1278645601 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (281 / 800 : ℝ) (563 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3963890722192963 / 625000000000000 : ℝ) (Real.pi * Real.exp (281 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell562_product_lower
  have hD : Real.exp (Real.pi * Real.exp (563 / 800 : ℝ) - (281 / 1600 : ℝ)) ≤
      (4803595642221 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell562_denomUpper
    linarith [hpThetaJensenCell562_product_upper]
  have hi : (1 / (4803595642221 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (563 / 800 : ℝ) - (281 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4803595642221 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4803595642221 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((281 / 1600 : ℝ) - Real.pi * Real.exp (563 / 800 : ℝ)) := by
    rw [show (281 / 1600 : ℝ) - Real.pi * Real.exp (563 / 800 : ℝ) =
      -(Real.pi * Real.exp (563 / 800 : ℝ) - (281 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (281 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (281 / 400 : ℝ)) := by
    have h := hpThetaJensenCell562_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4803595642221 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell562_endpointUpper :
    hpThetaJensenKernelEndpointUpper (281 / 800 : ℝ) (563 / 1600 : ℝ) ≤ (2592735609 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (563 / 800 : ℝ)) (63501599155961603 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (563 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell562_product_upper
  have hD : (238207102759 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (281 / 400 : ℝ) - (563 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell562_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell562_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (281 / 400 : ℝ) - (563 / 3200 : ℝ)) ≤
      (1 / (238207102759 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (238207102759 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((563 / 3200 : ℝ) - Real.pi * Real.exp (281 / 400 : ℝ)) ≤
      (2 / (238207102759 / 500000000 : ℝ) : ℝ) := by
    rw [show (563 / 3200 : ℝ) - Real.pi * Real.exp (281 / 400 : ℝ) =
      -(Real.pi * Real.exp (281 / 400 : ℝ) - (563 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (63501599155961603 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (63501599155961603 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell562_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (281 / 800 : ℝ) (563 / 1600 : ℝ)) :
    (1278645601 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2592735609 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell562_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell562_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell563_leftExp :
    (2021318457 / 1000000000 : ℝ) ≤ Real.exp (563 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (563 / 800 : ℝ) (511117899111 / 500000000000 : ℝ)
    (2021318457 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell563_rightExp :
    Real.exp (141 / 200 : ℝ) ≤ (404769337 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (141 / 200 : ℝ) (127784466261 / 125000000000 : ℝ)
    (404769337 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell563_denomUpper :
    Real.exp (1236433015733841 / 200000000000000 : ℝ) ≤ (968077609573 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1236433015733841 / 200000000000000 : ℝ) (1213116488463 /
    1000000000000 : ℝ) (968077609573 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell563_denomLower :
    (4800584627831 / 10000000000 : ℝ) ≤ Real.exp (771738486745443 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (771738486745443 / 125000000000000 : ℝ) (1212803499879 /
    1000000000000 : ℝ) (4800584627831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell563_product_lower :
    (793769736745443 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (563 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell563_leftExp
    (by norm_num : (0 : ℝ) ≤ (2021318457 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell563_product_upper :
    Real.pi * Real.exp (141 / 200 : ℝ) ≤ (1271620515733841 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell563_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell563_endpointLower :
    (5090380049 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (563 / 1600 : ℝ) (141 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (793769736745443 / 125000000000000 : ℝ) (Real.pi * Real.exp (563 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell563_product_lower
  have hD : Real.exp (Real.pi * Real.exp (141 / 200 : ℝ) - (563 / 3200 : ℝ)) ≤
      (968077609573 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell563_denomUpper
    linarith [hpThetaJensenCell563_product_upper]
  have hi : (1 / (968077609573 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (141 / 200 : ℝ) - (563 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (968077609573 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (968077609573 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((563 / 3200 : ℝ) - Real.pi * Real.exp (141 / 200 : ℝ)) := by
    rw [show (563 / 3200 : ℝ) - Real.pi * Real.exp (141 / 200 : ℝ) =
      -(Real.pi * Real.exp (141 / 200 : ℝ) - (563 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (563 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (563 / 800 : ℝ)) := by
    have h := hpThetaJensenCell563_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (968077609573 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell563_endpointUpper :
    hpThetaJensenKernelEndpointUpper (563 / 1600 : ℝ) (141 / 400 : ℝ) ≤ (5160981369 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (141 / 200 : ℝ)) (1271620515733841 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (141 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell563_product_upper
  have hD : (4800584627831 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (563 / 800 : ℝ) - (141 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell563_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell563_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (563 / 800 : ℝ) - (141 / 800 : ℝ)) ≤
      (1 / (4800584627831 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4800584627831 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((141 / 800 : ℝ) - Real.pi * Real.exp (563 / 800 : ℝ)) ≤
      (2 / (4800584627831 / 10000000000 : ℝ) : ℝ) := by
    rw [show (141 / 800 : ℝ) - Real.pi * Real.exp (563 / 800 : ℝ) =
      -(Real.pi * Real.exp (563 / 800 : ℝ) - (141 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1271620515733841 / 200000000000000 : ℝ) ^ 2 - 6 *
      (1271620515733841 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell563_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (563 / 1600 : ℝ) (141 / 400 : ℝ)) :
    (5090380049 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5160981369 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell563_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell563_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell564_leftExp :
    (632452089 / 312500000 : ℝ) ≤ Real.exp (141 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (141 / 200 : ℝ) (1022275730087 / 1000000000000 : ℝ)
    (632452089 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell564_rightExp :
    Real.exp (113 / 160 : ℝ) ≤ (20263780751 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (113 / 160 : ℝ) (511157831757 / 500000000000 : ℝ)
    (20263780751 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell564_denomUpper :
    Real.exp (61898051760876343 / 10000000000000000 : ℝ) ≤ (2438755356947 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61898051760876343 / 10000000000000000 : ℝ) (151675769787
    / 125000000000 : ℝ) (2438755356947 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell564_denomLower :
    (2418676978653 / 5000000000 : ℝ) ≤ Real.exp (241466330241961 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (241466330241961 / 39062500000000 : ℝ) (606546359133 /
    500000000000 : ℝ) (2418676978653 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell564_product_lower :
    (248363302898211 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (141 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell564_leftExp
    (by norm_num : (0 : ℝ) ≤ (632452089 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell564_product_upper :
    Real.pi * Real.exp (113 / 160 : ℝ) ≤ (63660551760876343 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell564_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell564_endpointLower :
    (1266559671 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (141 / 400 : ℝ) (113 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (248363302898211 / 39062500000000 : ℝ) (Real.pi * Real.exp (141 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell564_product_lower
  have hD : Real.exp (Real.pi * Real.exp (113 / 160 : ℝ) - (141 / 800 : ℝ)) ≤
      (2438755356947 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell564_denomUpper
    linarith [hpThetaJensenCell564_product_upper]
  have hi : (1 / (2438755356947 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (113 / 160 : ℝ) - (141 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2438755356947 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2438755356947 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((141 / 800 : ℝ) - Real.pi * Real.exp (113 / 160 : ℝ)) := by
    rw [show (141 / 800 : ℝ) - Real.pi * Real.exp (113 / 160 : ℝ) =
      -(Real.pi * Real.exp (113 / 160 : ℝ) - (141 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (141 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (141 / 200 : ℝ)) := by
    have h := hpThetaJensenCell564_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2438755356947 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell564_endpointUpper :
    hpThetaJensenKernelEndpointUpper (141 / 400 : ℝ) (113 / 320 : ℝ) ≤ (1284138243 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (113 / 160 : ℝ)) (63660551760876343 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (113 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell564_product_upper
  have hD : (2418676978653 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (141 / 200 : ℝ) - (113 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell564_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell564_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (141 / 200 : ℝ) - (113 / 640 : ℝ)) ≤
      (1 / (2418676978653 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2418676978653 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((113 / 640 : ℝ) - Real.pi * Real.exp (141 / 200 : ℝ)) ≤
      (2 / (2418676978653 / 5000000000 : ℝ) : ℝ) := by
    rw [show (113 / 640 : ℝ) - Real.pi * Real.exp (141 / 200 : ℝ) =
      -(Real.pi * Real.exp (141 / 200 : ℝ) - (113 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (63660551760876343 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (63660551760876343 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell564_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (141 / 400 : ℝ) (113 / 320 : ℝ)) :
    (1266559671 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1284138243 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell564_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell564_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell565_leftExp :
    (81055123 / 40000000 : ℝ) ≤ Real.exp (113 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (113 / 160 : ℝ) (1022315663513 / 1000000000000 : ℝ)
    (81055123 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell565_rightExp :
    Real.exp (283 / 400 : ℝ) ≤ (4057825263 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (283 / 400 : ℝ) (2044711197 / 2000000000 : ℝ)
    (4057825263 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell565_denomUpper :
    Real.exp (12394910441463959 / 2000000000000000 : ℝ) ≤ (2457483488531 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12394910441463959 / 2000000000000000 : ℝ) (75856017161 /
    62500000000 : ℝ) (2457483488531 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell565_denomLower :
    (4874453342997 / 10000000000 : ℝ) ≤ Real.exp (30945890746977 / 5000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (30945890746977 / 5000000000000 : ℝ) (1213382382339 /
    1000000000000 : ℝ) (4874453342997 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell565_product_lower :
    (31830265746977 / 5000000000000 : ℝ) ≤ Real.pi * Real.exp (113 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell565_leftExp
    (by norm_num : (0 : ℝ) ≤ (81055123 / 40000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell565_product_upper :
    Real.pi * Real.exp (283 / 400 : ℝ) ≤ (12748035441463959 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell565_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell565_endpointLower :
    (5042158471 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (113 / 320 : ℝ) (283 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (31830265746977 / 5000000000000 : ℝ) (Real.pi * Real.exp (113 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell565_product_lower
  have hD : Real.exp (Real.pi * Real.exp (283 / 400 : ℝ) - (113 / 640 : ℝ)) ≤
      (2457483488531 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell565_denomUpper
    linarith [hpThetaJensenCell565_product_upper]
  have hi : (1 / (2457483488531 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (283 / 400 : ℝ) - (113 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2457483488531 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2457483488531 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((113 / 640 : ℝ) - Real.pi * Real.exp (283 / 400 : ℝ)) := by
    rw [show (113 / 640 : ℝ) - Real.pi * Real.exp (283 / 400 : ℝ) =
      -(Real.pi * Real.exp (283 / 400 : ℝ) - (113 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (113 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (113 / 160 : ℝ)) := by
    have h := hpThetaJensenCell565_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2457483488531 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell565_endpointUpper :
    hpThetaJensenKernelEndpointUpper (113 / 320 : ℝ) (283 / 800 : ℝ) ≤ (319511637 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (283 / 400 : ℝ)) (12748035441463959 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (283 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell565_product_upper
  have hD : (4874453342997 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (113 / 160 : ℝ) - (283 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell565_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell565_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (113 / 160 : ℝ) - (283 / 1600 : ℝ)) ≤
      (1 / (4874453342997 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4874453342997 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((283 / 1600 : ℝ) - Real.pi * Real.exp (113 / 160 : ℝ)) ≤
      (2 / (4874453342997 / 10000000000 : ℝ) : ℝ) := by
    rw [show (283 / 1600 : ℝ) - Real.pi * Real.exp (113 / 160 : ℝ) =
      -(Real.pi * Real.exp (113 / 160 : ℝ) - (283 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12748035441463959 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (12748035441463959 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell565_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (113 / 320 : ℝ) (283 / 800 : ℝ)) :
    (5042158471 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (319511637 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell565_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell565_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell566_leftExp :
    (10144563157 / 5000000000 : ℝ) ≤ Real.exp (283 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (283 / 400 : ℝ) (1022355598499 / 1000000000000 : ℝ)
    (10144563157 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell566_rightExp :
    Real.exp (567 / 800 : ℝ) ≤ (1015725179 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (567 / 800 : ℝ) (204479107009 / 200000000000 : ℝ)
    (1015725179 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell566_denomUpper :
    Real.exp (3102557612270147 / 500000000000000 : ℝ) ≤ (619095025761 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3102557612270147 / 500000000000000 : ℝ) (1213986838041 /
    1000000000000 : ℝ) (619095025761 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell566_denomLower :
    (4911886114971 / 10000000000 : ℝ) ≤ Real.exp (3873017619690743 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3873017619690743 / 625000000000000 : ℝ) (606836246419 /
    500000000000 : ℝ) (4911886114971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell566_product_lower :
    (3983759807190743 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (283 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell566_leftExp
    (by norm_num : (0 : ℝ) ≤ (10144563157 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell566_product_upper :
    Real.pi * Real.exp (567 / 800 : ℝ) ≤ (3190995112270147 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell566_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell566_endpointLower :
    (200725583 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (283 / 800 : ℝ) (567 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3983759807190743 / 625000000000000 : ℝ) (Real.pi * Real.exp (283 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell566_product_lower
  have hD : Real.exp (Real.pi * Real.exp (567 / 800 : ℝ) - (283 / 1600 : ℝ)) ≤
      (619095025761 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell566_denomUpper
    linarith [hpThetaJensenCell566_product_upper]
  have hi : (1 / (619095025761 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (567 / 800 : ℝ) - (283 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (619095025761 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (619095025761 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((283 / 1600 : ℝ) - Real.pi * Real.exp (567 / 800 : ℝ)) := by
    rw [show (283 / 1600 : ℝ) - Real.pi * Real.exp (567 / 800 : ℝ) =
      -(Real.pi * Real.exp (567 / 800 : ℝ) - (283 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (283 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (283 / 400 : ℝ)) := by
    have h := hpThetaJensenCell566_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (619095025761 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell566_endpointUpper :
    hpThetaJensenKernelEndpointUpper (283 / 800 : ℝ) (567 / 1600 : ℝ) ≤ (2543940597 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (567 / 800 : ℝ)) (3190995112270147 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (567 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell566_product_upper
  have hD : (4911886114971 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (283 / 400 : ℝ) - (567 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell566_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell566_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (283 / 400 : ℝ) - (567 / 3200 : ℝ)) ≤
      (1 / (4911886114971 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4911886114971 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((567 / 3200 : ℝ) - Real.pi * Real.exp (283 / 400 : ℝ)) ≤
      (2 / (4911886114971 / 10000000000 : ℝ) : ℝ) := by
    rw [show (567 / 3200 : ℝ) - Real.pi * Real.exp (283 / 400 : ℝ) =
      -(Real.pi * Real.exp (283 / 400 : ℝ) - (567 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3190995112270147 / 500000000000000 : ℝ) ^ 2 - 6 *
      (3190995112270147 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell566_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (283 / 800 : ℝ) (567 / 1600 : ℝ)) :
    (200725583 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2543940597 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell566_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell566_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell567_leftExp :
    (20314503579 / 10000000000 : ℝ) ≤ Real.exp (567 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (567 / 800 : ℝ) (255598883761 / 250000000000 : ℝ)
    (20314503579 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell567_rightExp :
    Real.exp (71 / 100 : ℝ) ≤ (20339912587 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 100 : ℝ) (1022435473151 / 1000000000000 : ℝ)
    (20339912587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell567_denomUpper :
    Real.exp (62127852003931091 / 10000000000000000 : ℝ) ≤ (998178762461 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (62127852003931091 / 10000000000000000 : ℝ) (121427784947
    / 100000000000 : ℝ) (998178762461 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell567_denomLower :
    (618706955187 / 1250000000 : ℝ) ≤ Real.exp (7755610240969721 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7755610240969721 / 1250000000000000 : ℝ) (606981525257 /
    500000000000 : ℝ) (618706955187 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell567_product_lower :
    (7977485240969721 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (567 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell567_leftExp
    (by norm_num : (0 : ℝ) ≤ (20314503579 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell567_product_upper :
    Real.pi * Real.exp (71 / 100 : ℝ) ≤ (63899727003931091 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell567_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell567_endpointLower :
    (624272769 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (567 / 1600 : ℝ) (71 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7977485240969721 / 1250000000000000 : ℝ) (Real.pi * Real.exp (567 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell567_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 100 : ℝ) - (567 / 3200 : ℝ)) ≤
      (998178762461 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell567_denomUpper
    linarith [hpThetaJensenCell567_product_upper]
  have hi : (1 / (998178762461 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 100 : ℝ) - (567 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (998178762461 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (998178762461 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((567 / 3200 : ℝ) - Real.pi * Real.exp (71 / 100 : ℝ)) := by
    rw [show (567 / 3200 : ℝ) - Real.pi * Real.exp (71 / 100 : ℝ) =
      -(Real.pi * Real.exp (71 / 100 : ℝ) - (567 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (567 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (567 / 800 : ℝ)) := by
    have h := hpThetaJensenCell567_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (998178762461 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell567_endpointUpper :
    hpThetaJensenKernelEndpointUpper (567 / 1600 : ℝ) (71 / 200 : ℝ) ≤ (2531819071 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 100 : ℝ)) (63899727003931091 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell567_product_upper
  have hD : (618706955187 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (567 / 800 : ℝ) - (71 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell567_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell567_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (567 / 800 : ℝ) - (71 / 400 : ℝ)) ≤
      (1 / (618706955187 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (618706955187 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 400 : ℝ) - Real.pi * Real.exp (567 / 800 : ℝ)) ≤
      (2 / (618706955187 / 1250000000 : ℝ) : ℝ) := by
    rw [show (71 / 400 : ℝ) - Real.pi * Real.exp (567 / 800 : ℝ) =
      -(Real.pi * Real.exp (567 / 800 : ℝ) - (71 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (63899727003931091 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (63899727003931091 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell567_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (567 / 1600 : ℝ) (71 / 200 : ℝ)) :
    (624272769 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2531819071 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell567_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell567_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell568_leftExp :
    (10169956293 / 5000000000 : ℝ) ≤ Real.exp (71 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 100 : ℝ) (20448709463 / 20000000000 : ℝ)
    (10169956293 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell568_rightExp :
    Real.exp (569 / 800 : ℝ) ≤ (636417293 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (569 / 800 : ℝ) (1022475412817 / 1000000000000 : ℝ)
    (636417293 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell568_denomUpper :
    Real.exp (1943895362767749 / 312500000000000 : ℝ) ≤ (2514685621439 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1943895362767749 / 312500000000000 : ℝ) (1214569309627 /
    1000000000000 : ℝ) (2514685621439 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell568_denomLower :
    (39902122651 / 80000000 : ℝ) ≤ Real.exp (3882598853804807 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3882598853804807 / 625000000000000 : ℝ) (1214254056143 /
    1000000000000 : ℝ) (39902122651 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell568_product_lower :
    (3993731666304807 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell568_leftExp
    (by norm_num : (0 : ℝ) ≤ (10169956293 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell568_product_upper :
    Real.pi * Real.exp (569 / 800 : ℝ) ≤ (1999364112767749 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell568_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell568_endpointLower :
    (124257159 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 200 : ℝ) (569 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3993731666304807 / 625000000000000 : ℝ) (Real.pi * Real.exp (71 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell568_product_lower
  have hD : Real.exp (Real.pi * Real.exp (569 / 800 : ℝ) - (71 / 400 : ℝ)) ≤
      (2514685621439 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell568_denomUpper
    linarith [hpThetaJensenCell568_product_upper]
  have hi : (1 / (2514685621439 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (569 / 800 : ℝ) - (71 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2514685621439 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2514685621439 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 400 : ℝ) - Real.pi * Real.exp (569 / 800 : ℝ)) := by
    rw [show (71 / 400 : ℝ) - Real.pi * Real.exp (569 / 800 : ℝ) =
      -(Real.pi * Real.exp (569 / 800 : ℝ) - (71 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 100 : ℝ)) := by
    have h := hpThetaJensenCell568_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2514685621439 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell568_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 200 : ℝ) (569 / 1600 : ℝ) ≤ (1007891439 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (569 / 800 : ℝ)) (1999364112767749 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (569 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell568_product_upper
  have hD : (39902122651 / 80000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 100 : ℝ) - (569 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell568_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell568_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 100 : ℝ) - (569 / 3200 : ℝ)) ≤
      (1 / (39902122651 / 80000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (39902122651 / 80000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((569 / 3200 : ℝ) - Real.pi * Real.exp (71 / 100 : ℝ)) ≤
      (2 / (39902122651 / 80000000 : ℝ) : ℝ) := by
    rw [show (569 / 3200 : ℝ) - Real.pi * Real.exp (71 / 100 : ℝ) =
      -(Real.pi * Real.exp (71 / 100 : ℝ) - (569 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1999364112767749 / 312500000000000 : ℝ) ^ 2 - 6 *
      (1999364112767749 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell568_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 200 : ℝ) (569 / 1600 : ℝ)) :
    (124257159 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1007891439 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell568_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell568_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell569_leftExp :
    (10182676687 / 5000000000 : ℝ) ≤ Real.exp (569 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (569 / 800 : ℝ) (63904713301 / 62500000000 : ℝ)
    (10182676687 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell569_rightExp :
    Real.exp (57 / 80 : ℝ) ≤ (19912916 / 9765625 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 80 : ℝ) (511257677021 / 500000000000 : ℝ)
    (19912916 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell569_denomUpper :
    Real.exp (121643654639751 / 19531250000000 : ℝ) ≤ (2534097989459 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (121643654639751 / 19531250000000 : ℝ) (303715304811 /
    250000000000 : ℝ) (2534097989459 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell569_denomLower :
    (1005243725709 / 2000000000 : ℝ) ≤ Real.exp (3887398827308213 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3887398827308213 / 625000000000000 : ℝ) (1214545510481 /
    1000000000000 : ℝ) (1005243725709 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell569_product_lower :
    (3998726952308213 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (569 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell569_leftExp
    (by norm_num : (0 : ℝ) ≤ (10182676687 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell569_product_upper :
    Real.pi * Real.exp (57 / 80 : ℝ) ≤ (15639569378797 / 2441406250000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell569_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell569_endpointLower :
    (4946452359 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (569 / 1600 : ℝ) (57 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3998726952308213 / 625000000000000 : ℝ) (Real.pi * Real.exp (569 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell569_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 80 : ℝ) - (569 / 3200 : ℝ)) ≤
      (2534097989459 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell569_denomUpper
    linarith [hpThetaJensenCell569_product_upper]
  have hi : (1 / (2534097989459 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 80 : ℝ) - (569 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2534097989459 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2534097989459 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((569 / 3200 : ℝ) - Real.pi * Real.exp (57 / 80 : ℝ)) := by
    rw [show (569 / 3200 : ℝ) - Real.pi * Real.exp (57 / 80 : ℝ) =
      -(Real.pi * Real.exp (57 / 80 : ℝ) - (569 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (569 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (569 / 800 : ℝ)) := by
    have h := hpThetaJensenCell569_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2534097989459 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell569_endpointUpper :
    hpThetaJensenKernelEndpointUpper (569 / 1600 : ℝ) (57 / 160 : ℝ) ≤ (5015338511 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 80 : ℝ)) (15639569378797 / 2441406250000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell569_product_upper
  have hD : (1005243725709 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (569 / 800 : ℝ) - (57 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell569_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell569_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (569 / 800 : ℝ) - (57 / 320 : ℝ)) ≤
      (1 / (1005243725709 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1005243725709 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 320 : ℝ) - Real.pi * Real.exp (569 / 800 : ℝ)) ≤
      (2 / (1005243725709 / 2000000000 : ℝ) : ℝ) := by
    rw [show (57 / 320 : ℝ) - Real.pi * Real.exp (569 / 800 : ℝ) =
      -(Real.pi * Real.exp (569 / 800 : ℝ) - (57 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15639569378797 / 2441406250000 : ℝ) ^ 2 - 6 *
      (15639569378797 / 2441406250000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell569_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (569 / 1600 : ℝ) (57 / 160 : ℝ)) :
    (4946452359 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5015338511 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell569_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell569_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell570_leftExp :
    (10195412991 / 5000000000 : ℝ) ≤ Real.exp (57 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 80 : ℝ) (1022515354041 / 1000000000000 : ℝ)
    (10195412991 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell570_rightExp :
    Real.exp (571 / 800 : ℝ) ≤ (10208165227 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (571 / 800 : ℝ) (1022555296829 / 1000000000000 : ℝ)
    (10208165227 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell570_denomUpper :
    Real.exp (31179275419986611 / 5000000000000000 : ℝ) ≤ (1276842887407 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31179275419986611 / 5000000000000000 : ℝ) (303788394781
    / 250000000000 : ℝ) (1276842887407 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell570_denomLower :
    (2532509507353 / 5000000000 : ℝ) ≤ Real.exp (3892205048652709 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3892205048652709 / 625000000000000 : ℝ) (1214837414281 /
    1000000000000 : ℝ) (2532509507353 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell570_product_lower :
    (4003728486152709 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell570_leftExp
    (by norm_num : (0 : ℝ) ≤ (10195412991 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell570_product_upper :
    Real.pi * Real.exp (571 / 800 : ℝ) ≤ (32069900419986611 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell570_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell570_endpointLower :
    (615335037 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 160 : ℝ) (571 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4003728486152709 / 625000000000000 : ℝ) (Real.pi * Real.exp (57 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell570_product_lower
  have hD : Real.exp (Real.pi * Real.exp (571 / 800 : ℝ) - (57 / 320 : ℝ)) ≤
      (1276842887407 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell570_denomUpper
    linarith [hpThetaJensenCell570_product_upper]
  have hi : (1 / (1276842887407 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (571 / 800 : ℝ) - (57 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1276842887407 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1276842887407 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 320 : ℝ) - Real.pi * Real.exp (571 / 800 : ℝ)) := by
    rw [show (57 / 320 : ℝ) - Real.pi * Real.exp (571 / 800 : ℝ) =
      -(Real.pi * Real.exp (571 / 800 : ℝ) - (57 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 80 : ℝ)) := by
    have h := hpThetaJensenCell570_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1276842887407 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell570_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 160 : ℝ) (571 / 1600 : ℝ) ≤ (19965129 / 40000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (571 / 800 : ℝ)) (32069900419986611 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (571 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell570_product_upper
  have hD : (2532509507353 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 80 : ℝ) - (571 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell570_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell570_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 80 : ℝ) - (571 / 3200 : ℝ)) ≤
      (1 / (2532509507353 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2532509507353 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((571 / 3200 : ℝ) - Real.pi * Real.exp (57 / 80 : ℝ)) ≤
      (2 / (2532509507353 / 5000000000 : ℝ) : ℝ) := by
    rw [show (571 / 3200 : ℝ) - Real.pi * Real.exp (57 / 80 : ℝ) =
      -(Real.pi * Real.exp (57 / 80 : ℝ) - (571 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32069900419986611 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (32069900419986611 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell570_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 160 : ℝ) (571 / 1600 : ℝ)) :
    (615335037 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (19965129 / 40000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell570_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell570_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell571_leftExp :
    (5104082613 / 2500000000 : ℝ) ≤ Real.exp (571 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (571 / 800 : ℝ) (255638824207 / 250000000000 : ℝ)
    (5104082613 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell571_rightExp :
    Real.exp (143 / 200 : ℝ) ≤ (20441866823 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (143 / 200 : ℝ) (40903809647 / 40000000000 : ℝ)
    (20441866823 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell571_denomUpper :
    Real.exp (62435650718069039 / 10000000000000000 : ℝ) ≤ (5146901513881 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (62435650718069039 / 10000000000000000 : ℝ)
    (1215446389999 / 1000000000000 : ℝ) (5146901513881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell571_denomLower :
    (319010625971 / 625000000 : ℝ) ≤ Real.exp (1948508763042487 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1948508763042487 / 312500000000000 : ℝ) (75945610521 /
    62500000000 : ℝ) (319010625971 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell571_product_lower :
    (2004368138042487 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (571 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell571_leftExp
    (by norm_num : (0 : ℝ) ≤ (5104082613 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell571_product_upper :
    Real.pi * Real.exp (143 / 200 : ℝ) ≤ (64220025718069039 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell571_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell571_endpointLower :
    (4898970329 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (571 / 1600 : ℝ) (143 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2004368138042487 / 312500000000000 : ℝ) (Real.pi * Real.exp (571 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell571_product_lower
  have hD : Real.exp (Real.pi * Real.exp (143 / 200 : ℝ) - (571 / 3200 : ℝ)) ≤
      (5146901513881 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell571_denomUpper
    linarith [hpThetaJensenCell571_product_upper]
  have hi : (1 / (5146901513881 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (143 / 200 : ℝ) - (571 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5146901513881 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5146901513881 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((571 / 3200 : ℝ) - Real.pi * Real.exp (143 / 200 : ℝ)) := by
    rw [show (571 / 3200 : ℝ) - Real.pi * Real.exp (143 / 200 : ℝ) =
      -(Real.pi * Real.exp (143 / 200 : ℝ) - (571 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (571 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (571 / 800 : ℝ)) := by
    have h := hpThetaJensenCell571_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5146901513881 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell571_endpointUpper :
    hpThetaJensenKernelEndpointUpper (571 / 1600 : ℝ) (143 / 400 : ℝ) ≤ (4967288561 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (143 / 200 : ℝ)) (64220025718069039 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (143 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell571_product_upper
  have hD : (319010625971 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (571 / 800 : ℝ) - (143 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell571_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell571_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (571 / 800 : ℝ) - (143 / 800 : ℝ)) ≤
      (1 / (319010625971 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (319010625971 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((143 / 800 : ℝ) - Real.pi * Real.exp (571 / 800 : ℝ)) ≤
      (2 / (319010625971 / 625000000 : ℝ) : ℝ) := by
    rw [show (143 / 800 : ℝ) - Real.pi * Real.exp (571 / 800 : ℝ) =
      -(Real.pi * Real.exp (571 / 800 : ℝ) - (143 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64220025718069039 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (64220025718069039 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell571_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (571 / 1600 : ℝ) (143 / 400 : ℝ)) :
    (4898970329 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4967288561 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell571_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell571_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell572_leftExp :
    (10220933411 / 5000000000 : ℝ) ≤ Real.exp (143 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (143 / 200 : ℝ) (511297620587 / 500000000000 : ℝ)
    (10220933411 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell572_rightExp :
    Real.exp (573 / 800 : ℝ) ≤ (10233717567 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (573 / 800 : ℝ) (511317593541 / 500000000000 : ℝ)
    (10233717567 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell572_denomUpper :
    Real.exp (31256425472464231 / 5000000000000000 : ℝ) ≤ (5186789480261 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31256425472464231 / 5000000000000000 : ℝ) (303934913169
    / 250000000000 : ℝ) (5186789480261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell572_denomLower :
    (5143675189169 / 10000000000 : ℝ) ≤ Real.exp (3901836267066289 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3901836267066289 / 625000000000000 : ℝ) (1215422573389 /
    1000000000000 : ℝ) (5143675189169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell572_product_lower :
    (4013750329566289 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (143 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell572_leftExp
    (by norm_num : (0 : ℝ) ≤ (10220933411 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell572_product_upper :
    Real.pi * Real.exp (573 / 800 : ℝ) ≤ (32150175472464231 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell572_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell572_endpointLower :
    (2437661301 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (143 / 400 : ℝ) (573 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4013750329566289 / 625000000000000 : ℝ) (Real.pi * Real.exp (143 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell572_product_lower
  have hD : Real.exp (Real.pi * Real.exp (573 / 800 : ℝ) - (143 / 800 : ℝ)) ≤
      (5186789480261 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell572_denomUpper
    linarith [hpThetaJensenCell572_product_upper]
  have hi : (1 / (5186789480261 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (573 / 800 : ℝ) - (143 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5186789480261 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5186789480261 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((143 / 800 : ℝ) - Real.pi * Real.exp (573 / 800 : ℝ)) := by
    rw [show (143 / 800 : ℝ) - Real.pi * Real.exp (573 / 800 : ℝ) =
      -(Real.pi * Real.exp (573 / 800 : ℝ) - (143 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (143 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (143 / 200 : ℝ)) := by
    have h := hpThetaJensenCell572_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5186789480261 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell572_endpointUpper :
    hpThetaJensenKernelEndpointUpper (143 / 400 : ℝ) (573 / 1600 : ℝ) ≤ (4943357601 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (573 / 800 : ℝ)) (32150175472464231 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (573 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell572_product_upper
  have hD : (5143675189169 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (143 / 200 : ℝ) - (573 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell572_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell572_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (143 / 200 : ℝ) - (573 / 3200 : ℝ)) ≤
      (1 / (5143675189169 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5143675189169 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((573 / 3200 : ℝ) - Real.pi * Real.exp (143 / 200 : ℝ)) ≤
      (2 / (5143675189169 / 10000000000 : ℝ) : ℝ) := by
    rw [show (573 / 3200 : ℝ) - Real.pi * Real.exp (143 / 200 : ℝ) =
      -(Real.pi * Real.exp (143 / 200 : ℝ) - (573 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32150175472464231 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (32150175472464231 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell572_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (143 / 400 : ℝ) (573 / 1600 : ℝ)) :
    (2437661301 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4943357601 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell572_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell572_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell573_leftExp :
    (5116858783 / 2500000000 : ℝ) ≤ Real.exp (573 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (573 / 800 : ℝ) (1022635187081 / 1000000000000 : ℝ)
    (5116858783 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell573_rightExp :
    Real.exp (287 / 400 : ℝ) ≤ (819721417 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (287 / 400 : ℝ) (1022675134549 / 1000000000000 : ℝ)
    (819721417 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell573_denomUpper :
    Real.exp (2503606065597281 / 400000000000000 : ℝ) ≤ (5227039089213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2503606065597281 / 400000000000000 : ℝ) (1216033367901 /
    1000000000000 : ℝ) (5227039089213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell573_denomLower :
    (5183538136913 / 10000000000 : ℝ) ≤ Real.exp (1953330639725317 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1953330639725317 / 312500000000000 : ℝ) (121571583021 /
    100000000000 : ℝ) (5183538136913 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell573_product_lower :
    (2009385327225317 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (573 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell573_leftExp
    (by norm_num : (0 : ℝ) ≤ (5116858783 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell573_product_upper :
    Real.pi * Real.exp (287 / 400 : ℝ) ≤ (2575231065597281 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell573_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell573_endpointLower :
    (303233579 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (573 / 1600 : ℝ) (287 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2009385327225317 / 312500000000000 : ℝ) (Real.pi * Real.exp (573 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell573_product_lower
  have hD : Real.exp (Real.pi * Real.exp (287 / 400 : ℝ) - (573 / 3200 : ℝ)) ≤
      (5227039089213 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell573_denomUpper
    linarith [hpThetaJensenCell573_product_upper]
  have hi : (1 / (5227039089213 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (287 / 400 : ℝ) - (573 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5227039089213 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5227039089213 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((573 / 3200 : ℝ) - Real.pi * Real.exp (287 / 400 : ℝ)) := by
    rw [show (573 / 3200 : ℝ) - Real.pi * Real.exp (287 / 400 : ℝ) =
      -(Real.pi * Real.exp (287 / 400 : ℝ) - (573 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (573 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (573 / 800 : ℝ)) := by
    have h := hpThetaJensenCell573_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5227039089213 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell573_endpointUpper :
    hpThetaJensenKernelEndpointUpper (573 / 1600 : ℝ) (287 / 800 : ℝ) ≤ (4919489519 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (287 / 400 : ℝ)) (2575231065597281 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (287 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell573_product_upper
  have hD : (5183538136913 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (573 / 800 : ℝ) - (287 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell573_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell573_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (573 / 800 : ℝ) - (287 / 1600 : ℝ)) ≤
      (1 / (5183538136913 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5183538136913 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((287 / 1600 : ℝ) - Real.pi * Real.exp (573 / 800 : ℝ)) ≤
      (2 / (5183538136913 / 10000000000 : ℝ) : ℝ) := by
    rw [show (287 / 1600 : ℝ) - Real.pi * Real.exp (573 / 800 : ℝ) =
      -(Real.pi * Real.exp (573 / 800 : ℝ) - (287 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2575231065597281 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2575231065597281 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell573_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (573 / 1600 : ℝ) (287 / 800 : ℝ)) :
    (303233579 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4919489519 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell573_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell573_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell574_leftExp :
    (20493035423 / 10000000000 : ℝ) ≤ Real.exp (287 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (287 / 400 : ℝ) (255668783637 / 250000000000 : ℝ)
    (20493035423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell574_rightExp :
    Real.exp (23 / 32 : ℝ) ≤ (2564833467 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 32 : ℝ) (1022715083577 / 1000000000000 : ℝ)
    (2564833467 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell574_denomUpper :
    Real.exp (7833444116092931 / 1250000000000000 : ℝ) ≤ (164614188281 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7833444116092931 / 1250000000000000 : ℝ) (304081884111 /
    250000000000 : ℝ) (164614188281 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell574_denomLower :
    (2611881250971 / 5000000000 : ℝ) ≤ Real.exp (7822985142576677 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7822985142576677 / 1250000000000000 : ℝ) (608004769791 /
    500000000000 : ℝ) (2611881250971 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell574_product_lower :
    (8047594517576677 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (287 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell574_leftExp
    (by norm_num : (0 : ℝ) ≤ (20493035423 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell574_product_upper :
    Real.pi * Real.exp (23 / 32 : ℝ) ≤ (8057662866092931 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell574_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell574_endpointLower :
    (4828214463 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (287 / 800 : ℝ) (23 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8047594517576677 / 1250000000000000 : ℝ) (Real.pi * Real.exp (287 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell574_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 32 : ℝ) - (287 / 1600 : ℝ)) ≤
      (164614188281 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell574_denomUpper
    linarith [hpThetaJensenCell574_product_upper]
  have hi : (1 / (164614188281 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 32 : ℝ) - (287 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (164614188281 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (164614188281 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((287 / 1600 : ℝ) - Real.pi * Real.exp (23 / 32 : ℝ)) := by
    rw [show (287 / 1600 : ℝ) - Real.pi * Real.exp (23 / 32 : ℝ) =
      -(Real.pi * Real.exp (23 / 32 : ℝ) - (287 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (287 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (287 / 400 : ℝ)) := by
    have h := hpThetaJensenCell574_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (164614188281 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell574_endpointUpper :
    hpThetaJensenKernelEndpointUpper (287 / 800 : ℝ) (23 / 64 : ℝ) ≤ (4895684463 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 32 : ℝ)) (8057662866092931 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell574_product_upper
  have hD : (2611881250971 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (287 / 400 : ℝ) - (23 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell574_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell574_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (287 / 400 : ℝ) - (23 / 128 : ℝ)) ≤
      (1 / (2611881250971 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2611881250971 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 128 : ℝ) - Real.pi * Real.exp (287 / 400 : ℝ)) ≤
      (2 / (2611881250971 / 5000000000 : ℝ) : ℝ) := by
    rw [show (23 / 128 : ℝ) - Real.pi * Real.exp (287 / 400 : ℝ) =
      -(Real.pi * Real.exp (287 / 400 : ℝ) - (23 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8057662866092931 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (8057662866092931 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell574_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (287 / 800 : ℝ) (23 / 64 : ℝ)) :
    (4828214463 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4895684463 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell574_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell574_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell575_leftExp :
    (10259333867 / 5000000000 : ℝ) ≤ Real.exp (23 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 32 : ℝ) (127839385447 / 125000000000 : ℝ)
    (10259333867 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell575_rightExp :
    Real.exp (18 / 25 : ℝ) ≤ (20544332107 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18 / 25 : ℝ) (204551006833 / 200000000000 : ℝ)
    (20544332107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell575_denomUpper :
    Real.exp (62745054937026451 / 10000000000000000 : ℝ) ≤ (5308638013477 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (62745054937026451 / 10000000000000000 : ℝ)
    (1216622159079 / 1000000000000 : ℝ) (5308638013477 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell575_denomLower :
    (658043995589 / 1250000000 : ℝ) ≤ Real.exp (3916330150237033 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3916330150237033 / 625000000000000 : ℝ) (152037962783 /
    125000000000 : ℝ) (658043995589 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell575_product_lower :
    (4028830150237033 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell575_leftExp
    (by norm_num : (0 : ℝ) ≤ (10259333867 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell575_product_upper :
    Real.pi * Real.exp (18 / 25 : ℝ) ≤ (64541929937026451 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell575_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell575_endpointLower :
    (4804754341 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 64 : ℝ) (9 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4028830150237033 / 625000000000000 : ℝ) (Real.pi * Real.exp (23 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell575_product_lower
  have hD : Real.exp (Real.pi * Real.exp (18 / 25 : ℝ) - (23 / 128 : ℝ)) ≤
      (5308638013477 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell575_denomUpper
    linarith [hpThetaJensenCell575_product_upper]
  have hi : (1 / (5308638013477 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (18 / 25 : ℝ) - (23 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5308638013477 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5308638013477 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 128 : ℝ) - Real.pi * Real.exp (18 / 25 : ℝ)) := by
    rw [show (23 / 128 : ℝ) - Real.pi * Real.exp (18 / 25 : ℝ) =
      -(Real.pi * Real.exp (18 / 25 : ℝ) - (23 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 32 : ℝ)) := by
    have h := hpThetaJensenCell575_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5308638013477 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell575_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 64 : ℝ) (9 / 25 : ℝ) ≤ (4871942579 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (18 / 25 : ℝ)) (64541929937026451 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell575_product_upper
  have hD : (658043995589 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 32 : ℝ) - (9 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell575_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell575_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 32 : ℝ) - (9 / 50 : ℝ)) ≤
      (1 / (658043995589 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (658043995589 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 50 : ℝ) - Real.pi * Real.exp (23 / 32 : ℝ)) ≤
      (2 / (658043995589 / 1250000000 : ℝ) : ℝ) := by
    rw [show (9 / 50 : ℝ) - Real.pi * Real.exp (23 / 32 : ℝ) =
      -(Real.pi * Real.exp (23 / 32 : ℝ) - (9 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64541929937026451 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (64541929937026451 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell575_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 64 : ℝ) (9 / 25 : ℝ)) :
    (4804754341 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4871942579 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell575_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell575_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell576_leftExp :
    (10272166053 / 5000000000 : ℝ) ≤ Real.exp (18 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (18 / 25 : ℝ) (255688758541 / 250000000000 : ℝ)
    (10272166053 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell576_rightExp :
    Real.exp (577 / 800 : ℝ) ≤ (20570028579 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (577 / 800 : ℝ) (511397493157 / 500000000000 : ℝ)
    (20570028579 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell576_denomUpper :
    Real.exp (62822657793586347 / 10000000000000000 : ℝ) ≤ (2674997411909 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (62822657793586347 / 10000000000000000 : ℝ) (76057327287
    / 62500000000 : ℝ) (2674997411909 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell576_denomLower :
    (2652655125083 / 5000000000 : ℝ) ≤ Real.exp (3921174024347047 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3921174024347047 / 625000000000000 : ℝ) (3801869747 /
    3125000000 : ℝ) (2652655125083 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell576_product_lower :
    (4033869336847047 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (18 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell576_leftExp
    (by norm_num : (0 : ℝ) ≤ (10272166053 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell576_product_upper :
    Real.pi * Real.exp (577 / 800 : ℝ) ≤ (64622657793586347 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell576_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell576_endpointLower :
    (4781357039 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 25 : ℝ) (577 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4033869336847047 / 625000000000000 : ℝ) (Real.pi * Real.exp (18 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell576_product_lower
  have hD : Real.exp (Real.pi * Real.exp (577 / 800 : ℝ) - (9 / 50 : ℝ)) ≤
      (2674997411909 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell576_denomUpper
    linarith [hpThetaJensenCell576_product_upper]
  have hi : (1 / (2674997411909 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (577 / 800 : ℝ) - (9 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2674997411909 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2674997411909 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 50 : ℝ) - Real.pi * Real.exp (577 / 800 : ℝ)) := by
    rw [show (9 / 50 : ℝ) - Real.pi * Real.exp (577 / 800 : ℝ) =
      -(Real.pi * Real.exp (577 / 800 : ℝ) - (9 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (18 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (18 / 25 : ℝ)) := by
    have h := hpThetaJensenCell576_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2674997411909 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell576_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 25 : ℝ) (577 / 1600 : ℝ) ≤ (1212066003 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (577 / 800 : ℝ)) (64622657793586347 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (577 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell576_product_upper
  have hD : (2652655125083 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (18 / 25 : ℝ) - (577 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell576_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell576_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (18 / 25 : ℝ) - (577 / 3200 : ℝ)) ≤
      (1 / (2652655125083 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2652655125083 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((577 / 3200 : ℝ) - Real.pi * Real.exp (18 / 25 : ℝ)) ≤
      (2 / (2652655125083 / 5000000000 : ℝ) : ℝ) := by
    rw [show (577 / 3200 : ℝ) - Real.pi * Real.exp (18 / 25 : ℝ) =
      -(Real.pi * Real.exp (18 / 25 : ℝ) - (577 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64622657793586347 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (64622657793586347 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell576_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 25 : ℝ) (577 / 1600 : ℝ)) :
    (4781357039 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1212066003 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell576_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell576_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell577_leftExp :
    (10285014289 / 5000000000 : ℝ) ≤ Real.exp (577 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (577 / 800 : ℝ) (1022794986313 / 1000000000000 : ℝ)
    (10285014289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell577_rightExp :
    Real.exp (289 / 400 : ℝ) ≤ (2574469649 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (289 / 400 : ℝ) (1022834940023 / 1000000000000 : ℝ)
    (2574469649 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell577_denomUpper :
    Real.exp (7862545203010857 / 1250000000000000 : ℝ) ≤ (5391728265303 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7862545203010857 / 1250000000000000 : ℝ) (243442553951 /
    200000000000 : ℝ) (5391728265303 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell577_denomLower :
    (5346641121749 / 10000000000 : ℝ) ≤ Real.exp (3926024201276011 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3926024201276011 / 625000000000000 : ℝ) (76055836917 /
    62500000000 : ℝ) (5346641121749 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell577_product_lower :
    (4038914826276011 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (577 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell577_leftExp
    (by norm_num : (0 : ℝ) ≤ (10285014289 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell577_product_upper :
    Real.pi * Real.exp (289 / 400 : ℝ) ≤ (8087935828010857 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell577_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell577_endpointLower :
    (4758022697 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (577 / 1600 : ℝ) (289 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4038914826276011 / 625000000000000 : ℝ) (Real.pi * Real.exp (577 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell577_product_lower
  have hD : Real.exp (Real.pi * Real.exp (289 / 400 : ℝ) - (577 / 3200 : ℝ)) ≤
      (5391728265303 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell577_denomUpper
    linarith [hpThetaJensenCell577_product_upper]
  have hi : (1 / (5391728265303 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (289 / 400 : ℝ) - (577 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5391728265303 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5391728265303 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((577 / 3200 : ℝ) - Real.pi * Real.exp (289 / 400 : ℝ)) := by
    rw [show (577 / 3200 : ℝ) - Real.pi * Real.exp (289 / 400 : ℝ) =
      -(Real.pi * Real.exp (289 / 400 : ℝ) - (577 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (577 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (577 / 800 : ℝ)) := by
    have h := hpThetaJensenCell577_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5391728265303 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell577_endpointUpper :
    hpThetaJensenKernelEndpointUpper (577 / 1600 : ℝ) (289 / 800 : ℝ) ≤ (964929781 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (289 / 400 : ℝ)) (8087935828010857 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (289 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell577_product_upper
  have hD : (5346641121749 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (577 / 800 : ℝ) - (289 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell577_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell577_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (577 / 800 : ℝ) - (289 / 1600 : ℝ)) ≤
      (1 / (5346641121749 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5346641121749 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((289 / 1600 : ℝ) - Real.pi * Real.exp (577 / 800 : ℝ)) ≤
      (2 / (5346641121749 / 10000000000 : ℝ) : ℝ) := by
    rw [show (289 / 1600 : ℝ) - Real.pi * Real.exp (577 / 800 : ℝ) =
      -(Real.pi * Real.exp (577 / 800 : ℝ) - (289 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8087935828010857 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (8087935828010857 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell577_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (577 / 1600 : ℝ) (289 / 800 : ℝ)) :
    (4758022697 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (964929781 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell577_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell577_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell578_leftExp :
    (2059575719 / 1000000000 : ℝ) ≤ Real.exp (289 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (289 / 400 : ℝ) (511417470011 / 500000000000 : ℝ)
    (2059575719 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell578_rightExp :
    Real.exp (579 / 800 : ℝ) ≤ (4124303597 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (579 / 800 : ℝ) (1022874895293 / 1000000000000 : ℝ)
    (4124303597 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell578_denomUpper :
    Real.exp (12595633310210021 / 2000000000000000 : ℝ) ≤ (2716921094401 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12595633310210021 / 2000000000000000 : ℝ) (1217508759333
    / 1000000000000 : ℝ) (2716921094401 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell578_denomLower :
    (1077669677349 / 2000000000 : ℝ) ≤ Real.exp (786176137775581 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (786176137775581 / 125000000000000 : ℝ) (243437783587 /
    200000000000 : ℝ) (1077669677349 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell578_product_lower :
    (808793325275581 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (289 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell578_leftExp
    (by norm_num : (0 : ℝ) ≤ (2059575719 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell578_product_upper :
    Real.pi * Real.exp (579 / 800 : ℝ) ≤ (12956883310210021 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell578_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell578_endpointLower :
    (4734751453 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (289 / 800 : ℝ) (579 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (808793325275581 / 125000000000000 : ℝ) (Real.pi * Real.exp (289 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell578_product_lower
  have hD : Real.exp (Real.pi * Real.exp (579 / 800 : ℝ) - (289 / 1600 : ℝ)) ≤
      (2716921094401 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell578_denomUpper
    linarith [hpThetaJensenCell578_product_upper]
  have hi : (1 / (2716921094401 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (579 / 800 : ℝ) - (289 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2716921094401 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2716921094401 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((289 / 1600 : ℝ) - Real.pi * Real.exp (579 / 800 : ℝ)) := by
    rw [show (289 / 1600 : ℝ) - Real.pi * Real.exp (579 / 800 : ℝ) =
      -(Real.pi * Real.exp (579 / 800 : ℝ) - (289 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (289 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (289 / 400 : ℝ)) := by
    have h := hpThetaJensenCell578_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2716921094401 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell578_endpointUpper :
    hpThetaJensenKernelEndpointUpper (289 / 800 : ℝ) (579 / 1600 : ℝ) ≤ (4801097399 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (579 / 800 : ℝ)) (12956883310210021 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (579 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell578_product_upper
  have hD : (1077669677349 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (289 / 400 : ℝ) - (579 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell578_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell578_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (289 / 400 : ℝ) - (579 / 3200 : ℝ)) ≤
      (1 / (1077669677349 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1077669677349 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((579 / 3200 : ℝ) - Real.pi * Real.exp (289 / 400 : ℝ)) ≤
      (2 / (1077669677349 / 2000000000 : ℝ) : ℝ) := by
    rw [show (579 / 3200 : ℝ) - Real.pi * Real.exp (289 / 400 : ℝ) =
      -(Real.pi * Real.exp (289 / 400 : ℝ) - (579 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12956883310210021 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (12956883310210021 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell578_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (289 / 800 : ℝ) (579 / 1600 : ℝ)) :
    (4734751453 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4801097399 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell578_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell578_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell579_leftExp :
    (644422437 / 312500000 : ℝ) ≤ Real.exp (579 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (579 / 800 : ℝ) (255718723823 / 250000000000 : ℝ)
    (644422437 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell579_rightExp :
    Real.exp (29 / 40 : ℝ) ≤ (20647311 / 10000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 40 : ℝ) (255728713031 / 250000000000 : ℝ)
    (20647311 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell579_denomUpper :
    Real.exp (63056072706423 / 10000000000000 : ℝ) ≤ (1369085123283 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63056072706423 / 10000000000000 : ℝ) (9742441649 /
    8000000000 : ℝ) (1369085123283 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell579_denomLower :
    (1086087179629 / 2000000000 : ℝ) ≤ Real.exp (245983968462463 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (245983968462463 / 39062500000000 : ℝ) (608742450813 /
    500000000000 : ℝ) (1086087179629 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell579_product_lower :
    (253064046587463 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (579 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell579_leftExp
    (by norm_num : (0 : ℝ) ≤ (644422437 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell579_product_upper :
    Real.pi * Real.exp (29 / 40 : ℝ) ≤ (64865447706423 / 10000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell579_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell579_endpointLower :
    (4711543441 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (579 / 1600 : ℝ) (29 / 80 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (253064046587463 / 39062500000000 : ℝ) (Real.pi * Real.exp (579 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell579_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 40 : ℝ) - (579 / 3200 : ℝ)) ≤
      (1369085123283 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell579_denomUpper
    linarith [hpThetaJensenCell579_product_upper]
  have hi : (1 / (1369085123283 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 40 : ℝ) - (579 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1369085123283 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1369085123283 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((579 / 3200 : ℝ) - Real.pi * Real.exp (29 / 40 : ℝ)) := by
    rw [show (579 / 3200 : ℝ) - Real.pi * Real.exp (29 / 40 : ℝ) =
      -(Real.pi * Real.exp (29 / 40 : ℝ) - (579 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (579 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (579 / 800 : ℝ)) := by
    have h := hpThetaJensenCell579_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1369085123283 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell579_endpointUpper :
    hpThetaJensenKernelEndpointUpper (579 / 1600 : ℝ) (29 / 80 : ℝ) ≤ (477760963 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 40 : ℝ)) (64865447706423 / 10000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell579_product_upper
  have hD : (1086087179629 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (579 / 800 : ℝ) - (29 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell579_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell579_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (579 / 800 : ℝ) - (29 / 160 : ℝ)) ≤
      (1 / (1086087179629 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1086087179629 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 160 : ℝ) - Real.pi * Real.exp (579 / 800 : ℝ)) ≤
      (2 / (1086087179629 / 2000000000 : ℝ) : ℝ) := by
    rw [show (29 / 160 : ℝ) - Real.pi * Real.exp (579 / 800 : ℝ) =
      -(Real.pi * Real.exp (579 / 800 : ℝ) - (29 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (64865447706423 / 10000000000000 : ℝ) ^ 2 - 6 *
      (64865447706423 / 10000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell579_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (579 / 1600 : ℝ) (29 / 80 : ℝ)) :
    (4711543441 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (477760963 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell579_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell579_endpointUpper

def hpThetaJensenCellsBatch028Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5163169421 / 10000000000 : ℝ)
  | 1 => (5138845583 / 10000000000 : ℝ)
  | 2 => (1278645601 / 2500000000 : ℝ)
  | 3 => (5090380049 / 10000000000 : ℝ)
  | 4 => (1266559671 / 2500000000 : ℝ)
  | 5 => (5042158471 / 10000000000 : ℝ)
  | 6 => (200725583 / 400000000 : ℝ)
  | 7 => (624272769 / 1250000000 : ℝ)
  | 8 => (124257159 / 250000000 : ℝ)
  | 9 => (4946452359 / 10000000000 : ℝ)
  | 10 => (615335037 / 1250000000 : ℝ)
  | 11 => (4898970329 / 10000000000 : ℝ)
  | 12 => (2437661301 / 5000000000 : ℝ)
  | 13 => (303233579 / 625000000 : ℝ)
  | 14 => (4828214463 / 10000000000 : ℝ)
  | 15 => (4804754341 / 10000000000 : ℝ)
  | 16 => (4781357039 / 10000000000 : ℝ)
  | 17 => (4758022697 / 10000000000 : ℝ)
  | 18 => (4734751453 / 10000000000 : ℝ)
  | 19 => (4711543441 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch028Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5234634593 / 10000000000 : ℝ)
  | 1 => (104200447 / 200000000 : ℝ)
  | 2 => (2592735609 / 5000000000 : ℝ)
  | 3 => (5160981369 / 10000000000 : ℝ)
  | 4 => (1284138243 / 2500000000 : ℝ)
  | 5 => (319511637 / 625000000 : ℝ)
  | 6 => (2543940597 / 5000000000 : ℝ)
  | 7 => (2531819071 / 5000000000 : ℝ)
  | 8 => (1007891439 / 2000000000 : ℝ)
  | 9 => (5015338511 / 10000000000 : ℝ)
  | 10 => (19965129 / 40000000 : ℝ)
  | 11 => (4967288561 / 10000000000 : ℝ)
  | 12 => (4943357601 / 10000000000 : ℝ)
  | 13 => (4919489519 / 10000000000 : ℝ)
  | 14 => (4895684463 / 10000000000 : ℝ)
  | 15 => (4871942579 / 10000000000 : ℝ)
  | 16 => (1212066003 / 2500000000 : ℝ)
  | 17 => (964929781 / 2000000000 : ℝ)
  | 18 => (4801097399 / 10000000000 : ℝ)
  | 19 => (477760963 / 1000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch028_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch028Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch028Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell560_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell561_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell562_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell563_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell564_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell565_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell566_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell567_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell568_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell569_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell570_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell571_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell572_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell573_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell574_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell575_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell576_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell577_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell578_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell579_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper] at h ⊢
    exact h

end HodgeProofHP
