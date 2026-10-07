import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell700_leftExp :
    (23988752939 / 10000000000 : ℝ) ≤ Real.exp (7 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 8 : ℝ) (1027721021151 / 1000000000000 : ℝ)
    (23988752939 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell700_rightExp :
    Real.exp (701 / 800 : ℝ) ≤ (24018757631 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (701 / 800 : ℝ) (1027761167289 / 1000000000000 : ℝ)
    (24018757631 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell700_denomUpper :
    Real.exp (73269660842246183 / 10000000000000000 : ℝ) ≤ (15207609053801 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (73269660842246183 / 10000000000000000 : ℝ)
    (1257301415111 / 1000000000000 : ℝ) (15207609053801 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell700_denomLower :
    (1506018861157 / 1000000000 : ℝ) ≤ Real.exp (9146531165392361 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9146531165392361 / 1250000000000000 : ℝ) (1256918736981
    / 1000000000000 : ℝ) (1506018861157 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell700_product_lower :
    (9420359290392361 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell700_leftExp
    (by norm_num : (0 : ℝ) ≤ (23988752939 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell700_product_upper :
    Real.pi * Real.exp (701 / 800 : ℝ) ≤ (75457160842246183 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell700_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell700_endpointLower :
    (2393075569 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 16 : ℝ) (701 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9420359290392361 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell700_product_lower
  have hD : Real.exp (Real.pi * Real.exp (701 / 800 : ℝ) - (7 / 32 : ℝ)) ≤
      (15207609053801 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell700_denomUpper
    linarith [hpThetaJensenCell700_product_upper]
  have hi : (1 / (15207609053801 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (701 / 800 : ℝ) - (7 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15207609053801 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15207609053801 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 32 : ℝ) - Real.pi * Real.exp (701 / 800 : ℝ)) := by
    rw [show (7 / 32 : ℝ) - Real.pi * Real.exp (701 / 800 : ℝ) =
      -(Real.pi * Real.exp (701 / 800 : ℝ) - (7 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 8 : ℝ)) := by
    have h := hpThetaJensenCell700_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15207609053801 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell700_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 16 : ℝ) (701 / 1600 : ℝ) ≤ (2429685199 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (701 / 800 : ℝ)) (75457160842246183 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (701 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell700_product_upper
  have hD : (1506018861157 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 8 : ℝ) - (701 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell700_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell700_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 8 : ℝ) - (701 / 3200 : ℝ)) ≤
      (1 / (1506018861157 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1506018861157 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((701 / 3200 : ℝ) - Real.pi * Real.exp (7 / 8 : ℝ)) ≤
      (2 / (1506018861157 / 1000000000 : ℝ) : ℝ) := by
    rw [show (701 / 3200 : ℝ) - Real.pi * Real.exp (7 / 8 : ℝ) =
      -(Real.pi * Real.exp (7 / 8 : ℝ) - (701 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (75457160842246183 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (75457160842246183 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell700_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 16 : ℝ) (701 / 1600 : ℝ)) :
    (2393075569 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2429685199 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell700_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell700_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell701_leftExp :
    (24018757629 / 10000000000 : ℝ) ≤ Real.exp (701 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (701 / 800 : ℝ) (128470145911 / 125000000000 : ℝ)
    (24018757629 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell701_rightExp :
    Real.exp (351 / 400 : ℝ) ≤ (480975997 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (351 / 400 : ℝ) (1027801314993 / 1000000000000 : ℝ)
    (480975997 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell701_denomUpper :
    Real.exp (1467218325343221 / 200000000000000 : ℝ) ≤ (15347021877923 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1467218325343221 / 200000000000000 : ℝ) (19650937733 /
    15625000000 : ℝ) (15347021877923 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell701_denomLower :
    (15198070754133 / 10000000000 : ℝ) ≤ Real.exp (9157923352150671 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9157923352150671 / 1250000000000000 : ℝ) (9822474721 /
    7812500000 : ℝ) (15198070754133 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell701_product_lower :
    (9432142102150671 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (701 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell701_leftExp
    (by norm_num : (0 : ℝ) ≤ (24018757629 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell701_product_upper :
    Real.pi * Real.exp (351 / 400 : ℝ) ≤ (1511030825343221 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell701_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell701_endpointLower :
    (95120421 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (701 / 1600 : ℝ) (351 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9432142102150671 / 1250000000000000 : ℝ) (Real.pi * Real.exp (701 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell701_product_lower
  have hD : Real.exp (Real.pi * Real.exp (351 / 400 : ℝ) - (701 / 3200 : ℝ)) ≤
      (15347021877923 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell701_denomUpper
    linarith [hpThetaJensenCell701_product_upper]
  have hi : (1 / (15347021877923 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (351 / 400 : ℝ) - (701 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15347021877923 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15347021877923 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((701 / 3200 : ℝ) - Real.pi * Real.exp (351 / 400 : ℝ)) := by
    rw [show (701 / 3200 : ℝ) - Real.pi * Real.exp (351 / 400 : ℝ) =
      -(Real.pi * Real.exp (351 / 400 : ℝ) - (701 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (701 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (701 / 800 : ℝ)) := by
    have h := hpThetaJensenCell701_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15347021877923 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell701_endpointUpper :
    hpThetaJensenKernelEndpointUpper (701 / 1600 : ℝ) (351 / 800 : ℝ) ≤ (75450531 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (351 / 400 : ℝ)) (1511030825343221 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (351 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell701_product_upper
  have hD : (15198070754133 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (701 / 800 : ℝ) - (351 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell701_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell701_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (701 / 800 : ℝ) - (351 / 1600 : ℝ)) ≤
      (1 / (15198070754133 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15198070754133 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((351 / 1600 : ℝ) - Real.pi * Real.exp (701 / 800 : ℝ)) ≤
      (2 / (15198070754133 / 10000000000 : ℝ) : ℝ) := by
    rw [show (351 / 1600 : ℝ) - Real.pi * Real.exp (701 / 800 : ℝ) =
      -(Real.pi * Real.exp (701 / 800 : ℝ) - (351 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1511030825343221 / 200000000000000 : ℝ) ^ 2 - 6 *
      (1511030825343221 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell701_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (701 / 1600 : ℝ) (351 / 800 : ℝ)) :
    (95120421 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (75450531 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell701_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell701_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell702_leftExp :
    (3006099981 / 1250000000 : ℝ) ≤ Real.exp (351 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (351 / 400 : ℝ) (64237582187 / 62500000000 : ℝ)
    (3006099981 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell702_rightExp :
    Real.exp (703 / 800 : ℝ) ≤ (12039439823 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (703 / 800 : ℝ) (513920732133 / 500000000000 : ℝ)
    (12039439823 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell702_denomUpper :
    Real.exp (36726144871858039 / 5000000000000000 : ℝ) ≤ (15487895578247 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36726144871858039 / 5000000000000000 : ℝ) (39313099409 /
    31250000000 : ℝ) (15487895578247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell702_denomLower :
    (15337396091587 / 10000000000 : ℝ) ≤ Real.exp (1146166284563719 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1146166284563719 / 156250000000000 : ℝ) (62881767847 /
    50000000000 : ℝ) (15337396091587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell702_product_lower :
    (1180492456438719 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (351 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell702_leftExp
    (by norm_num : (0 : ℝ) ≤ (3006099981 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell702_product_upper :
    Real.pi * Real.exp (703 / 800 : ℝ) ≤ (37823019871858039 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell702_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell702_endpointLower :
    (29537641 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (351 / 800 : ℝ) (703 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1180492456438719 / 156250000000000 : ℝ) (Real.pi * Real.exp (351 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell702_product_lower
  have hD : Real.exp (Real.pi * Real.exp (703 / 800 : ℝ) - (351 / 1600 : ℝ)) ≤
      (15487895578247 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell702_denomUpper
    linarith [hpThetaJensenCell702_product_upper]
  have hi : (1 / (15487895578247 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (703 / 800 : ℝ) - (351 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15487895578247 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15487895578247 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((351 / 1600 : ℝ) - Real.pi * Real.exp (703 / 800 : ℝ)) := by
    rw [show (351 / 1600 : ℝ) - Real.pi * Real.exp (703 / 800 : ℝ) =
      -(Real.pi * Real.exp (703 / 800 : ℝ) - (351 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (351 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (351 / 400 : ℝ)) := by
    have h := hpThetaJensenCell702_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15487895578247 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell702_endpointUpper :
    hpThetaJensenKernelEndpointUpper (351 / 800 : ℝ) (703 / 1600 : ℝ) ≤ (1199607643 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (703 / 800 : ℝ)) (37823019871858039 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (703 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell702_product_upper
  have hD : (15337396091587 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (351 / 400 : ℝ) - (703 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell702_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell702_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (351 / 400 : ℝ) - (703 / 3200 : ℝ)) ≤
      (1 / (15337396091587 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15337396091587 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((703 / 3200 : ℝ) - Real.pi * Real.exp (351 / 400 : ℝ)) ≤
      (2 / (15337396091587 / 10000000000 : ℝ) : ℝ) := by
    rw [show (703 / 3200 : ℝ) - Real.pi * Real.exp (351 / 400 : ℝ) =
      -(Real.pi * Real.exp (351 / 400 : ℝ) - (703 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37823019871858039 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (37823019871858039 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell702_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (351 / 800 : ℝ) (703 / 1600 : ℝ)) :
    (29537641 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1199607643 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell702_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell702_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell703_leftExp :
    (6019719911 / 2500000000 : ℝ) ≤ Real.exp (703 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (703 / 800 : ℝ) (205568292853 / 200000000000 : ℝ)
    (6019719911 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell703_rightExp :
    Real.exp (22 / 25 : ℝ) ≤ (4821799413 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22 / 25 : ℝ) (256970403777 / 250000000000 : ℝ)
    (4821799413 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell703_denomUpper :
    Real.exp (14708756283284909 / 2000000000000000 : ℝ) ≤ (3126049426337 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14708756283284909 / 2000000000000000 : ℝ) (629189457317
    / 500000000000 : ℝ) (3126049426337 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell703_denomLower :
    (77390906939 / 50000000 : ℝ) ≤ Real.exp (2295187989329789 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2295187989329789 / 312500000000000 : ℝ) (251598903191 /
    200000000000 : ℝ) (77390906939 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell703_product_lower :
    (2363937989329789 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (703 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell703_leftExp
    (by norm_num : (0 : ℝ) ≤ (6019719911 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell703_product_upper :
    Real.pi * Real.exp (22 / 25 : ℝ) ≤ (15148131283284909 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell703_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell703_endpointLower :
    (469615551 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (703 / 1600 : ℝ) (11 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2363937989329789 / 312500000000000 : ℝ) (Real.pi * Real.exp (703 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell703_product_lower
  have hD : Real.exp (Real.pi * Real.exp (22 / 25 : ℝ) - (703 / 3200 : ℝ)) ≤
      (3126049426337 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell703_denomUpper
    linarith [hpThetaJensenCell703_product_upper]
  have hi : (1 / (3126049426337 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (22 / 25 : ℝ) - (703 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3126049426337 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3126049426337 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((703 / 3200 : ℝ) - Real.pi * Real.exp (22 / 25 : ℝ)) := by
    rw [show (703 / 3200 : ℝ) - Real.pi * Real.exp (22 / 25 : ℝ) =
      -(Real.pi * Real.exp (22 / 25 : ℝ) - (703 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (703 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (703 / 800 : ℝ)) := by
    have h := hpThetaJensenCell703_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3126049426337 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell703_endpointUpper :
    hpThetaJensenKernelEndpointUpper (703 / 1600 : ℝ) (11 / 25 : ℝ) ≤ (2384079999 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (22 / 25 : ℝ)) (15148131283284909 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell703_product_upper
  have hD : (77390906939 / 50000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (703 / 800 : ℝ) - (11 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell703_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell703_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (703 / 800 : ℝ) - (11 / 50 : ℝ)) ≤
      (1 / (77390906939 / 50000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (77390906939 / 50000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 50 : ℝ) - Real.pi * Real.exp (703 / 800 : ℝ)) ≤
      (2 / (77390906939 / 50000000 : ℝ) : ℝ) := by
    rw [show (11 / 50 : ℝ) - Real.pi * Real.exp (703 / 800 : ℝ) =
      -(Real.pi * Real.exp (703 / 800 : ℝ) - (11 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15148131283284909 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (15148131283284909 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell703_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (703 / 1600 : ℝ) (11 / 25 : ℝ)) :
    (469615551 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2384079999 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell703_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell703_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell704_leftExp :
    (24108997063 / 10000000000 : ℝ) ≤ Real.exp (22 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (22 / 25 : ℝ) (1027881615107 / 1000000000000 : ℝ)
    (24108997063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell704_rightExp :
    Real.exp (141 / 160 : ℝ) ≤ (4827830431 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (141 / 160 : ℝ) (513960883759 / 500000000000 : ℝ)
    (4827830431 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell704_denomUpper :
    Real.exp (14727078287216583 / 2000000000000000 : ℝ) ≤ (15774093739759 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14727078287216583 / 2000000000000000 : ℝ) (1258739216571
    / 1000000000000 : ℝ) (15774093739759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell704_denomLower :
    (3124088721963 / 2000000000 : ℝ) ≤ Real.exp (9192188412643037 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9192188412643037 / 1250000000000000 : ℝ) (125835424233 /
    100000000000 : ℝ) (3124088721963 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell704_product_lower :
    (9467579037643037 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (22 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell704_leftExp
    (by norm_num : (0 : ℝ) ≤ (24108997063 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell704_product_upper :
    Real.pi * Real.exp (141 / 160 : ℝ) ≤ (15167078287216583 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell704_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell704_endpointLower :
    (583302467 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 25 : ℝ) (141 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9467579037643037 / 1250000000000000 : ℝ) (Real.pi * Real.exp (22 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell704_product_lower
  have hD : Real.exp (Real.pi * Real.exp (141 / 160 : ℝ) - (11 / 50 : ℝ)) ≤
      (15774093739759 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell704_denomUpper
    linarith [hpThetaJensenCell704_product_upper]
  have hi : (1 / (15774093739759 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (141 / 160 : ℝ) - (11 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15774093739759 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15774093739759 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 50 : ℝ) - Real.pi * Real.exp (141 / 160 : ℝ)) := by
    rw [show (11 / 50 : ℝ) - Real.pi * Real.exp (141 / 160 : ℝ) =
      -(Real.pi * Real.exp (141 / 160 : ℝ) - (11 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (22 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (22 / 25 : ℝ)) := by
    have h := hpThetaJensenCell704_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15774093739759 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell704_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 25 : ℝ) (141 / 320 : ℝ) ≤ (2369011051 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (141 / 160 : ℝ)) (15167078287216583 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (141 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell704_product_upper
  have hD : (3124088721963 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (22 / 25 : ℝ) - (141 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell704_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell704_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (22 / 25 : ℝ) - (141 / 640 : ℝ)) ≤
      (1 / (3124088721963 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3124088721963 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((141 / 640 : ℝ) - Real.pi * Real.exp (22 / 25 : ℝ)) ≤
      (2 / (3124088721963 / 2000000000 : ℝ) : ℝ) := by
    rw [show (141 / 640 : ℝ) - Real.pi * Real.exp (22 / 25 : ℝ) =
      -(Real.pi * Real.exp (22 / 25 : ℝ) - (141 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15167078287216583 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (15167078287216583 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell704_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 25 : ℝ) (141 / 320 : ℝ)) :
    (583302467 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2369011051 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell704_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell704_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell705_leftExp :
    (24139152153 / 10000000000 : ℝ) ≤ Real.exp (141 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (141 / 160 : ℝ) (1027921767517 / 1000000000000 : ℝ)
    (24139152153 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell705_rightExp :
    Real.exp (353 / 400 : ℝ) ≤ (24169344961 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (353 / 400 : ℝ) (128495240187 / 125000000000 : ℝ)
    (24169344961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell705_denomUpper :
    Real.exp (73727119944062873 / 10000000000000000 : ℝ) ≤ (3183890561457 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73727119944062873 / 10000000000000000 : ℝ) (251820017577
    / 200000000000 : ℝ) (3183890561457 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell705_denomLower :
    (7882099973787 / 5000000000 : ℝ) ≤ Real.exp (9203639661330947 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9203639661330947 / 1250000000000000 : ℝ) (314678634271 /
    250000000000 : ℝ) (7882099973787 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell705_product_lower :
    (9479420911330947 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (141 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell705_leftExp
    (by norm_num : (0 : ℝ) ≤ (24139152153 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell705_product_upper :
    Real.pi * Real.exp (353 / 400 : ℝ) ≤ (75930244944062873 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell705_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell705_endpointLower :
    (2318407537 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (141 / 320 : ℝ) (353 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9479420911330947 / 1250000000000000 : ℝ) (Real.pi * Real.exp (141 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell705_product_lower
  have hD : Real.exp (Real.pi * Real.exp (353 / 400 : ℝ) - (141 / 640 : ℝ)) ≤
      (3183890561457 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell705_denomUpper
    linarith [hpThetaJensenCell705_product_upper]
  have hi : (1 / (3183890561457 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (353 / 400 : ℝ) - (141 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3183890561457 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3183890561457 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((141 / 640 : ℝ) - Real.pi * Real.exp (353 / 400 : ℝ)) := by
    rw [show (141 / 640 : ℝ) - Real.pi * Real.exp (353 / 400 : ℝ) =
      -(Real.pi * Real.exp (353 / 400 : ℝ) - (141 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (141 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (141 / 160 : ℝ)) := by
    have h := hpThetaJensenCell705_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3183890561457 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell705_endpointUpper :
    hpThetaJensenKernelEndpointUpper (141 / 320 : ℝ) (353 / 800 : ℝ) ≤ (2354008359 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (353 / 400 : ℝ)) (75930244944062873 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (353 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell705_product_upper
  have hD : (7882099973787 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (141 / 160 : ℝ) - (353 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell705_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell705_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (141 / 160 : ℝ) - (353 / 1600 : ℝ)) ≤
      (1 / (7882099973787 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7882099973787 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((353 / 1600 : ℝ) - Real.pi * Real.exp (141 / 160 : ℝ)) ≤
      (2 / (7882099973787 / 5000000000 : ℝ) : ℝ) := by
    rw [show (353 / 1600 : ℝ) - Real.pi * Real.exp (141 / 160 : ℝ) =
      -(Real.pi * Real.exp (141 / 160 : ℝ) - (353 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (75930244944062873 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (75930244944062873 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell705_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (141 / 320 : ℝ) (353 / 800 : ℝ)) :
    (2318407537 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2354008359 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell705_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell705_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell706_leftExp :
    (75529203 / 31250000 : ℝ) ≤ Real.exp (353 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (353 / 400 : ℝ) (205592384299 / 200000000000 : ℝ)
    (75529203 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell706_rightExp :
    Real.exp (707 / 800 : ℝ) ≤ (24199575533 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (707 / 800 : ℝ) (1028002077043 / 1000000000000 : ℝ)
    (24199575533 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell706_denomUpper :
    Real.exp (73818967097444069 / 10000000000000000 : ℝ) ≤ (3213268396937 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73818967097444069 / 10000000000000000 : ℝ) (10075692237
    / 8000000000 : ℝ) (3213268396937 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell706_denomLower :
    (15909467800619 / 10000000000 : ℝ) ≤ Real.exp (14398602689761 / 1953125000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14398602689761 / 1953125000000 : ℝ) (1259075401217 /
    1000000000000 : ℝ) (15909467800619 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell706_product_lower :
    (29660242488897 / 3906250000000 : ℝ) ≤ Real.pi * Real.exp (353 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell706_leftExp
    (by norm_num : (0 : ℝ) ≤ (75529203 / 31250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell706_product_upper :
    Real.pi * Real.exp (707 / 800 : ℝ) ≤ (76025217097444069 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell706_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell706_endpointLower :
    (2303670677 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (353 / 800 : ℝ) (707 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (29660242488897 / 3906250000000 : ℝ) (Real.pi * Real.exp (353 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell706_product_lower
  have hD : Real.exp (Real.pi * Real.exp (707 / 800 : ℝ) - (353 / 1600 : ℝ)) ≤
      (3213268396937 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell706_denomUpper
    linarith [hpThetaJensenCell706_product_upper]
  have hi : (1 / (3213268396937 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (707 / 800 : ℝ) - (353 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3213268396937 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3213268396937 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((353 / 1600 : ℝ) - Real.pi * Real.exp (707 / 800 : ℝ)) := by
    rw [show (353 / 1600 : ℝ) - Real.pi * Real.exp (707 / 800 : ℝ) =
      -(Real.pi * Real.exp (707 / 800 : ℝ) - (353 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (353 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (353 / 400 : ℝ)) := by
    have h := hpThetaJensenCell706_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3213268396937 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell706_endpointUpper :
    hpThetaJensenKernelEndpointUpper (353 / 800 : ℝ) (707 / 1600 : ℝ) ≤ (14619199 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (707 / 800 : ℝ)) (76025217097444069 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (707 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell706_product_upper
  have hD : (15909467800619 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (353 / 400 : ℝ) - (707 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell706_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell706_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (353 / 400 : ℝ) - (707 / 3200 : ℝ)) ≤
      (1 / (15909467800619 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15909467800619 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((707 / 3200 : ℝ) - Real.pi * Real.exp (353 / 400 : ℝ)) ≤
      (2 / (15909467800619 / 10000000000 : ℝ) : ℝ) := by
    rw [show (707 / 3200 : ℝ) - Real.pi * Real.exp (353 / 400 : ℝ) =
      -(Real.pi * Real.exp (353 / 400 : ℝ) - (707 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (76025217097444069 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (76025217097444069 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell706_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (353 / 800 : ℝ) (707 / 1600 : ℝ)) :
    (2303670677 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14619199 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell706_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell706_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell707_leftExp :
    (24199575531 / 10000000000 : ℝ) ≤ Real.exp (707 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (707 / 800 : ℝ) (514001038521 / 500000000000 : ℝ)
    (24199575531 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell707_rightExp :
    Real.exp (177 / 200 : ℝ) ≤ (6057460979 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (177 / 200 : ℝ) (514021117079 / 500000000000 : ℝ)
    (6057460979 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell707_denomUpper :
    Real.exp (18477733259399547 / 2500000000000000 : ℝ) ≤ (8107389560521 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18477733259399547 / 2500000000000000 : ℝ) (1259823542779
    / 1000000000000 : ℝ) (8107389560521 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell707_denomLower :
    (16056264792531 / 10000000000 : ℝ) ≤ Real.exp (9226586611448169 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9226586611448169 / 1250000000000000 : ℝ) (1259436835739
    / 1000000000000 : ℝ) (16056264792531 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell707_product_lower :
    (9503149111448169 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (707 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell707_leftExp
    (by norm_num : (0 : ℝ) ≤ (24199575531 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell707_product_upper :
    Real.pi * Real.exp (177 / 200 : ℝ) ≤ (19030077009399547 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell707_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell707_endpointLower :
    (2288999203 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (707 / 1600 : ℝ) (177 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9503149111448169 / 1250000000000000 : ℝ) (Real.pi * Real.exp (707 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell707_product_lower
  have hD : Real.exp (Real.pi * Real.exp (177 / 200 : ℝ) - (707 / 3200 : ℝ)) ≤
      (8107389560521 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell707_denomUpper
    linarith [hpThetaJensenCell707_product_upper]
  have hi : (1 / (8107389560521 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (177 / 200 : ℝ) - (707 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8107389560521 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8107389560521 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((707 / 3200 : ℝ) - Real.pi * Real.exp (177 / 200 : ℝ)) := by
    rw [show (707 / 3200 : ℝ) - Real.pi * Real.exp (177 / 200 : ℝ) =
      -(Real.pi * Real.exp (177 / 200 : ℝ) - (707 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (707 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (707 / 800 : ℝ)) := by
    have h := hpThetaJensenCell707_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8107389560521 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell707_endpointUpper :
    hpThetaJensenKernelEndpointUpper (707 / 1600 : ℝ) (177 / 400 : ℝ) ≤ (2324201409 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (177 / 200 : ℝ)) (19030077009399547 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (177 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell707_product_upper
  have hD : (16056264792531 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (707 / 800 : ℝ) - (177 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell707_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell707_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (707 / 800 : ℝ) - (177 / 800 : ℝ)) ≤
      (1 / (16056264792531 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16056264792531 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((177 / 800 : ℝ) - Real.pi * Real.exp (707 / 800 : ℝ)) ≤
      (2 / (16056264792531 / 10000000000 : ℝ) : ℝ) := by
    rw [show (177 / 800 : ℝ) - Real.pi * Real.exp (707 / 800 : ℝ) =
      -(Real.pi * Real.exp (707 / 800 : ℝ) - (177 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19030077009399547 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (19030077009399547 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell707_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (707 / 1600 : ℝ) (177 / 400 : ℝ)) :
    (2288999203 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2324201409 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell707_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell707_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell708_leftExp :
    (12114921957 / 5000000000 : ℝ) ≤ Real.exp (177 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (177 / 200 : ℝ) (1028042234157 / 1000000000000 : ℝ)
    (12114921957 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell708_rightExp :
    Real.exp (709 / 800 : ℝ) ≤ (12130075079 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (709 / 800 : ℝ) (514041196421 / 500000000000 : ℝ)
    (12130075079 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell708_denomUpper :
    Real.exp (37001508957660847 / 5000000000000000 : ℝ) ≤ (16364782307571 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37001508957660847 / 5000000000000000 : ℝ) (630093064187
    / 500000000000 : ℝ) (16364782307571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell708_denomLower :
    (16204608776553 / 10000000000 : ℝ) ≤ Real.exp (4619041175091943 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4619041175091943 / 625000000000000 : ℝ) (314949710419 /
    250000000000 : ℝ) (16204608776553 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell708_product_lower :
    (4757517737591943 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (177 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell708_leftExp
    (by norm_num : (0 : ℝ) ≤ (12114921957 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell708_product_upper :
    Real.pi * Real.exp (709 / 800 : ℝ) ≤ (38107758957660847 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell708_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell708_endpointLower :
    (568598257 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (177 / 400 : ℝ) (709 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4757517737591943 / 625000000000000 : ℝ) (Real.pi * Real.exp (177 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell708_product_lower
  have hD : Real.exp (Real.pi * Real.exp (709 / 800 : ℝ) - (177 / 800 : ℝ)) ≤
      (16364782307571 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell708_denomUpper
    linarith [hpThetaJensenCell708_product_upper]
  have hi : (1 / (16364782307571 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (709 / 800 : ℝ) - (177 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16364782307571 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16364782307571 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((177 / 800 : ℝ) - Real.pi * Real.exp (709 / 800 : ℝ)) := by
    rw [show (177 / 800 : ℝ) - Real.pi * Real.exp (709 / 800 : ℝ) =
      -(Real.pi * Real.exp (709 / 800 : ℝ) - (177 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (177 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (177 / 200 : ℝ)) := by
    have h := hpThetaJensenCell708_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16364782307571 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell708_endpointUpper :
    hpThetaJensenKernelEndpointUpper (177 / 400 : ℝ) (709 / 1600 : ℝ) ≤ (2309396979 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (709 / 800 : ℝ)) (38107758957660847 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (709 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell708_product_upper
  have hD : (16204608776553 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (177 / 200 : ℝ) - (709 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell708_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell708_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (177 / 200 : ℝ) - (709 / 3200 : ℝ)) ≤
      (1 / (16204608776553 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16204608776553 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((709 / 3200 : ℝ) - Real.pi * Real.exp (177 / 200 : ℝ)) ≤
      (2 / (16204608776553 / 10000000000 : ℝ) : ℝ) := by
    rw [show (709 / 3200 : ℝ) - Real.pi * Real.exp (177 / 200 : ℝ) =
      -(Real.pi * Real.exp (177 / 200 : ℝ) - (709 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38107758957660847 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (38107758957660847 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell708_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (177 / 400 : ℝ) (709 / 1600 : ℝ)) :
    (568598257 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2309396979 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell708_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell708_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell709_leftExp :
    (6065037539 / 2500000000 : ℝ) ≤ Real.exp (709 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (709 / 800 : ℝ) (1028082392841 / 1000000000000 : ℝ)
    (6065037539 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell709_rightExp :
    Real.exp (71 / 80 : ℝ) ≤ (24290494307 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 80 : ℝ) (205624510619 / 200000000000 : ℝ)
    (24290494307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell709_denomUpper :
    Real.exp (74095221881411051 / 10000000000000000 : ℝ) ≤ (8258184932947 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (74095221881411051 / 10000000000000000 : ℝ)
    (1260549287439 / 1000000000000 : ℝ) (8258184932947 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell709_denomLower :
    (8177258913641 / 5000000000 : ℝ) ≤ Real.exp (2312398239027761 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2312398239027761 / 312500000000000 : ℝ) (630080710021 /
    500000000000 : ℝ) (8177258913641 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell709_product_lower :
    (2381734176527761 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (709 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell709_leftExp
    (by norm_num : (0 : ℝ) ≤ (6065037539 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell709_product_upper :
    Real.pi * Real.exp (71 / 80 : ℝ) ≤ (76310846881411051 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell709_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell709_endpointLower :
    (70620377 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (709 / 1600 : ℝ) (71 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2381734176527761 / 312500000000000 : ℝ) (Real.pi * Real.exp (709 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell709_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 80 : ℝ) - (709 / 3200 : ℝ)) ≤
      (8258184932947 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell709_denomUpper
    linarith [hpThetaJensenCell709_product_upper]
  have hi : (1 / (8258184932947 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 80 : ℝ) - (709 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8258184932947 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8258184932947 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((709 / 3200 : ℝ) - Real.pi * Real.exp (71 / 80 : ℝ)) := by
    rw [show (709 / 3200 : ℝ) - Real.pi * Real.exp (71 / 80 : ℝ) =
      -(Real.pi * Real.exp (71 / 80 : ℝ) - (709 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (709 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (709 / 800 : ℝ)) := by
    have h := hpThetaJensenCell709_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8258184932947 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell709_endpointUpper :
    hpThetaJensenKernelEndpointUpper (709 / 1600 : ℝ) (71 / 160 : ℝ) ≤ (2294658463 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 80 : ℝ)) (76310846881411051 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell709_product_upper
  have hD : (8177258913641 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (709 / 800 : ℝ) - (71 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell709_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell709_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (709 / 800 : ℝ) - (71 / 320 : ℝ)) ≤
      (1 / (8177258913641 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8177258913641 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 320 : ℝ) - Real.pi * Real.exp (709 / 800 : ℝ)) ≤
      (2 / (8177258913641 / 5000000000 : ℝ) : ℝ) := by
    rw [show (71 / 320 : ℝ) - Real.pi * Real.exp (709 / 800 : ℝ) =
      -(Real.pi * Real.exp (709 / 800 : ℝ) - (71 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (76310846881411051 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (76310846881411051 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell709_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (709 / 1600 : ℝ) (71 / 160 : ℝ)) :
    (70620377 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2294658463 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell709_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell709_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell710_leftExp :
    (4858098861 / 2000000000 : ℝ) ≤ Real.exp (71 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 80 : ℝ) (514061276547 / 500000000000 : ℝ)
    (4858098861 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell710_rightExp :
    Real.exp (711 / 800 : ℝ) ≤ (2432087641 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (711 / 800 : ℝ) (1028162714917 / 1000000000000 : ℝ)
    (2432087641 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell710_denomUpper :
    Real.exp (7418754508352113 / 1000000000000000 : ℝ) ≤ (16669560344851 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7418754508352113 / 1000000000000000 : ℝ) (126091302099 /
    100000000000 : ℝ) (16669560344851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell710_denomLower :
    (8253005127627 / 5000000000 : ℝ) ≤ Real.exp (1852223689615839 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1852223689615839 / 250000000000000 : ℝ) (1260524571867 /
    1000000000000 : ℝ) (8253005127627 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell710_product_lower :
    (1907770564615839 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell710_leftExp
    (by norm_num : (0 : ℝ) ≤ (4858098861 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell710_product_upper :
    Real.pi * Real.exp (711 / 800 : ℝ) ≤ (7640629508352113 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell710_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell710_endpointLower :
    (1122688111 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 160 : ℝ) (711 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1907770564615839 / 250000000000000 : ℝ) (Real.pi * Real.exp (71 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell710_product_lower
  have hD : Real.exp (Real.pi * Real.exp (711 / 800 : ℝ) - (71 / 320 : ℝ)) ≤
      (16669560344851 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell710_denomUpper
    linarith [hpThetaJensenCell710_product_upper]
  have hi : (1 / (16669560344851 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (711 / 800 : ℝ) - (71 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16669560344851 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16669560344851 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 320 : ℝ) - Real.pi * Real.exp (711 / 800 : ℝ)) := by
    rw [show (71 / 320 : ℝ) - Real.pi * Real.exp (711 / 800 : ℝ) =
      -(Real.pi * Real.exp (711 / 800 : ℝ) - (71 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 80 : ℝ)) := by
    have h := hpThetaJensenCell710_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16669560344851 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell710_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 160 : ℝ) (711 / 1600 : ℝ) ≤ (227998577 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (711 / 800 : ℝ)) (7640629508352113 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (711 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell710_product_upper
  have hD : (8253005127627 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 80 : ℝ) - (711 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell710_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell710_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 80 : ℝ) - (711 / 3200 : ℝ)) ≤
      (1 / (8253005127627 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8253005127627 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((711 / 3200 : ℝ) - Real.pi * Real.exp (71 / 80 : ℝ)) ≤
      (2 / (8253005127627 / 5000000000 : ℝ) : ℝ) := by
    rw [show (711 / 3200 : ℝ) - Real.pi * Real.exp (71 / 80 : ℝ) =
      -(Real.pi * Real.exp (71 / 80 : ℝ) - (711 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7640629508352113 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (7640629508352113 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell710_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 160 : ℝ) (711 / 1600 : ℝ)) :
    (1122688111 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (227998577 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell710_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell710_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell711_leftExp :
    (3040109551 / 1250000000 : ℝ) ≤ Real.exp (711 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (711 / 800 : ℝ) (257040678729 / 250000000000 : ℝ)
    (3040109551 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell711_rightExp :
    Real.exp (89 / 100 : ℝ) ≤ (12175648257 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89 / 100 : ℝ) (1028202878307 / 1000000000000 : ℝ)
    (12175648257 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell711_denomUpper :
    Real.exp (37139993834653401 / 5000000000000000 : ℝ) ≤ (672974901227 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37139993834653401 / 5000000000000000 : ℝ) (1261277330047
    / 1000000000000 : ℝ) (672974901227 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell711_denomLower :
    (65074627333 / 39062500 : ℝ) ≤ Real.exp (1159082355568149 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1159082355568149 / 156250000000000 : ℝ) (630444149083 /
    500000000000 : ℝ) (65074627333 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell711_product_lower :
    (1193847980568149 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (711 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell711_leftExp
    (by norm_num : (0 : ℝ) ≤ (3040109551 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell711_product_upper :
    Real.pi * Real.exp (89 / 100 : ℝ) ≤ (38250931334653401 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell711_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell711_endpointLower :
    (557741353 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (711 / 1600 : ℝ) (89 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1193847980568149 / 156250000000000 : ℝ) (Real.pi * Real.exp (711 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell711_product_lower
  have hD : Real.exp (Real.pi * Real.exp (89 / 100 : ℝ) - (711 / 3200 : ℝ)) ≤
      (672974901227 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell711_denomUpper
    linarith [hpThetaJensenCell711_product_upper]
  have hi : (1 / (672974901227 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (89 / 100 : ℝ) - (711 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (672974901227 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (672974901227 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((711 / 3200 : ℝ) - Real.pi * Real.exp (89 / 100 : ℝ)) := by
    rw [show (711 / 3200 : ℝ) - Real.pi * Real.exp (89 / 100 : ℝ) =
      -(Real.pi * Real.exp (89 / 100 : ℝ) - (711 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (711 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (711 / 800 : ℝ)) := by
    have h := hpThetaJensenCell711_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (672974901227 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell711_endpointUpper :
    hpThetaJensenKernelEndpointUpper (711 / 1600 : ℝ) (89 / 200 : ℝ) ≤ (2265378811 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (89 / 100 : ℝ)) (38250931334653401 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (89 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell711_product_upper
  have hD : (65074627333 / 39062500 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (711 / 800 : ℝ) - (89 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell711_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell711_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (711 / 800 : ℝ) - (89 / 400 : ℝ)) ≤
      (1 / (65074627333 / 39062500 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (65074627333 / 39062500 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((89 / 400 : ℝ) - Real.pi * Real.exp (711 / 800 : ℝ)) ≤
      (2 / (65074627333 / 39062500 : ℝ) : ℝ) := by
    rw [show (89 / 400 : ℝ) - Real.pi * Real.exp (711 / 800 : ℝ) =
      -(Real.pi * Real.exp (711 / 800 : ℝ) - (89 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38250931334653401 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (38250931334653401 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell711_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (711 / 1600 : ℝ) (89 / 200 : ℝ)) :
    (557741353 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2265378811 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell711_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell711_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell712_leftExp :
    (23780563 / 9765625 : ℝ) ≤ Real.exp (89 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (89 / 100 : ℝ) (514101439153 / 500000000000 : ℝ)
    (23780563 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell712_rightExp :
    Real.exp (713 / 800 : ℝ) ≤ (24381754667 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (713 / 800 : ℝ) (1028243043267 / 1000000000000 : ℝ)
    (24381754667 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell712_denomUpper :
    Real.exp (74372549789564531 / 10000000000000000 : ℝ) ≤ (1698082545329 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (74372549789564531 / 10000000000000000 : ℝ)
    (1261642215641 / 1000000000000 : ℝ) (1698082545329 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell712_denomLower :
    (16813819628127 / 10000000000 : ℝ) ≤ Real.exp (145065846311967 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (145065846311967 / 19531250000000 : ℝ) (31531314999 /
    25000000000 : ℝ) (16813819628127 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell712_product_lower :
    (9338603309537 / 1220703125000 : ℝ) ≤ Real.pi * Real.exp (89 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell712_leftExp
    (by norm_num : (0 : ℝ) ≤ (23780563 / 9765625 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell712_product_upper :
    Real.pi * Real.exp (713 / 800 : ℝ) ≤ (76597549789564531 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell712_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell712_endpointLower :
    (2216619541 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 200 : ℝ) (713 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9338603309537 / 1220703125000 : ℝ) (Real.pi * Real.exp (89 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell712_product_lower
  have hD : Real.exp (Real.pi * Real.exp (713 / 800 : ℝ) - (89 / 400 : ℝ)) ≤
      (1698082545329 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell712_denomUpper
    linarith [hpThetaJensenCell712_product_upper]
  have hi : (1 / (1698082545329 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (713 / 800 : ℝ) - (89 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1698082545329 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1698082545329 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((89 / 400 : ℝ) - Real.pi * Real.exp (713 / 800 : ℝ)) := by
    rw [show (89 / 400 : ℝ) - Real.pi * Real.exp (713 / 800 : ℝ) =
      -(Real.pi * Real.exp (713 / 800 : ℝ) - (89 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (89 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (89 / 100 : ℝ)) := by
    have h := hpThetaJensenCell712_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1698082545329 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell712_endpointUpper :
    hpThetaJensenKernelEndpointUpper (89 / 200 : ℝ) (713 / 1600 : ℝ) ≤ (450167499 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (713 / 800 : ℝ)) (76597549789564531 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (713 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell712_product_upper
  have hD : (16813819628127 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (89 / 100 : ℝ) - (713 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell712_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell712_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (89 / 100 : ℝ) - (713 / 3200 : ℝ)) ≤
      (1 / (16813819628127 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16813819628127 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((713 / 3200 : ℝ) - Real.pi * Real.exp (89 / 100 : ℝ)) ≤
      (2 / (16813819628127 / 10000000000 : ℝ) : ℝ) := by
    rw [show (713 / 3200 : ℝ) - Real.pi * Real.exp (89 / 100 : ℝ) =
      -(Real.pi * Real.exp (89 / 100 : ℝ) - (713 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (76597549789564531 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (76597549789564531 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell712_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (89 / 200 : ℝ) (713 / 1600 : ℝ)) :
    (2216619541 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (450167499 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell712_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell712_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell713_leftExp :
    (4876350933 / 2000000000 : ℝ) ≤ Real.exp (713 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (713 / 800 : ℝ) (514121521633 / 500000000000 : ℝ)
    (4876350933 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell713_rightExp :
    Real.exp (357 / 400 : ℝ) ≤ (6103062729 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (357 / 400 : ℝ) (205656641959 / 200000000000 : ℝ)
    (6103062729 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell713_denomUpper :
    Real.exp (18616307897987297 / 2500000000000000 : ℝ) ≤ (8569469190979 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18616307897987297 / 2500000000000000 : ℝ) (315501919699
    / 250000000000 : ℝ) (8569469190979 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell713_denomLower :
    (16970174365877 / 10000000000 : ℝ) ≤ Real.exp (1859156885038167 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1859156885038167 / 250000000000000 : ℝ) (31540436957 /
    25000000000 : ℝ) (16970174365877 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell713_product_lower :
    (1914938135038167 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (713 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell713_leftExp
    (by norm_num : (0 : ℝ) ≤ (4876350933 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell713_product_upper :
    Real.pi * Real.exp (357 / 400 : ℝ) ≤ (19173339147987297 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell713_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell713_endpointLower :
    (550584629 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (713 / 1600 : ℝ) (357 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1914938135038167 / 250000000000000 : ℝ) (Real.pi * Real.exp (713 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell713_product_lower
  have hD : Real.exp (Real.pi * Real.exp (357 / 400 : ℝ) - (713 / 3200 : ℝ)) ≤
      (8569469190979 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell713_denomUpper
    linarith [hpThetaJensenCell713_product_upper]
  have hi : (1 / (8569469190979 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (357 / 400 : ℝ) - (713 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8569469190979 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8569469190979 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((713 / 3200 : ℝ) - Real.pi * Real.exp (357 / 400 : ℝ)) := by
    rw [show (713 / 3200 : ℝ) - Real.pi * Real.exp (357 / 400 : ℝ) =
      -(Real.pi * Real.exp (357 / 400 : ℝ) - (713 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (713 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (713 / 800 : ℝ)) := by
    have h := hpThetaJensenCell713_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8569469190979 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell713_endpointUpper :
    hpThetaJensenKernelEndpointUpper (713 / 1600 : ℝ) (357 / 800 : ℝ) ≤ (2183947 / 9765625 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (357 / 400 : ℝ)) (19173339147987297 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (357 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell713_product_upper
  have hD : (16970174365877 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (713 / 800 : ℝ) - (357 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell713_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell713_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (713 / 800 : ℝ) - (357 / 1600 : ℝ)) ≤
      (1 / (16970174365877 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16970174365877 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((357 / 1600 : ℝ) - Real.pi * Real.exp (713 / 800 : ℝ)) ≤
      (2 / (16970174365877 / 10000000000 : ℝ) : ℝ) := by
    rw [show (357 / 1600 : ℝ) - Real.pi * Real.exp (713 / 800 : ℝ) =
      -(Real.pi * Real.exp (713 / 800 : ℝ) - (357 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19173339147987297 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (19173339147987297 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell713_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (713 / 1600 : ℝ) (357 / 800 : ℝ)) :
    (550584629 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2183947 / 9765625 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell713_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell713_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell714_leftExp :
    (4882450183 / 2000000000 : ℝ) ≤ Real.exp (357 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (357 / 400 : ℝ) (514141604897 / 500000000000 : ℝ)
    (4882450183 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell714_rightExp :
    Real.exp (143 / 160 : ℝ) ≤ (2444278531 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (143 / 160 : ℝ) (257080844473 / 250000000000 : ℝ)
    (2444278531 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell714_denomUpper :
    Real.exp (7455803323039883 / 1000000000000000 : ℝ) ≤ (1351463347 / 781250 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7455803323039883 / 1000000000000000 : ℝ) (1262373720559
    / 1000000000000 : ℝ) (1351463347 / 781250 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell714_denomLower :
    (4282047018221 / 2500000000 : ℝ) ≤ Real.exp (1861473929413917 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1861473929413917 / 250000000000000 : ℝ) (630991467081 /
    500000000000 : ℝ) (4282047018221 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell714_product_lower :
    (1917333304413917 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (357 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell714_leftExp
    (by norm_num : (0 : ℝ) ≤ (4882450183 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell714_product_upper :
    Real.pi * Real.exp (143 / 160 : ℝ) ≤ (7678928323039883 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell714_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell714_endpointLower :
    (2188122243 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (357 / 800 : ℝ) (143 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1917333304413917 / 250000000000000 : ℝ) (Real.pi * Real.exp (357 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell714_product_lower
  have hD : Real.exp (Real.pi * Real.exp (143 / 160 : ℝ) - (357 / 1600 : ℝ)) ≤
      (1351463347 / 781250 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell714_denomUpper
    linarith [hpThetaJensenCell714_product_upper]
  have hi : (1 / (1351463347 / 781250 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (143 / 160 : ℝ) - (357 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1351463347 / 781250 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1351463347 / 781250 : ℝ) : ℝ) ≤
      2 * Real.exp ((357 / 1600 : ℝ) - Real.pi * Real.exp (143 / 160 : ℝ)) := by
    rw [show (357 / 1600 : ℝ) - Real.pi * Real.exp (143 / 160 : ℝ) =
      -(Real.pi * Real.exp (143 / 160 : ℝ) - (357 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (357 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (357 / 400 : ℝ)) := by
    have h := hpThetaJensenCell714_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1351463347 / 781250 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell714_endpointUpper :
    hpThetaJensenKernelEndpointUpper (357 / 800 : ℝ) (143 / 320 : ℝ) ≤ (277743927 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (143 / 160 : ℝ)) (7678928323039883 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (143 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell714_product_upper
  have hD : (4282047018221 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (357 / 400 : ℝ) - (143 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell714_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell714_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (357 / 400 : ℝ) - (143 / 640 : ℝ)) ≤
      (1 / (4282047018221 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4282047018221 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((143 / 640 : ℝ) - Real.pi * Real.exp (357 / 400 : ℝ)) ≤
      (2 / (4282047018221 / 2500000000 : ℝ) : ℝ) := by
    rw [show (143 / 640 : ℝ) - Real.pi * Real.exp (357 / 400 : ℝ) =
      -(Real.pi * Real.exp (357 / 400 : ℝ) - (143 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7678928323039883 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (7678928323039883 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell714_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (357 / 800 : ℝ) (143 / 320 : ℝ)) :
    (2188122243 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (277743927 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell714_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell714_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell715_leftExp :
    (6110696327 / 2500000000 : ℝ) ≤ Real.exp (143 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (143 / 160 : ℝ) (1028323377891 / 1000000000000 : ℝ)
    (6110696327 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell715_rightExp :
    Real.exp (179 / 200 : ℝ) ≤ (3059169737 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (179 / 200 : ℝ) (1028363547559 / 1000000000000 : ℝ)
    (3059169737 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell715_denomUpper :
    Real.exp (9331369356571041 / 1250000000000000 : ℝ) ≤ (8730111298347 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9331369356571041 / 1250000000000000 : ℝ) (252548068391 /
    200000000000 : ℝ) (8730111298347 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell715_denomLower :
    (4321970061327 / 2500000000 : ℝ) ≤ Real.exp (2329742461916573 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2329742461916573 / 312500000000000 : ℝ) (252469793723 /
    200000000000 : ℝ) (4321970061327 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell715_product_lower :
    (2399664336916573 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (143 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell715_leftExp
    (by norm_num : (0 : ℝ) ≤ (6110696327 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell715_product_upper :
    Real.pi * Real.exp (179 / 200 : ℝ) ≤ (9610666231571041 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell715_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell715_endpointLower :
    (1086985313 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (143 / 320 : ℝ) (179 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2399664336916573 / 312500000000000 : ℝ) (Real.pi * Real.exp (143 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell715_product_lower
  have hD : Real.exp (Real.pi * Real.exp (179 / 200 : ℝ) - (143 / 640 : ℝ)) ≤
      (8730111298347 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell715_denomUpper
    linarith [hpThetaJensenCell715_product_upper]
  have hi : (1 / (8730111298347 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (179 / 200 : ℝ) - (143 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8730111298347 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8730111298347 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((143 / 640 : ℝ) - Real.pi * Real.exp (179 / 200 : ℝ)) := by
    rw [show (143 / 640 : ℝ) - Real.pi * Real.exp (179 / 200 : ℝ) =
      -(Real.pi * Real.exp (179 / 200 : ℝ) - (143 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (143 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (143 / 160 : ℝ)) := by
    have h := hpThetaJensenCell715_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8730111298347 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell715_endpointUpper :
    hpThetaJensenKernelEndpointUpper (143 / 320 : ℝ) (179 / 400 : ℝ) ≤ (34493851 / 156250000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (179 / 200 : ℝ)) (9610666231571041 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (179 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell715_product_upper
  have hD : (4321970061327 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (143 / 160 : ℝ) - (179 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell715_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell715_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (143 / 160 : ℝ) - (179 / 800 : ℝ)) ≤
      (1 / (4321970061327 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4321970061327 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((179 / 800 : ℝ) - Real.pi * Real.exp (143 / 160 : ℝ)) ≤
      (2 / (4321970061327 / 2500000000 : ℝ) : ℝ) := by
    rw [show (179 / 800 : ℝ) - Real.pi * Real.exp (143 / 160 : ℝ) =
      -(Real.pi * Real.exp (143 / 160 : ℝ) - (179 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9610666231571041 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (9610666231571041 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell715_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (143 / 320 : ℝ) (179 / 400 : ℝ)) :
    (1086985313 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (34493851 / 156250000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell715_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell715_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell716_leftExp :
    (12236678947 / 5000000000 : ℝ) ≤ Real.exp (179 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (179 / 200 : ℝ) (514181773779 / 500000000000 : ℝ)
    (12236678947 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell716_rightExp :
    Real.exp (717 / 800 : ℝ) ≤ (24503968721 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (717 / 800 : ℝ) (205680743759 / 200000000000 : ℝ)
    (24503968721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell716_denomUpper :
    Real.exp (74743996606112553 / 10000000000000000 : ℝ) ≤ (17623433664063 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (74743996606112553 / 10000000000000000 : ℝ)
    (1263107544009 / 1000000000000 : ℝ) (17623433664063 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell716_denomLower :
    (8724635325641 / 5000000000 : ℝ) ≤ Real.exp (4665292523307953 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4665292523307953 / 625000000000000 : ℝ) (1262715582701 /
    1000000000000 : ℝ) (8724635325641 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell716_product_lower :
    (4805331585807953 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (179 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell716_leftExp
    (by norm_num : (0 : ℝ) ≤ (12236678947 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell716_product_upper :
    Real.pi * Real.exp (717 / 800 : ℝ) ≤ (76981496606112553 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell716_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell716_endpointLower :
    (2159883569 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (179 / 400 : ℝ) (717 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4805331585807953 / 625000000000000 : ℝ) (Real.pi * Real.exp (179 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell716_product_lower
  have hD : Real.exp (Real.pi * Real.exp (717 / 800 : ℝ) - (179 / 800 : ℝ)) ≤
      (17623433664063 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell716_denomUpper
    linarith [hpThetaJensenCell716_product_upper]
  have hi : (1 / (17623433664063 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (717 / 800 : ℝ) - (179 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17623433664063 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17623433664063 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((179 / 800 : ℝ) - Real.pi * Real.exp (717 / 800 : ℝ)) := by
    rw [show (179 / 800 : ℝ) - Real.pi * Real.exp (717 / 800 : ℝ) =
      -(Real.pi * Real.exp (717 / 800 : ℝ) - (179 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (179 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (179 / 200 : ℝ)) := by
    have h := hpThetaJensenCell716_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17623433664063 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell716_endpointUpper :
    hpThetaJensenKernelEndpointUpper (179 / 400 : ℝ) (717 / 1600 : ℝ) ≤ (1096663387 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (717 / 800 : ℝ)) (76981496606112553 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (717 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell716_product_upper
  have hD : (8724635325641 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (179 / 200 : ℝ) - (717 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell716_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell716_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (179 / 200 : ℝ) - (717 / 3200 : ℝ)) ≤
      (1 / (8724635325641 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8724635325641 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((717 / 3200 : ℝ) - Real.pi * Real.exp (179 / 200 : ℝ)) ≤
      (2 / (8724635325641 / 5000000000 : ℝ) : ℝ) := by
    rw [show (717 / 3200 : ℝ) - Real.pi * Real.exp (179 / 200 : ℝ) =
      -(Real.pi * Real.exp (179 / 200 : ℝ) - (717 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (76981496606112553 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (76981496606112553 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell716_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (179 / 400 : ℝ) (717 / 1600 : ℝ)) :
    (2159883569 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1096663387 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell716_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell716_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell717_leftExp :
    (24503968719 / 10000000000 : ℝ) ≤ Real.exp (717 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (717 / 800 : ℝ) (514201859397 / 500000000000 : ℝ)
    (24503968719 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell717_rightExp :
    Real.exp (359 / 400 : ℝ) ≤ (24534617833 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (359 / 400 : ℝ) (1028443891599 / 1000000000000 : ℝ)
    (24534617833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell717_denomUpper :
    Real.exp (74837158641827969 / 10000000000000000 : ℝ) ≤ (17788384323983 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (74837158641827969 / 10000000000000000 : ℝ)
    (1263475327763 / 1000000000000 : ℝ) (17788384323983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell717_denomLower :
    (17612379290741 / 10000000000 : ℝ) ≤ Real.exp (9342215261982581 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9342215261982581 / 1250000000000000 : ℝ) (252616555487 /
    200000000000 : ℝ) (17612379290741 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell717_product_lower :
    (9622684011982581 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (717 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell717_leftExp
    (by norm_num : (0 : ℝ) ≤ (24503968719 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell717_product_upper :
    Real.pi * Real.exp (359 / 400 : ℝ) ≤ (77077783641827969 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell717_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell717_endpointLower :
    (1072930487 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (717 / 1600 : ℝ) (359 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9622684011982581 / 1250000000000000 : ℝ) (Real.pi * Real.exp (717 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell717_product_lower
  have hD : Real.exp (Real.pi * Real.exp (359 / 400 : ℝ) - (717 / 3200 : ℝ)) ≤
      (17788384323983 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell717_denomUpper
    linarith [hpThetaJensenCell717_product_upper]
  have hi : (1 / (17788384323983 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (359 / 400 : ℝ) - (717 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17788384323983 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17788384323983 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((717 / 3200 : ℝ) - Real.pi * Real.exp (359 / 400 : ℝ)) := by
    rw [show (717 / 3200 : ℝ) - Real.pi * Real.exp (359 / 400 : ℝ) =
      -(Real.pi * Real.exp (359 / 400 : ℝ) - (717 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (717 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (717 / 800 : ℝ)) := by
    have h := hpThetaJensenCell717_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17788384323983 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell717_endpointUpper :
    hpThetaJensenKernelEndpointUpper (717 / 1600 : ℝ) (359 / 800 : ℝ) ≤ (2179112249 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (359 / 400 : ℝ)) (77077783641827969 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (359 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell717_product_upper
  have hD : (17612379290741 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (717 / 800 : ℝ) - (359 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell717_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell717_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (717 / 800 : ℝ) - (359 / 1600 : ℝ)) ≤
      (1 / (17612379290741 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17612379290741 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((359 / 1600 : ℝ) - Real.pi * Real.exp (717 / 800 : ℝ)) ≤
      (2 / (17612379290741 / 10000000000 : ℝ) : ℝ) := by
    rw [show (359 / 1600 : ℝ) - Real.pi * Real.exp (717 / 800 : ℝ) =
      -(Real.pi * Real.exp (717 / 800 : ℝ) - (359 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77077783641827969 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (77077783641827969 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell717_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (717 / 1600 : ℝ) (359 / 800 : ℝ)) :
    (1072930487 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2179112249 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell717_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell717_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell718_leftExp :
    (24534617831 / 10000000000 : ℝ) ≤ Real.exp (359 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (359 / 400 : ℝ) (514221945799 / 500000000000 : ℝ)
    (24534617831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell718_rightExp :
    Real.exp (719 / 800 : ℝ) ≤ (24565305281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (719 / 800 : ℝ) (514242032987 / 500000000000 : ℝ)
    (24565305281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell718_denomUpper :
    Real.exp (74930441113652633 / 10000000000000000 : ℝ) ≤ (359101902417 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (74930441113652633 / 10000000000000000 : ℝ)
    (1263843694269 / 1000000000000 : ℝ) (359101902417 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell718_denomLower :
    (17777226429901 / 10000000000 : ℝ) ≤ Real.exp (9353860512615869 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9353860512615869 / 1250000000000000 : ℝ) (2467676863 /
    1953125000 : ℝ) (17777226429901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell718_product_lower :
    (9634719887615869 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (359 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell718_leftExp
    (by norm_num : (0 : ℝ) ≤ (24534617831 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell718_product_upper :
    Real.pi * Real.exp (719 / 800 : ℝ) ≤ (77174191113652633 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell718_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell718_endpointLower :
    (106595137 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (359 / 800 : ℝ) (719 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (9634719887615869 / 1250000000000000 : ℝ) (Real.pi * Real.exp (359 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell718_product_lower
  have hD : Real.exp (Real.pi * Real.exp (719 / 800 : ℝ) - (359 / 1600 : ℝ)) ≤
      (359101902417 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell718_denomUpper
    linarith [hpThetaJensenCell718_product_upper]
  have hi : (1 / (359101902417 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (719 / 800 : ℝ) - (359 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (359101902417 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (359101902417 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((359 / 1600 : ℝ) - Real.pi * Real.exp (719 / 800 : ℝ)) := by
    rw [show (359 / 1600 : ℝ) - Real.pi * Real.exp (719 / 800 : ℝ) =
      -(Real.pi * Real.exp (719 / 800 : ℝ) - (359 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (359 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (359 / 400 : ℝ)) := by
    have h := hpThetaJensenCell718_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (359101902417 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell718_endpointUpper :
    hpThetaJensenKernelEndpointUpper (359 / 800 : ℝ) (719 / 1600 : ℝ) ≤ (216496279 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (719 / 800 : ℝ)) (77174191113652633 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (719 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell718_product_upper
  have hD : (17777226429901 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (359 / 400 : ℝ) - (719 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell718_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell718_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (359 / 400 : ℝ) - (719 / 3200 : ℝ)) ≤
      (1 / (17777226429901 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17777226429901 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((719 / 3200 : ℝ) - Real.pi * Real.exp (359 / 400 : ℝ)) ≤
      (2 / (17777226429901 / 10000000000 : ℝ) : ℝ) := by
    rw [show (719 / 3200 : ℝ) - Real.pi * Real.exp (359 / 400 : ℝ) =
      -(Real.pi * Real.exp (359 / 400 : ℝ) - (719 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (77174191113652633 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (77174191113652633 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell718_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (359 / 800 : ℝ) (719 / 1600 : ℝ)) :
    (106595137 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (216496279 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell718_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell718_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell719_leftExp :
    (76766579 / 31250000 : ℝ) ≤ Real.exp (719 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (719 / 800 : ℝ) (1028484065973 / 1000000000000 : ℝ)
    (76766579 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell719_rightExp :
    Real.exp (9 / 10 : ℝ) ≤ (3074503889 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 10 : ℝ) (1028524241917 / 1000000000000 : ℝ)
    (3074503889 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell719_denomUpper :
    Real.exp (9377980521155177 / 1250000000000000 : ℝ) ≤ (18123586852717 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9377980521155177 / 1250000000000000 : ℝ) (632106322279 /
    500000000000 : ℝ) (18123586852717 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell719_denomLower :
    (3588766521321 / 2000000000 : ℝ) ≤ Real.exp (29267252556721 / 3906250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29267252556721 / 3906250000000 : ℝ) (126381891303 /
    100000000000 : ℝ) (3588766521321 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell719_product_lower :
    (30146158806721 / 3906250000000 : ℝ) ≤ Real.pi * Real.exp (719 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell719_leftExp
    (by norm_num : (0 : ℝ) ≤ (76766579 / 31250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell719_product_upper :
    Real.pi * Real.exp (9 / 10 : ℝ) ≤ (9658839896155177 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell719_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell719_endpointLower :
    (33093887 / 156250000 : ℝ) ≤ hpThetaTraceEndpointLower (719 / 1600 : ℝ) (9 / 20 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (30146158806721 / 3906250000000 : ℝ) (Real.pi * Real.exp (719 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell719_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 10 : ℝ) - (719 / 3200 : ℝ)) ≤
      (18123586852717 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell719_denomUpper
    linarith [hpThetaJensenCell719_product_upper]
  have hi : (1 / (18123586852717 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 10 : ℝ) - (719 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18123586852717 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18123586852717 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((719 / 3200 : ℝ) - Real.pi * Real.exp (9 / 10 : ℝ)) := by
    rw [show (719 / 3200 : ℝ) - Real.pi * Real.exp (9 / 10 : ℝ) =
      -(Real.pi * Real.exp (9 / 10 : ℝ) - (719 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (719 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (719 / 800 : ℝ)) := by
    have h := hpThetaJensenCell719_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18123586852717 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell719_endpointUpper :
    hpThetaJensenKernelEndpointUpper (719 / 1600 : ℝ) (9 / 20 : ℝ) ≤ (430175659 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 10 : ℝ)) (9658839896155177 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 20 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell719_product_upper
  have hD : (3588766521321 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (719 / 800 : ℝ) - (9 / 40 : ℝ)) := by
    apply le_trans hpThetaJensenCell719_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell719_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (719 / 800 : ℝ) - (9 / 40 : ℝ)) ≤
      (1 / (3588766521321 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3588766521321 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 40 : ℝ) - Real.pi * Real.exp (719 / 800 : ℝ)) ≤
      (2 / (3588766521321 / 2000000000 : ℝ) : ℝ) := by
    rw [show (9 / 40 : ℝ) - Real.pi * Real.exp (719 / 800 : ℝ) =
      -(Real.pi * Real.exp (719 / 800 : ℝ) - (9 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9658839896155177 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (9658839896155177 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell719_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (719 / 1600 : ℝ) (9 / 20 : ℝ)) :
    (33093887 / 156250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (430175659 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell719_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell719_endpointUpper

def hpThetaJensenCellsBatch035Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2393075569 / 10000000000 : ℝ)
  | 1 => (95120421 / 400000000 : ℝ)
  | 2 => (29537641 / 125000000 : ℝ)
  | 3 => (469615551 / 2000000000 : ℝ)
  | 4 => (583302467 / 2500000000 : ℝ)
  | 5 => (2318407537 / 10000000000 : ℝ)
  | 6 => (2303670677 / 10000000000 : ℝ)
  | 7 => (2288999203 / 10000000000 : ℝ)
  | 8 => (568598257 / 2500000000 : ℝ)
  | 9 => (70620377 / 312500000 : ℝ)
  | 10 => (1122688111 / 5000000000 : ℝ)
  | 11 => (557741353 / 2500000000 : ℝ)
  | 12 => (2216619541 / 10000000000 : ℝ)
  | 13 => (550584629 / 2500000000 : ℝ)
  | 14 => (2188122243 / 10000000000 : ℝ)
  | 15 => (1086985313 / 5000000000 : ℝ)
  | 16 => (2159883569 / 10000000000 : ℝ)
  | 17 => (1072930487 / 5000000000 : ℝ)
  | 18 => (106595137 / 500000000 : ℝ)
  | 19 => (33093887 / 156250000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch035Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2429685199 / 10000000000 : ℝ)
  | 1 => (75450531 / 312500000 : ℝ)
  | 2 => (1199607643 / 5000000000 : ℝ)
  | 3 => (2384079999 / 10000000000 : ℝ)
  | 4 => (2369011051 / 10000000000 : ℝ)
  | 5 => (2354008359 / 10000000000 : ℝ)
  | 6 => (14619199 / 62500000 : ℝ)
  | 7 => (2324201409 / 10000000000 : ℝ)
  | 8 => (2309396979 / 10000000000 : ℝ)
  | 9 => (2294658463 / 10000000000 : ℝ)
  | 10 => (227998577 / 1000000000 : ℝ)
  | 11 => (2265378811 / 10000000000 : ℝ)
  | 12 => (450167499 / 2000000000 : ℝ)
  | 13 => (2183947 / 9765625 : ℝ)
  | 14 => (277743927 / 1250000000 : ℝ)
  | 15 => (34493851 / 156250000 : ℝ)
  | 16 => (1096663387 / 5000000000 : ℝ)
  | 17 => (2179112249 / 10000000000 : ℝ)
  | 18 => (216496279 / 1000000000 : ℝ)
  | 19 => (430175659 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch035_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch035Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch035Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell700_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell701_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell702_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell703_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell704_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell705_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell706_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell707_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell708_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell709_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell710_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell711_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell712_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell713_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell714_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell715_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell716_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell717_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell718_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell719_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper] at h ⊢
    exact h

end HodgeProofHP
