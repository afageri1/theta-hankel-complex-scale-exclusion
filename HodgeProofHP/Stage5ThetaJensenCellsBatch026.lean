import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell520_leftExp :
    (1915540829 / 1000000000 : ℝ) ≤ Real.exp (13 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 20 : ℝ) (204104040553 / 200000000000 : ℝ)
    (1915540829 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell520_rightExp :
    Real.exp (521 / 800 : ℝ) ≤ (19179367523 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (521 / 800 : ℝ) (204112013523 / 200000000000 : ℝ)
    (19179367523 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell520_denomUpper :
    Real.exp (58628766754684139 / 10000000000000000 : ℝ) ≤ (35173451613 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58628766754684139 / 10000000000000000 : ℝ) (600536243077
    / 500000000000 : ℝ) (35173451613 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell520_denomLower :
    (3489871995581 / 10000000000 : ℝ) ≤ Real.exp (731879405507471 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (731879405507471 / 125000000000000 : ℝ) (48031128229 /
    40000000000 : ℝ) (3489871995581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell520_product_lower :
    (752230968007471 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell520_leftExp
    (by norm_num : (0 : ℝ) ≤ (1915540829 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell520_product_upper :
    Real.pi * Real.exp (521 / 800 : ℝ) ≤ (60253766754684139 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell520_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell520_endpointLower :
    (247347643 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 40 : ℝ) (521 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (752230968007471 / 125000000000000 : ℝ) (Real.pi * Real.exp (13 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell520_product_lower
  have hD : Real.exp (Real.pi * Real.exp (521 / 800 : ℝ) - (13 / 80 : ℝ)) ≤
      (35173451613 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell520_denomUpper
    linarith [hpThetaJensenCell520_product_upper]
  have hi : (1 / (35173451613 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (521 / 800 : ℝ) - (13 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (35173451613 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (35173451613 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 80 : ℝ) - Real.pi * Real.exp (521 / 800 : ℝ)) := by
    rw [show (13 / 80 : ℝ) - Real.pi * Real.exp (521 / 800 : ℝ) =
      -(Real.pi * Real.exp (521 / 800 : ℝ) - (13 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 20 : ℝ)) := by
    have h := hpThetaJensenCell520_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (35173451613 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell520_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 40 : ℝ) (521 / 1600 : ℝ) ≤ (1253405639 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (521 / 800 : ℝ)) (60253766754684139 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (521 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell520_product_upper
  have hD : (3489871995581 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 20 : ℝ) - (521 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell520_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell520_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 20 : ℝ) - (521 / 3200 : ℝ)) ≤
      (1 / (3489871995581 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3489871995581 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((521 / 3200 : ℝ) - Real.pi * Real.exp (13 / 20 : ℝ)) ≤
      (2 / (3489871995581 / 10000000000 : ℝ) : ℝ) := by
    rw [show (521 / 3200 : ℝ) - Real.pi * Real.exp (13 / 20 : ℝ) =
      -(Real.pi * Real.exp (13 / 20 : ℝ) - (521 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (60253766754684139 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (60253766754684139 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell520_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 40 : ℝ) (521 / 1600 : ℝ)) :
    (247347643 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1253405639 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell520_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell520_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell521_leftExp :
    (19179367521 / 10000000000 : ℝ) ≤ Real.exp (521 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (521 / 800 : ℝ) (510280033807 / 500000000000 : ℝ)
    (19179367521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell521_rightExp :
    Real.exp (261 / 400 : ℝ) ≤ (9601678361 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (261 / 400 : ℝ) (1020599934021 / 1000000000000 : ℝ)
    (9601678361 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell521_denomUpper :
    Real.exp (29350503027169073 / 5000000000000000 : ℝ) ≤ (354284621433 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29350503027169073 / 5000000000000000 : ℝ) (240268731249
    / 200000000000 : ℝ) (354284621433 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell521_denomLower :
    (703028152657 / 2000000000 : ℝ) ≤ Real.exp (7327812196129179 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7327812196129179 / 1250000000000000 : ℝ) (600524477963 /
    500000000000 : ℝ) (703028152657 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell521_product_lower :
    (7531718446129179 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (521 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell521_leftExp
    (by norm_num : (0 : ℝ) ≤ (19179367521 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell521_product_upper :
    Real.pi * Real.exp (261 / 400 : ℝ) ≤ (30164565527169073 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell521_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell521_endpointLower :
    (1539275327 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (521 / 1600 : ℝ) (261 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7531718446129179 / 1250000000000000 : ℝ) (Real.pi * Real.exp (521 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell521_product_lower
  have hD : Real.exp (Real.pi * Real.exp (261 / 400 : ℝ) - (521 / 3200 : ℝ)) ≤
      (354284621433 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell521_denomUpper
    linarith [hpThetaJensenCell521_product_upper]
  have hi : (1 / (354284621433 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (261 / 400 : ℝ) - (521 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (354284621433 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (354284621433 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((521 / 3200 : ℝ) - Real.pi * Real.exp (261 / 400 : ℝ)) := by
    rw [show (521 / 3200 : ℝ) - Real.pi * Real.exp (261 / 400 : ℝ) =
      -(Real.pi * Real.exp (261 / 400 : ℝ) - (521 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (521 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (521 / 800 : ℝ)) := by
    have h := hpThetaJensenCell521_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (354284621433 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell521_endpointUpper :
    hpThetaJensenKernelEndpointUpper (521 / 1600 : ℝ) (261 / 800 : ℝ) ≤ (6240134539 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (261 / 400 : ℝ)) (30164565527169073 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (261 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell521_product_upper
  have hD : (703028152657 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (521 / 800 : ℝ) - (261 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell521_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell521_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (521 / 800 : ℝ) - (261 / 1600 : ℝ)) ≤
      (1 / (703028152657 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (703028152657 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((261 / 1600 : ℝ) - Real.pi * Real.exp (521 / 800 : ℝ)) ≤
      (2 / (703028152657 / 2000000000 : ℝ) : ℝ) := by
    rw [show (261 / 1600 : ℝ) - Real.pi * Real.exp (521 / 800 : ℝ) =
      -(Real.pi * Real.exp (521 / 800 : ℝ) - (261 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30164565527169073 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (30164565527169073 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell521_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (521 / 1600 : ℝ) (261 / 800 : ℝ)) :
    (1539275327 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6240134539 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell521_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell521_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell522_leftExp :
    (19203356721 / 10000000000 : ℝ) ≤ Real.exp (261 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (261 / 400 : ℝ) (51029996701 / 50000000000 : ℝ)
    (19203356721 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell522_rightExp :
    Real.exp (523 / 800 : ℝ) ≤ (19227375927 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (523 / 800 : ℝ) (204127960397 / 200000000000 : ℝ)
    (19227375927 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell522_denomUpper :
    Real.exp (58773339620631711 / 10000000000000000 : ℝ) ≤ (713713158363 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58773339620631711 / 10000000000000000 : ℝ) (18775238149
    / 15625000000 : ℝ) (713713158363 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell522_denomLower :
    (3540625826931 / 10000000000 : ℝ) ≤ Real.exp (7336842105979979 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7336842105979979 / 1250000000000000 : ℝ) (1201320120627
    / 1000000000000 : ℝ) (3540625826931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell522_product_lower :
    (7541138980979979 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (261 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell522_leftExp
    (by norm_num : (0 : ℝ) ≤ (19203356721 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell522_product_upper :
    Real.pi * Real.exp (523 / 800 : ℝ) ≤ (60404589620631711 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell522_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell522_endpointLower :
    (3065281929 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (261 / 800 : ℝ) (523 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7541138980979979 / 1250000000000000 : ℝ) (Real.pi * Real.exp (261 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell522_product_lower
  have hD : Real.exp (Real.pi * Real.exp (523 / 800 : ℝ) - (261 / 1600 : ℝ)) ≤
      (713713158363 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell522_denomUpper
    linarith [hpThetaJensenCell522_product_upper]
  have hi : (1 / (713713158363 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (523 / 800 : ℝ) - (261 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (713713158363 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (713713158363 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((261 / 1600 : ℝ) - Real.pi * Real.exp (523 / 800 : ℝ)) := by
    rw [show (261 / 1600 : ℝ) - Real.pi * Real.exp (523 / 800 : ℝ) =
      -(Real.pi * Real.exp (523 / 800 : ℝ) - (261 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (261 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (261 / 400 : ℝ)) := by
    have h := hpThetaJensenCell522_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (713713158363 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell522_endpointUpper :
    hpThetaJensenKernelEndpointUpper (261 / 800 : ℝ) (523 / 1600 : ℝ) ≤ (3106646759 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (523 / 800 : ℝ)) (60404589620631711 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (523 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell522_product_upper
  have hD : (3540625826931 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (261 / 400 : ℝ) - (523 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell522_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell522_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (261 / 400 : ℝ) - (523 / 3200 : ℝ)) ≤
      (1 / (3540625826931 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3540625826931 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((523 / 3200 : ℝ) - Real.pi * Real.exp (261 / 400 : ℝ)) ≤
      (2 / (3540625826931 / 10000000000 : ℝ) : ℝ) := by
    rw [show (523 / 3200 : ℝ) - Real.pi * Real.exp (261 / 400 : ℝ) =
      -(Real.pi * Real.exp (261 / 400 : ℝ) - (523 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (60404589620631711 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (60404589620631711 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell522_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (261 / 800 : ℝ) (523 / 1600 : ℝ)) :
    (3065281929 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3106646759 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell522_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell522_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell523_leftExp :
    (9613687963 / 5000000000 : ℝ) ≤ Real.exp (523 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (523 / 800 : ℝ) (7973748453 / 7812500000 : ℝ) (9613687963
    / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell523_rightExp :
    Real.exp (131 / 200 : ℝ) ≤ (770057007 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (131 / 200 : ℝ) (510339835753 / 500000000000 : ℝ)
    (770057007 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell523_denomUpper :
    Real.exp (2353830702792151 / 400000000000000 : ℝ) ≤ (1797253004229 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2353830702792151 / 400000000000000 : ℝ) (300471810679 /
    250000000000 : ℝ) (1797253004229 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell523_denomLower :
    (1783164638377 / 5000000000 : ℝ) ≤ Real.exp (3672941899382137 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3672941899382137 / 625000000000000 : ℝ) (1201591700507 /
    1000000000000 : ℝ) (1783164638377 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell523_product_lower :
    (3775285649382137 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (523 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell523_leftExp
    (by norm_num : (0 : ℝ) ≤ (9613687963 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell523_product_upper :
    Real.pi * Real.exp (131 / 200 : ℝ) ≤ (2419205702792151 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell523_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell523_endpointLower :
    (6104078973 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (523 / 1600 : ℝ) (131 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3775285649382137 / 625000000000000 : ℝ) (Real.pi * Real.exp (523 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell523_product_lower
  have hD : Real.exp (Real.pi * Real.exp (131 / 200 : ℝ) - (523 / 3200 : ℝ)) ≤
      (1797253004229 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell523_denomUpper
    linarith [hpThetaJensenCell523_product_upper]
  have hi : (1 / (1797253004229 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (131 / 200 : ℝ) - (523 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1797253004229 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1797253004229 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((523 / 3200 : ℝ) - Real.pi * Real.exp (131 / 200 : ℝ)) := by
    rw [show (523 / 3200 : ℝ) - Real.pi * Real.exp (131 / 200 : ℝ) =
      -(Real.pi * Real.exp (131 / 200 : ℝ) - (523 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (523 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (523 / 800 : ℝ)) := by
    have h := hpThetaJensenCell523_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1797253004229 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell523_endpointUpper :
    hpThetaJensenKernelEndpointUpper (523 / 1600 : ℝ) (131 / 400 : ℝ) ≤ (773313173 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (131 / 200 : ℝ)) (2419205702792151 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (131 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell523_product_upper
  have hD : (1783164638377 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (523 / 800 : ℝ) - (131 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell523_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell523_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (523 / 800 : ℝ) - (131 / 800 : ℝ)) ≤
      (1 / (1783164638377 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1783164638377 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((131 / 800 : ℝ) - Real.pi * Real.exp (523 / 800 : ℝ)) ≤
      (2 / (1783164638377 / 5000000000 : ℝ) : ℝ) := by
    rw [show (131 / 800 : ℝ) - Real.pi * Real.exp (523 / 800 : ℝ) =
      -(Real.pi * Real.exp (523 / 800 : ℝ) - (131 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2419205702792151 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2419205702792151 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell523_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (523 / 1600 : ℝ) (131 / 400 : ℝ)) :
    (6104078973 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (773313173 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell523_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell523_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell524_leftExp :
    (19251425173 / 10000000000 : ℝ) ≤ Real.exp (131 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (131 / 200 : ℝ) (204135934301 / 200000000000 : ℝ)
    (19251425173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell524_rightExp :
    Real.exp (21 / 32 : ℝ) ≤ (9637752251 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 32 : ℝ) (127589942823 / 125000000000 : ℝ)
    (9637752251 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell524_denomUpper :
    Real.exp (29459145007475843 / 5000000000000000 : ℝ) ≤ (14143238283 / 39062500 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29459145007475843 / 5000000000000000 : ℝ) (75134978779 /
    62500000000 : ℝ) (14143238283 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell524_denomLower :
    (449031653263 / 1250000000 : ℝ) ≤ Real.exp (7354937289011927 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7354937289011927 / 1250000000000000 : ℝ) (240372739251 /
    200000000000 : ℝ) (449031653263 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell524_product_lower :
    (7560015414011927 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (131 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell524_leftExp
    (by norm_num : (0 : ℝ) ≤ (19251425173 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell524_product_upper :
    Real.pi * Real.exp (21 / 32 : ℝ) ≤ (30277895007475843 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell524_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell524_endpointLower :
    (60776469 / 100000000 : ℝ) ≤ hpThetaTraceEndpointLower (131 / 400 : ℝ) (21 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7560015414011927 / 1250000000000000 : ℝ) (Real.pi * Real.exp (131 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell524_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 32 : ℝ) - (131 / 800 : ℝ)) ≤
      (14143238283 / 39062500 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell524_denomUpper
    linarith [hpThetaJensenCell524_product_upper]
  have hi : (1 / (14143238283 / 39062500 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 32 : ℝ) - (131 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14143238283 / 39062500 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14143238283 / 39062500 : ℝ) : ℝ) ≤
      2 * Real.exp ((131 / 800 : ℝ) - Real.pi * Real.exp (21 / 32 : ℝ)) := by
    rw [show (131 / 800 : ℝ) - Real.pi * Real.exp (21 / 32 : ℝ) =
      -(Real.pi * Real.exp (21 / 32 : ℝ) - (131 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (131 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (131 / 200 : ℝ)) := by
    have h := hpThetaJensenCell524_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14143238283 / 39062500 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell524_endpointUpper :
    hpThetaJensenKernelEndpointUpper (131 / 400 : ℝ) (21 / 64 : ℝ) ≤ (1539942597 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 32 : ℝ)) (30277895007475843 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell524_product_upper
  have hD : (449031653263 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (131 / 200 : ℝ) - (21 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell524_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell524_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (131 / 200 : ℝ) - (21 / 128 : ℝ)) ≤
      (1 / (449031653263 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (449031653263 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 128 : ℝ) - Real.pi * Real.exp (131 / 200 : ℝ)) ≤
      (2 / (449031653263 / 1250000000 : ℝ) : ℝ) := by
    rw [show (21 / 128 : ℝ) - Real.pi * Real.exp (131 / 200 : ℝ) =
      -(Real.pi * Real.exp (131 / 200 : ℝ) - (21 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30277895007475843 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (30277895007475843 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell524_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (131 / 400 : ℝ) (21 / 64 : ℝ)) :
    (60776469 / 100000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1539942597 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell524_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell524_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell525_leftExp :
    (19275504501 / 10000000000 : ℝ) ≤ Real.exp (21 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 32 : ℝ) (1020719542583 / 1000000000000 : ℝ)
    (19275504501 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell525_rightExp :
    Real.exp (263 / 400 : ℝ) ≤ (4824903487 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (263 / 400 : ℝ) (51037970761 / 50000000000 : ℝ)
    (4824903487 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell525_denomUpper :
    Real.exp (14747726770434791 / 2500000000000000 : ℝ) ≤ (1823528465757 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14747726770434791 / 2500000000000000 : ℝ) (1202432495509
    / 1000000000000 : ℝ) (1823528465757 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell525_denomLower :
    (3618399813467 / 10000000000 : ℝ) ≤ Real.exp (7364002592038199 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7364002592038199 / 1250000000000000 : ℝ) (300534027147 /
    250000000000 : ℝ) (3618399813467 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell525_product_lower :
    (7569471342038199 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell525_leftExp
    (by norm_num : (0 : ℝ) ≤ (19275504501 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell525_product_upper :
    Real.pi * Real.exp (263 / 400 : ℝ) ≤ (15157883020434791 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell525_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell525_endpointLower :
    (151281697 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 64 : ℝ) (263 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7569471342038199 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell525_product_lower
  have hD : Real.exp (Real.pi * Real.exp (263 / 400 : ℝ) - (21 / 128 : ℝ)) ≤
      (1823528465757 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell525_denomUpper
    linarith [hpThetaJensenCell525_product_upper]
  have hi : (1 / (1823528465757 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (263 / 400 : ℝ) - (21 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1823528465757 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1823528465757 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 128 : ℝ) - Real.pi * Real.exp (263 / 400 : ℝ)) := by
    rw [show (21 / 128 : ℝ) - Real.pi * Real.exp (263 / 400 : ℝ) =
      -(Real.pi * Real.exp (263 / 400 : ℝ) - (21 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 32 : ℝ)) := by
    have h := hpThetaJensenCell525_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1823528465757 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell525_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 64 : ℝ) (263 / 800 : ℝ) ≤ (3066544387 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (263 / 400 : ℝ)) (15157883020434791 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (263 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell525_product_upper
  have hD : (3618399813467 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 32 : ℝ) - (263 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell525_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell525_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 32 : ℝ) - (263 / 1600 : ℝ)) ≤
      (1 / (3618399813467 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3618399813467 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((263 / 1600 : ℝ) - Real.pi * Real.exp (21 / 32 : ℝ)) ≤
      (2 / (3618399813467 / 10000000000 : ℝ) : ℝ) := by
    rw [show (263 / 1600 : ℝ) - Real.pi * Real.exp (21 / 32 : ℝ) =
      -(Real.pi * Real.exp (21 / 32 : ℝ) - (263 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15157883020434791 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (15157883020434791 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell525_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 64 : ℝ) (263 / 800 : ℝ)) :
    (151281697 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3066544387 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell525_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell525_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell526_leftExp :
    (19299613947 / 10000000000 : ℝ) ≤ Real.exp (263 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (263 / 400 : ℝ) (1020759415219 / 1000000000000 : ℝ)
    (19299613947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell526_rightExp :
    Real.exp (527 / 800 : ℝ) ≤ (386475071 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (527 / 800 : ℝ) (1020799289413 / 1000000000000 : ℝ)
    (386475071 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell526_denomUpper :
    Real.exp (1181272377728103 / 200000000000000 : ℝ) ≤ (229604499047 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1181272377728103 / 200000000000000 : ℝ) (601352874271 /
    500000000000 : ℝ) (229604499047 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell526_denomLower :
    (182238559879 / 500000000 : ℝ) ≤ Real.exp (7373079722372953 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7373079722372953 / 1250000000000000 : ℝ) (1202408938197
    / 1000000000000 : ℝ) (182238559879 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell526_product_lower :
    (7578939097372953 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (263 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell526_leftExp
    (by norm_num : (0 : ℝ) ≤ (19299613947 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell526_product_upper :
    Real.pi * Real.exp (527 / 800 : ℝ) ≤ (1214147377728103 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell526_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell526_endpointLower :
    (3012471077 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (263 / 800 : ℝ) (527 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7578939097372953 / 1250000000000000 : ℝ) (Real.pi * Real.exp (263 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell526_product_lower
  have hD : Real.exp (Real.pi * Real.exp (527 / 800 : ℝ) - (263 / 1600 : ℝ)) ≤
      (229604499047 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell526_denomUpper
    linarith [hpThetaJensenCell526_product_upper]
  have hi : (1 / (229604499047 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (527 / 800 : ℝ) - (263 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (229604499047 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (229604499047 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((263 / 1600 : ℝ) - Real.pi * Real.exp (527 / 800 : ℝ)) := by
    rw [show (263 / 1600 : ℝ) - Real.pi * Real.exp (527 / 800 : ℝ) =
      -(Real.pi * Real.exp (527 / 800 : ℝ) - (263 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (263 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (263 / 400 : ℝ)) := by
    have h := hpThetaJensenCell526_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (229604499047 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell526_endpointUpper :
    hpThetaJensenKernelEndpointUpper (263 / 800 : ℝ) (527 / 1600 : ℝ) ≤ (6106460787 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (527 / 800 : ℝ)) (1214147377728103 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (527 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell526_product_upper
  have hD : (182238559879 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (263 / 400 : ℝ) - (527 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell526_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell526_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (263 / 400 : ℝ) - (527 / 3200 : ℝ)) ≤
      (1 / (182238559879 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (182238559879 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((527 / 3200 : ℝ) - Real.pi * Real.exp (263 / 400 : ℝ)) ≤
      (2 / (182238559879 / 500000000 : ℝ) : ℝ) := by
    rw [show (527 / 3200 : ℝ) - Real.pi * Real.exp (263 / 400 : ℝ) =
      -(Real.pi * Real.exp (263 / 400 : ℝ) - (527 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1214147377728103 / 200000000000000 : ℝ) ^ 2 - 6 *
      (1214147377728103 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell526_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (263 / 800 : ℝ) (527 / 1600 : ℝ)) :
    (3012471077 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6106460787 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell526_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell526_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell527_leftExp :
    (4830938387 / 2500000000 : ℝ) ≤ Real.exp (527 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (527 / 800 : ℝ) (255199822353 / 250000000000 : ℝ)
    (4830938387 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell527_rightExp :
    Real.exp (33 / 50 : ℝ) ≤ (3869584669 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 50 : ℝ) (255209791291 / 250000000000 : ℝ)
    (3869584669 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell527_denomUpper :
    Real.exp (11827285109037717 / 2000000000000000 : ℝ) ≤ (925129091723 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11827285109037717 / 2000000000000000 : ℝ) (601489710129
    / 500000000000 : ℝ) (925129091723 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell527_denomLower :
    (1835684780121 / 5000000000 : ℝ) ≤ Real.exp (1845542173636513 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1845542173636513 / 312500000000000 : ℝ) (601341092887 /
    500000000000 : ℝ) (1835684780121 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell527_product_lower :
    (1897104673636513 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (527 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell527_leftExp
    (by norm_num : (0 : ℝ) ≤ (4830938387 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell527_product_upper :
    Real.pi * Real.exp (33 / 50 : ℝ) ≤ (12156660109037717 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell527_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell527_endpointLower :
    (2999334981 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (527 / 1600 : ℝ) (33 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1897104673636513 / 312500000000000 : ℝ) (Real.pi * Real.exp (527 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell527_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 50 : ℝ) - (527 / 3200 : ℝ)) ≤
      (925129091723 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell527_denomUpper
    linarith [hpThetaJensenCell527_product_upper]
  have hi : (1 / (925129091723 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 50 : ℝ) - (527 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (925129091723 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (925129091723 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((527 / 3200 : ℝ) - Real.pi * Real.exp (33 / 50 : ℝ)) := by
    rw [show (527 / 3200 : ℝ) - Real.pi * Real.exp (33 / 50 : ℝ) =
      -(Real.pi * Real.exp (33 / 50 : ℝ) - (527 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (527 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (527 / 800 : ℝ)) := by
    have h := hpThetaJensenCell527_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (925129091723 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell527_endpointUpper :
    hpThetaJensenKernelEndpointUpper (527 / 1600 : ℝ) (33 / 100 : ℝ) ≤ (6079886673 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 50 : ℝ)) (12156660109037717 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell527_product_upper
  have hD : (1835684780121 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (527 / 800 : ℝ) - (33 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell527_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell527_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (527 / 800 : ℝ) - (33 / 200 : ℝ)) ≤
      (1 / (1835684780121 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1835684780121 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 200 : ℝ) - Real.pi * Real.exp (527 / 800 : ℝ)) ≤
      (2 / (1835684780121 / 5000000000 : ℝ) : ℝ) := by
    rw [show (33 / 200 : ℝ) - Real.pi * Real.exp (527 / 800 : ℝ) =
      -(Real.pi * Real.exp (527 / 800 : ℝ) - (33 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12156660109037717 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (12156660109037717 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell527_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (527 / 1600 : ℝ) (33 / 100 : ℝ)) :
    (2999334981 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6079886673 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell527_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell527_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell528_leftExp :
    (19347923343 / 10000000000 : ℝ) ≤ Real.exp (33 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 50 : ℝ) (1020839165163 / 1000000000000 : ℝ)
    (19347923343 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell528_rightExp :
    Real.exp (529 / 800 : ℝ) ≤ (19372123371 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (529 / 800 : ℝ) (1020879042473 / 1000000000000 : ℝ)
    (19372123371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell528_denomUpper :
    Real.exp (59209327177470003 / 10000000000000000 : ℝ) ≤ (29121814917 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59209327177470003 / 10000000000000000 : ℝ) (300813377841
    / 250000000000 : ℝ) (29121814917 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell528_denomLower :
    (231137319321 / 625000000 : ℝ) ≤ Real.exp (7391269523872757 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7391269523872757 / 1250000000000000 : ℝ) (601477926019 /
    500000000000 : ℝ) (231137319321 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell528_product_lower :
    (7597910148872757 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell528_leftExp
    (by norm_num : (0 : ℝ) ≤ (19347923343 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell528_product_upper :
    Real.pi * Real.exp (529 / 800 : ℝ) ≤ (60859327177470003 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell528_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell528_endpointLower :
    (5972451541 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 100 : ℝ) (529 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7597910148872757 / 1250000000000000 : ℝ) (Real.pi * Real.exp (33 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell528_product_lower
  have hD : Real.exp (Real.pi * Real.exp (529 / 800 : ℝ) - (33 / 200 : ℝ)) ≤
      (29121814917 / 78125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell528_denomUpper
    linarith [hpThetaJensenCell528_product_upper]
  have hi : (1 / (29121814917 / 78125000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (529 / 800 : ℝ) - (33 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29121814917 / 78125000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29121814917 / 78125000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 200 : ℝ) - Real.pi * Real.exp (529 / 800 : ℝ)) := by
    rw [show (33 / 200 : ℝ) - Real.pi * Real.exp (529 / 800 : ℝ) =
      -(Real.pi * Real.exp (529 / 800 : ℝ) - (33 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 50 : ℝ)) := by
    have h := hpThetaJensenCell528_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29121814917 / 78125000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell528_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 100 : ℝ) (529 / 1600 : ℝ) ≤ (1513341667 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (529 / 800 : ℝ)) (60859327177470003 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (529 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell528_product_upper
  have hD : (231137319321 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 50 : ℝ) - (529 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell528_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell528_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 50 : ℝ) - (529 / 3200 : ℝ)) ≤
      (1 / (231137319321 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (231137319321 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((529 / 3200 : ℝ) - Real.pi * Real.exp (33 / 50 : ℝ)) ≤
      (2 / (231137319321 / 625000000 : ℝ) : ℝ) := by
    rw [show (529 / 3200 : ℝ) - Real.pi * Real.exp (33 / 50 : ℝ) =
      -(Real.pi * Real.exp (33 / 50 : ℝ) - (529 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (60859327177470003 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (60859327177470003 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell528_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 100 : ℝ) (529 / 1600 : ℝ)) :
    (5972451541 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1513341667 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell528_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell528_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell529_leftExp :
    (19372123369 / 10000000000 : ℝ) ≤ Real.exp (529 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (529 / 800 : ℝ) (127609880309 / 125000000000 : ℝ)
    (19372123369 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell529_rightExp :
    Real.exp (53 / 80 : ℝ) ≤ (9698176833 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 80 : ℝ) (51045946067 / 50000000000 : ℝ)
    (9698176833 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell529_denomUpper :
    Real.exp (29641161951314969 / 5000000000000000 : ℝ) ≤ (469362758421 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29641161951314969 / 5000000000000000 : ℝ) (601764011283
    / 500000000000 : ℝ) (469362758421 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell529_denomLower :
    (3725256073043 / 10000000000 : ℝ) ≤ Real.exp (7400382224882931 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7400382224882931 / 1250000000000000 : ℝ) (1203229937683
    / 1000000000000 : ℝ) (3725256073043 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell529_product_lower :
    (7607413474882931 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (529 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell529_leftExp
    (by norm_num : (0 : ℝ) ≤ (19372123369 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell529_product_upper :
    Real.pi * Real.exp (53 / 80 : ℝ) ≤ (30467724451314969 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell529_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell529_endpointLower :
    (743285891 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (529 / 1600 : ℝ) (53 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7607413474882931 / 1250000000000000 : ℝ) (Real.pi * Real.exp (529 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell529_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 80 : ℝ) - (529 / 3200 : ℝ)) ≤
      (469362758421 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell529_denomUpper
    linarith [hpThetaJensenCell529_product_upper]
  have hi : (1 / (469362758421 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 80 : ℝ) - (529 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (469362758421 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (469362758421 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((529 / 3200 : ℝ) - Real.pi * Real.exp (53 / 80 : ℝ)) := by
    rw [show (529 / 3200 : ℝ) - Real.pi * Real.exp (53 / 80 : ℝ) =
      -(Real.pi * Real.exp (53 / 80 : ℝ) - (529 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (529 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (529 / 800 : ℝ)) := by
    have h := hpThetaJensenCell529_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (469362758421 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell529_endpointUpper :
    hpThetaJensenKernelEndpointUpper (529 / 1600 : ℝ) (53 / 160 : ℝ) ≤ (1205380203 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 80 : ℝ)) (30467724451314969 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell529_product_upper
  have hD : (3725256073043 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (529 / 800 : ℝ) - (53 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell529_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell529_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (529 / 800 : ℝ) - (53 / 320 : ℝ)) ≤
      (1 / (3725256073043 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3725256073043 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 320 : ℝ) - Real.pi * Real.exp (529 / 800 : ℝ)) ≤
      (2 / (3725256073043 / 10000000000 : ℝ) : ℝ) := by
    rw [show (53 / 320 : ℝ) - Real.pi * Real.exp (529 / 800 : ℝ) =
      -(Real.pi * Real.exp (529 / 800 : ℝ) - (53 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30467724451314969 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (30467724451314969 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell529_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (529 / 1600 : ℝ) (53 / 160 : ℝ)) :
    (743285891 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1205380203 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell529_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell529_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell530_leftExp :
    (3879270733 / 2000000000 : ℝ) ≤ Real.exp (53 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 80 : ℝ) (1020918921339 / 1000000000000 : ℝ)
    (3879270733 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell530_rightExp :
    Real.exp (531 / 800 : ℝ) ≤ (4855153567 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (531 / 800 : ℝ) (255239700441 / 250000000000 : ℝ)
    (4855153567 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell530_denomUpper :
    Real.exp (14838853960012231 / 2500000000000000 : ℝ) ≤ (236402995027 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14838853960012231 / 2500000000000000 : ℝ) (1203802954573
    / 1000000000000 : ℝ) (236402995027 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell530_denomLower :
    (3752548707009 / 10000000000 : ℝ) ≤ Real.exp (1481901362578367 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1481901362578367 / 250000000000000 : ℝ) (300876110857 /
    250000000000 : ℝ) (3752548707009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell530_product_lower :
    (1523385737578367 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell530_leftExp
    (by norm_num : (0 : ℝ) ≤ (3879270733 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell530_product_upper :
    Real.pi * Real.exp (531 / 800 : ℝ) ≤ (15252916460012231 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell530_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell530_endpointLower :
    (2960088477 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 160 : ℝ) (531 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1523385737578367 / 250000000000000 : ℝ) (Real.pi * Real.exp (53 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell530_product_lower
  have hD : Real.exp (Real.pi * Real.exp (531 / 800 : ℝ) - (53 / 320 : ℝ)) ≤
      (236402995027 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell530_denomUpper
    linarith [hpThetaJensenCell530_product_upper]
  have hi : (1 / (236402995027 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (531 / 800 : ℝ) - (53 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (236402995027 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (236402995027 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 320 : ℝ) - Real.pi * Real.exp (531 / 800 : ℝ)) := by
    rw [show (53 / 320 : ℝ) - Real.pi * Real.exp (531 / 800 : ℝ) =
      -(Real.pi * Real.exp (531 / 800 : ℝ) - (53 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 80 : ℝ)) := by
    have h := hpThetaJensenCell530_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (236402995027 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell530_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 160 : ℝ) (531 / 1600 : ℝ) ≤ (3000244973 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (531 / 800 : ℝ)) (15252916460012231 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (531 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell530_product_upper
  have hD : (3752548707009 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 80 : ℝ) - (531 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell530_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell530_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 80 : ℝ) - (531 / 3200 : ℝ)) ≤
      (1 / (3752548707009 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3752548707009 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((531 / 3200 : ℝ) - Real.pi * Real.exp (53 / 80 : ℝ)) ≤
      (2 / (3752548707009 / 10000000000 : ℝ) : ℝ) := by
    rw [show (531 / 3200 : ℝ) - Real.pi * Real.exp (53 / 80 : ℝ) =
      -(Real.pi * Real.exp (53 / 80 : ℝ) - (531 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (15252916460012231 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (15252916460012231 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell530_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 160 : ℝ) (531 / 1600 : ℝ)) :
    (2960088477 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3000244973 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell530_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell530_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell531_leftExp :
    (9710307133 / 5000000000 : ℝ) ≤ Real.exp (531 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (531 / 800 : ℝ) (1020958801763 / 1000000000000 : ℝ)
    (9710307133 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell531_rightExp :
    Real.exp (133 / 200 : ℝ) ≤ (9722452607 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (133 / 200 : ℝ) (510499341873 / 500000000000 : ℝ)
    (9722452607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell531_denomUpper :
    Real.exp (29714301552982951 / 5000000000000000 : ℝ) ≤ (3810232171299 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29714301552982951 / 5000000000000000 : ℝ) (602039154041
    / 500000000000 : ℝ) (3810232171299 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell531_denomLower :
    (1890038642739 / 5000000000 : ℝ) ≤ Real.exp (3709321650821967 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3709321650821967 / 625000000000000 : ℝ) (240755873989 /
    200000000000 : ℝ) (1890038642739 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell531_product_lower :
    (3813227900821967 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (531 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell531_leftExp
    (by norm_num : (0 : ℝ) ≤ (9710307133 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell531_product_upper :
    Real.pi * Real.exp (133 / 200 : ℝ) ≤ (30543989052982951 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell531_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell531_endpointLower :
    (5894121251 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (531 / 1600 : ℝ) (133 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3813227900821967 / 625000000000000 : ℝ) (Real.pi * Real.exp (531 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell531_product_lower
  have hD : Real.exp (Real.pi * Real.exp (133 / 200 : ℝ) - (531 / 3200 : ℝ)) ≤
      (3810232171299 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell531_denomUpper
    linarith [hpThetaJensenCell531_product_upper]
  have hi : (1 / (3810232171299 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (133 / 200 : ℝ) - (531 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3810232171299 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3810232171299 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((531 / 3200 : ℝ) - Real.pi * Real.exp (133 / 200 : ℝ)) := by
    rw [show (531 / 3200 : ℝ) - Real.pi * Real.exp (133 / 200 : ℝ) =
      -(Real.pi * Real.exp (133 / 200 : ℝ) - (531 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (531 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (531 / 800 : ℝ)) := by
    have h := hpThetaJensenCell531_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3810232171299 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell531_endpointUpper :
    hpThetaJensenKernelEndpointUpper (531 / 1600 : ℝ) (133 / 400 : ℝ) ≤ (5974133703 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (133 / 200 : ℝ)) (30543989052982951 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (133 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell531_product_upper
  have hD : (1890038642739 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (531 / 800 : ℝ) - (133 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell531_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell531_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (531 / 800 : ℝ) - (133 / 800 : ℝ)) ≤
      (1 / (1890038642739 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1890038642739 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((133 / 800 : ℝ) - Real.pi * Real.exp (531 / 800 : ℝ)) ≤
      (2 / (1890038642739 / 5000000000 : ℝ) : ℝ) := by
    rw [show (133 / 800 : ℝ) - Real.pi * Real.exp (531 / 800 : ℝ) =
      -(Real.pi * Real.exp (531 / 800 : ℝ) - (133 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30543989052982951 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (30543989052982951 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell531_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (531 / 1600 : ℝ) (133 / 400 : ℝ)) :
    (5894121251 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5974133703 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell531_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell531_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell532_leftExp :
    (19444905213 / 10000000000 : ℝ) ≤ Real.exp (133 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (133 / 200 : ℝ) (204199736749 / 200000000000 : ℝ)
    (19444905213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell532_rightExp :
    Real.exp (533 / 800 : ℝ) ≤ (19469226543 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (533 / 800 : ℝ) (510519283643 / 500000000000 : ℝ)
    (19469226543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell532_denomUpper :
    Real.exp (59501885822902999 / 10000000000000000 : ℝ) ≤ (3838257149777 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59501885822902999 / 10000000000000000 : ℝ) (602177041907
    / 500000000000 : ℝ) (3838257149777 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell532_denomLower :
    (190392205727 / 500000000 : ℝ) ≤ Real.exp (7427791707239887 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7427791707239887 / 1250000000000000 : ℝ) (1204054717979
    / 1000000000000 : ℝ) (190392205727 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell532_product_lower :
    (7635994832239887 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (133 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell532_leftExp
    (by norm_num : (0 : ℝ) ≤ (19444905213 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell532_product_upper :
    Real.pi * Real.exp (533 / 800 : ℝ) ≤ (61164385822902999 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell532_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell532_endpointLower :
    (5868120249 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (133 / 400 : ℝ) (533 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7635994832239887 / 1250000000000000 : ℝ) (Real.pi * Real.exp (133 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell532_product_lower
  have hD : Real.exp (Real.pi * Real.exp (533 / 800 : ℝ) - (133 / 800 : ℝ)) ≤
      (3838257149777 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell532_denomUpper
    linarith [hpThetaJensenCell532_product_upper]
  have hi : (1 / (3838257149777 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (533 / 800 : ℝ) - (133 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3838257149777 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3838257149777 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((133 / 800 : ℝ) - Real.pi * Real.exp (533 / 800 : ℝ)) := by
    rw [show (133 / 800 : ℝ) - Real.pi * Real.exp (533 / 800 : ℝ) =
      -(Real.pi * Real.exp (533 / 800 : ℝ) - (133 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (133 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (133 / 200 : ℝ)) := by
    have h := hpThetaJensenCell532_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3838257149777 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell532_endpointUpper :
    hpThetaJensenKernelEndpointUpper (133 / 400 : ℝ) (533 / 1600 : ℝ) ≤ (2973916257 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (533 / 800 : ℝ)) (61164385822902999 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (533 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell532_product_upper
  have hD : (190392205727 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (133 / 200 : ℝ) - (533 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell532_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell532_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (133 / 200 : ℝ) - (533 / 3200 : ℝ)) ≤
      (1 / (190392205727 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (190392205727 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((533 / 3200 : ℝ) - Real.pi * Real.exp (133 / 200 : ℝ)) ≤
      (2 / (190392205727 / 500000000 : ℝ) : ℝ) := by
    rw [show (533 / 3200 : ℝ) - Real.pi * Real.exp (133 / 200 : ℝ) =
      -(Real.pi * Real.exp (133 / 200 : ℝ) - (533 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61164385822902999 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (61164385822902999 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell532_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (133 / 400 : ℝ) (533 / 1600 : ℝ)) :
    (5868120249 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2973916257 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell532_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell532_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell533_leftExp :
    (9734613271 / 5000000000 : ℝ) ≤ Real.exp (533 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (533 / 800 : ℝ) (204207713457 / 200000000000 : ℝ)
    (9734613271 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell533_rightExp :
    Real.exp (267 / 400 : ℝ) ≤ (19493578293 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (267 / 400 : ℝ) (31908701637 / 31250000000 : ℝ)
    (19493578293 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell533_denomUpper :
    Real.exp (59575264110240749 / 10000000000000000 : ℝ) ≤ (386652520963 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59575264110240749 / 10000000000000000 : ℝ) (15057878531
    / 12500000000 : ℝ) (386652520963 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell533_denomLower :
    (3835851519129 / 10000000000 : ℝ) ≤ Real.exp (3718476021908429 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3718476021908429 / 625000000000000 : ℝ) (1204330488217 /
    1000000000000 : ℝ) (3835851519129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell533_product_lower :
    (3822772896908429 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (533 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell533_leftExp
    (by norm_num : (0 : ℝ) ≤ (9734613271 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell533_product_upper :
    Real.pi * Real.exp (267 / 400 : ℝ) ≤ (61240889110240749 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell533_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell533_endpointLower :
    (2921087087 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (533 / 1600 : ℝ) (267 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3822772896908429 / 625000000000000 : ℝ) (Real.pi * Real.exp (533 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell533_product_lower
  have hD : Real.exp (Real.pi * Real.exp (267 / 400 : ℝ) - (533 / 3200 : ℝ)) ≤
      (386652520963 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell533_denomUpper
    linarith [hpThetaJensenCell533_product_upper]
  have hi : (1 / (386652520963 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (267 / 400 : ℝ) - (533 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (386652520963 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (386652520963 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((533 / 3200 : ℝ) - Real.pi * Real.exp (267 / 400 : ℝ)) := by
    rw [show (533 / 3200 : ℝ) - Real.pi * Real.exp (267 / 400 : ℝ) =
      -(Real.pi * Real.exp (267 / 400 : ℝ) - (533 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (533 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (533 / 800 : ℝ)) := by
    have h := hpThetaJensenCell533_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (386652520963 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell533_endpointUpper :
    hpThetaJensenKernelEndpointUpper (533 / 1600 : ℝ) (267 / 800 : ℝ) ≤ (5921586611 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (267 / 400 : ℝ)) (61240889110240749 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (267 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell533_product_upper
  have hD : (3835851519129 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (533 / 800 : ℝ) - (267 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell533_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell533_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (533 / 800 : ℝ) - (267 / 1600 : ℝ)) ≤
      (1 / (3835851519129 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3835851519129 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((267 / 1600 : ℝ) - Real.pi * Real.exp (533 / 800 : ℝ)) ≤
      (2 / (3835851519129 / 10000000000 : ℝ) : ℝ) := by
    rw [show (267 / 1600 : ℝ) - Real.pi * Real.exp (533 / 800 : ℝ) =
      -(Real.pi * Real.exp (533 / 800 : ℝ) - (267 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61240889110240749 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (61240889110240749 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell533_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (533 / 1600 : ℝ) (267 / 800 : ℝ)) :
    (2921087087 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5921586611 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell533_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell533_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell534_leftExp :
    (4873394573 / 2500000000 : ℝ) ≤ Real.exp (267 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (267 / 400 : ℝ) (1021078452383 / 1000000000000 : ℝ)
    (4873394573 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell534_rightExp :
    Real.exp (107 / 160 : ℝ) ≤ (9758980251 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (107 / 160 : ℝ) (6381989619 / 6250000000 : ℝ)
    (9758980251 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell534_denomUpper :
    Real.exp (29824369043679843 / 5000000000000000 : ℝ) ≤ (1947519364933 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29824369043679843 / 5000000000000000 : ℝ) (1204906904791
    / 1000000000000 : ℝ) (1947519364933 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell534_denomLower :
    (483012731567 / 1250000000 : ℝ) ≤ Real.exp (1861531081672527 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1861531081672527 / 312500000000000 : ℝ) (60230334069 /
    50000000000 : ℝ) (483012731567 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell534_product_lower :
    (1913777175422527 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (267 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell534_leftExp
    (by norm_num : (0 : ℝ) ≤ (4873394573 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell534_product_upper :
    Real.pi * Real.exp (107 / 160 : ℝ) ≤ (30658744043679843 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell534_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell534_endpointLower :
    (5816283253 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (267 / 800 : ℝ) (107 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1913777175422527 / 312500000000000 : ℝ) (Real.pi * Real.exp (267 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell534_product_lower
  have hD : Real.exp (Real.pi * Real.exp (107 / 160 : ℝ) - (267 / 1600 : ℝ)) ≤
      (1947519364933 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell534_denomUpper
    linarith [hpThetaJensenCell534_product_upper]
  have hi : (1 / (1947519364933 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (107 / 160 : ℝ) - (267 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1947519364933 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1947519364933 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((267 / 1600 : ℝ) - Real.pi * Real.exp (107 / 160 : ℝ)) := by
    rw [show (267 / 1600 : ℝ) - Real.pi * Real.exp (107 / 160 : ℝ) =
      -(Real.pi * Real.exp (107 / 160 : ℝ) - (267 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (267 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (267 / 400 : ℝ)) := by
    have h := hpThetaJensenCell534_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1947519364933 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell534_endpointUpper :
    hpThetaJensenKernelEndpointUpper (267 / 800 : ℝ) (107 / 320 : ℝ) ≤ (46057783 / 78125000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (107 / 160 : ℝ)) (30658744043679843 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (107 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell534_product_upper
  have hD : (483012731567 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (267 / 400 : ℝ) - (107 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell534_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell534_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (267 / 400 : ℝ) - (107 / 640 : ℝ)) ≤
      (1 / (483012731567 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (483012731567 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((107 / 640 : ℝ) - Real.pi * Real.exp (267 / 400 : ℝ)) ≤
      (2 / (483012731567 / 1250000000 : ℝ) : ℝ) := by
    rw [show (107 / 640 : ℝ) - Real.pi * Real.exp (267 / 400 : ℝ) =
      -(Real.pi * Real.exp (267 / 400 : ℝ) - (107 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30658744043679843 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (30658744043679843 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell534_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (267 / 800 : ℝ) (107 / 320 : ℝ)) :
    (5816283253 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (46057783 / 78125000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell534_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell534_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell535_leftExp :
    (39035921 / 20000000 : ℝ) ≤ Real.exp (107 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (107 / 160 : ℝ) (1021118339039 / 1000000000000 : ℝ)
    (39035921 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell535_rightExp :
    Real.exp (67 / 100 : ℝ) ≤ (19542373207 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 100 : ℝ) (510579113627 / 500000000000 : ℝ)
    (19542373207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell535_denomUpper :
    Real.exp (59722307870498751 / 10000000000000000 : ℝ) ≤ (392380011409 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59722307870498751 / 10000000000000000 : ℝ)
    (1205183951449 / 1000000000000 : ℝ) (392380011409 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell535_denomLower :
    (194629874557 / 500000000 : ℝ) ≤ Real.exp (14910617140779 / 2500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14910617140779 / 2500000000000 : ℝ) (150610412271 /
    125000000000 : ℝ) (194629874557 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell535_product_lower :
    (15329367140779 / 2500000000000 : ℝ) ≤ Real.pi * Real.exp (107 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell535_leftExp
    (by norm_num : (0 : ℝ) ≤ (39035921 / 20000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell535_product_upper :
    Real.pi * Real.exp (67 / 100 : ℝ) ≤ (61394182870498751 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell535_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell535_endpointLower :
    (1447611927 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (107 / 320 : ℝ) (67 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15329367140779 / 2500000000000 : ℝ) (Real.pi * Real.exp (107 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell535_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 100 : ℝ) - (107 / 640 : ℝ)) ≤
      (392380011409 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell535_denomUpper
    linarith [hpThetaJensenCell535_product_upper]
  have hi : (1 / (392380011409 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 100 : ℝ) - (107 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (392380011409 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (392380011409 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((107 / 640 : ℝ) - Real.pi * Real.exp (67 / 100 : ℝ)) := by
    rw [show (107 / 640 : ℝ) - Real.pi * Real.exp (67 / 100 : ℝ) =
      -(Real.pi * Real.exp (67 / 100 : ℝ) - (107 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (107 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (107 / 160 : ℝ)) := by
    have h := hpThetaJensenCell535_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (392380011409 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell535_endpointUpper :
    hpThetaJensenKernelEndpointUpper (107 / 320 : ℝ) (67 / 200 : ℝ) ≤ (5869261579 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 100 : ℝ)) (61394182870498751 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell535_product_upper
  have hD : (194629874557 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (107 / 160 : ℝ) - (67 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell535_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell535_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (107 / 160 : ℝ) - (67 / 400 : ℝ)) ≤
      (1 / (194629874557 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (194629874557 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 400 : ℝ) - Real.pi * Real.exp (107 / 160 : ℝ)) ≤
      (2 / (194629874557 / 500000000 : ℝ) : ℝ) := by
    rw [show (67 / 400 : ℝ) - Real.pi * Real.exp (107 / 160 : ℝ) =
      -(Real.pi * Real.exp (107 / 160 : ℝ) - (67 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61394182870498751 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (61394182870498751 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell535_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (107 / 320 : ℝ) (67 / 200 : ℝ)) :
    (1447611927 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5869261579 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell535_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell535_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell536_leftExp :
    (3908474641 / 2000000000 : ℝ) ≤ Real.exp (67 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 100 : ℝ) (1021158227253 / 1000000000000 : ℝ)
    (3908474641 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell536_rightExp :
    Real.exp (537 / 800 : ℝ) ≤ (305731507 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (537 / 800 : ℝ) (1021198117027 / 1000000000000 : ℝ)
    (305731507 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell536_denomUpper :
    Real.exp (934312087270651 / 156250000000000 : ℝ) ≤ (158112471807 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (934312087270651 / 156250000000000 : ℝ) (1205461423189 /
    1000000000000 : ℝ) (158112471807 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell536_denomLower :
    (3921340839407 / 10000000000 : ℝ) ≤ Real.exp (1492900958046059 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1492900958046059 / 250000000000000 : ℝ) (602580169653 /
    500000000000 : ℝ) (3921340839407 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell536_product_lower :
    (1534854083046059 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell536_leftExp
    (by norm_num : (0 : ℝ) ≤ (3908474641 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell536_product_upper :
    Real.pi * Real.exp (537 / 800 : ℝ) ≤ (960483962270651 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell536_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell536_endpointLower :
    (5764667761 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 200 : ℝ) (537 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1534854083046059 / 250000000000000 : ℝ) (Real.pi * Real.exp (67 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell536_product_lower
  have hD : Real.exp (Real.pi * Real.exp (537 / 800 : ℝ) - (67 / 400 : ℝ)) ≤
      (158112471807 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell536_denomUpper
    linarith [hpThetaJensenCell536_product_upper]
  have hi : (1 / (158112471807 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (537 / 800 : ℝ) - (67 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (158112471807 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (158112471807 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 400 : ℝ) - Real.pi * Real.exp (537 / 800 : ℝ)) := by
    rw [show (67 / 400 : ℝ) - Real.pi * Real.exp (537 / 800 : ℝ) =
      -(Real.pi * Real.exp (537 / 800 : ℝ) - (67 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 100 : ℝ)) := by
    have h := hpThetaJensenCell536_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (158112471807 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell536_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 200 : ℝ) (537 / 1600 : ℝ) ≤ (5843182903 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (537 / 800 : ℝ)) (960483962270651 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (537 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell536_product_upper
  have hD : (3921340839407 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 100 : ℝ) - (537 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell536_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell536_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 100 : ℝ) - (537 / 3200 : ℝ)) ≤
      (1 / (3921340839407 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3921340839407 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((537 / 3200 : ℝ) - Real.pi * Real.exp (67 / 100 : ℝ)) ≤
      (2 / (3921340839407 / 10000000000 : ℝ) : ℝ) := by
    rw [show (537 / 3200 : ℝ) - Real.pi * Real.exp (67 / 100 : ℝ) =
      -(Real.pi * Real.exp (67 / 100 : ℝ) - (537 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (960483962270651 / 156250000000000 : ℝ) ^ 2 - 6 *
      (960483962270651 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell536_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 200 : ℝ) (537 / 1600 : ℝ)) :
    (5764667761 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5843182903 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell536_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell536_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell537_leftExp :
    (9783408223 / 5000000000 : ℝ) ≤ Real.exp (537 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (537 / 800 : ℝ) (510599058513 / 500000000000 : ℝ)
    (9783408223 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell537_rightExp :
    Real.exp (269 / 400 : ℝ) ≤ (19591290261 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (269 / 400 : ℝ) (1021238008357 / 1000000000000 : ℝ)
    (19591290261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell537_denomUpper :
    Real.exp (59869735344925773 / 10000000000000000 : ℝ) ≤ (3982076227651 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59869735344925773 / 10000000000000000 : ℝ)
    (1205739320703 / 1000000000000 : ℝ) (3982076227651 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell537_denomLower :
    (1975167163779 / 5000000000 : ℝ) ≤ Real.exp (3736856500763877 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3736856500763877 / 625000000000000 : ℝ) (602718902759 /
    500000000000 : ℝ) (1975167163779 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell537_product_lower :
    (3841934625763877 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (537 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell537_leftExp
    (by norm_num : (0 : ℝ) ≤ (9783408223 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell537_product_upper :
    Real.pi * Real.exp (269 / 400 : ℝ) ≤ (61547860344925773 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell537_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell537_endpointLower :
    (5738943633 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (537 / 1600 : ℝ) (269 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3841934625763877 / 625000000000000 : ℝ) (Real.pi * Real.exp (537 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell537_product_lower
  have hD : Real.exp (Real.pi * Real.exp (269 / 400 : ℝ) - (537 / 3200 : ℝ)) ≤
      (3982076227651 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell537_denomUpper
    linarith [hpThetaJensenCell537_product_upper]
  have hi : (1 / (3982076227651 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (269 / 400 : ℝ) - (537 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3982076227651 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3982076227651 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((537 / 3200 : ℝ) - Real.pi * Real.exp (269 / 400 : ℝ)) := by
    rw [show (537 / 3200 : ℝ) - Real.pi * Real.exp (269 / 400 : ℝ) =
      -(Real.pi * Real.exp (269 / 400 : ℝ) - (537 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (537 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (537 / 800 : ℝ)) := by
    have h := hpThetaJensenCell537_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3982076227651 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell537_endpointUpper :
    hpThetaJensenKernelEndpointUpper (537 / 1600 : ℝ) (269 / 800 : ℝ) ≤ (5817160413 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (269 / 400 : ℝ)) (61547860344925773 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (269 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell537_product_upper
  have hD : (1975167163779 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (537 / 800 : ℝ) - (269 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell537_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell537_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (537 / 800 : ℝ) - (269 / 1600 : ℝ)) ≤
      (1 / (1975167163779 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1975167163779 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((269 / 1600 : ℝ) - Real.pi * Real.exp (537 / 800 : ℝ)) ≤
      (2 / (1975167163779 / 5000000000 : ℝ) : ℝ) := by
    rw [show (269 / 1600 : ℝ) - Real.pi * Real.exp (537 / 800 : ℝ) =
      -(Real.pi * Real.exp (537 / 800 : ℝ) - (269 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (61547860344925773 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (61547860344925773 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell537_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (537 / 1600 : ℝ) (269 / 800 : ℝ)) :
    (5738943633 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5817160413 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell537_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell537_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell538_leftExp :
    (19591290259 / 10000000000 : ℝ) ≤ Real.exp (269 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (269 / 400 : ℝ) (255309502089 / 250000000000 : ℝ)
    (19591290259 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell538_rightExp :
    Real.exp (539 / 800 : ℝ) ≤ (9807897343 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (539 / 800 : ℝ) (510638950623 / 500000000000 : ℝ)
    (9807897343 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell538_denomUpper :
    Real.exp (29971796637487399 / 5000000000000000 : ℝ) ≤ (2005797948661 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29971796637487399 / 5000000000000000 : ℝ) (1206017644729
    / 1000000000000 : ℝ) (2005797948661 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell538_denomLower :
    (1989790204239 / 5000000000 : ℝ) ≤ Real.exp (7482933218419041 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7482933218419041 / 1250000000000000 : ℝ) (241143139499 /
    200000000000 : ℝ) (1989790204239 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell538_product_lower :
    (7693480093419041 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (269 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell538_leftExp
    (by norm_num : (0 : ℝ) ≤ (19591290259 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell538_product_upper :
    Real.pi * Real.exp (539 / 800 : ℝ) ≤ (30812421637487399 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell538_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell538_endpointLower :
    (5713275539 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (269 / 800 : ℝ) (539 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7693480093419041 / 1250000000000000 : ℝ) (Real.pi * Real.exp (269 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell538_product_lower
  have hD : Real.exp (Real.pi * Real.exp (539 / 800 : ℝ) - (269 / 1600 : ℝ)) ≤
      (2005797948661 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell538_denomUpper
    linarith [hpThetaJensenCell538_product_upper]
  have hi : (1 / (2005797948661 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (539 / 800 : ℝ) - (269 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2005797948661 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2005797948661 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((269 / 1600 : ℝ) - Real.pi * Real.exp (539 / 800 : ℝ)) := by
    rw [show (269 / 1600 : ℝ) - Real.pi * Real.exp (539 / 800 : ℝ) =
      -(Real.pi * Real.exp (539 / 800 : ℝ) - (269 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (269 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (269 / 400 : ℝ)) := by
    have h := hpThetaJensenCell538_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2005797948661 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell538_endpointUpper :
    hpThetaJensenKernelEndpointUpper (269 / 800 : ℝ) (539 / 1600 : ℝ) ≤ (5791194337 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (539 / 800 : ℝ)) (30812421637487399 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (539 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell538_product_upper
  have hD : (1989790204239 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (269 / 400 : ℝ) - (539 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell538_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell538_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (269 / 400 : ℝ) - (539 / 3200 : ℝ)) ≤
      (1 / (1989790204239 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1989790204239 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((539 / 3200 : ℝ) - Real.pi * Real.exp (269 / 400 : ℝ)) ≤
      (2 / (1989790204239 / 5000000000 : ℝ) : ℝ) := by
    rw [show (539 / 3200 : ℝ) - Real.pi * Real.exp (269 / 400 : ℝ) =
      -(Real.pi * Real.exp (269 / 400 : ℝ) - (539 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30812421637487399 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (30812421637487399 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell538_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (269 / 800 : ℝ) (539 / 1600 : ℝ)) :
    (5713275539 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5791194337 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell538_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell538_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell539_leftExp :
    (4903948671 / 2500000000 : ℝ) ≤ Real.exp (539 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (539 / 800 : ℝ) (204255580249 / 200000000000 : ℝ)
    (4903948671 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell539_rightExp :
    Real.exp (27 / 40 : ℝ) ≤ (122752061 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 40 : ℝ) (1021317795693 / 1000000000000 : ℝ)
    (122752061 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell539_denomUpper :
    Real.exp (375109671823173 / 62500000000000 : ℝ) ≤ (2020686656531 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (375109671823173 / 62500000000000 : ℝ) (120629639597 /
    100000000000 : ℝ) (2020686656531 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell539_denomLower :
    (4009081566411 / 10000000000 : ℝ) ≤ Real.exp (1873041364153029 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1873041364153029 / 312500000000000 : ℝ) (48239760639 /
    40000000000 : ℝ) (4009081566411 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell539_product_lower :
    (1925775739153029 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (539 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell539_leftExp
    (by norm_num : (0 : ℝ) ≤ (4903948671 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell539_product_upper :
    Real.pi * Real.exp (27 / 40 : ℝ) ≤ (385637015573173 / 62500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell539_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell539_endpointLower :
    (2843831849 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (539 / 1600 : ℝ) (27 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1925775739153029 / 312500000000000 : ℝ) (Real.pi * Real.exp (539 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell539_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 40 : ℝ) - (539 / 3200 : ℝ)) ≤
      (2020686656531 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell539_denomUpper
    linarith [hpThetaJensenCell539_product_upper]
  have hi : (1 / (2020686656531 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 40 : ℝ) - (539 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2020686656531 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2020686656531 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((539 / 3200 : ℝ) - Real.pi * Real.exp (27 / 40 : ℝ)) := by
    rw [show (539 / 3200 : ℝ) - Real.pi * Real.exp (27 / 40 : ℝ) =
      -(Real.pi * Real.exp (27 / 40 : ℝ) - (539 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (539 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (539 / 800 : ℝ)) := by
    have h := hpThetaJensenCell539_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2020686656531 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell539_endpointUpper :
    hpThetaJensenKernelEndpointUpper (539 / 1600 : ℝ) (27 / 80 : ℝ) ≤ (576528489 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 40 : ℝ)) (385637015573173 / 62500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell539_product_upper
  have hD : (4009081566411 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (539 / 800 : ℝ) - (27 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell539_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell539_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (539 / 800 : ℝ) - (27 / 160 : ℝ)) ≤
      (1 / (4009081566411 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4009081566411 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 160 : ℝ) - Real.pi * Real.exp (539 / 800 : ℝ)) ≤
      (2 / (4009081566411 / 10000000000 : ℝ) : ℝ) := by
    rw [show (27 / 160 : ℝ) - Real.pi * Real.exp (539 / 800 : ℝ) =
      -(Real.pi * Real.exp (539 / 800 : ℝ) - (27 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (385637015573173 / 62500000000000 : ℝ) ^ 2 - 6 *
      (385637015573173 / 62500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell539_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (539 / 1600 : ℝ) (27 / 80 : ℝ)) :
    (2843831849 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (576528489 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell539_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell539_endpointUpper

def hpThetaJensenCellsBatch026Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (247347643 / 400000000 : ℝ)
  | 1 => (1539275327 / 2500000000 : ℝ)
  | 2 => (3065281929 / 5000000000 : ℝ)
  | 3 => (6104078973 / 10000000000 : ℝ)
  | 4 => (60776469 / 100000000 : ℝ)
  | 5 => (151281697 / 250000000 : ℝ)
  | 6 => (3012471077 / 5000000000 : ℝ)
  | 7 => (2999334981 / 5000000000 : ℝ)
  | 8 => (5972451541 / 10000000000 : ℝ)
  | 9 => (743285891 / 1250000000 : ℝ)
  | 10 => (2960088477 / 5000000000 : ℝ)
  | 11 => (5894121251 / 10000000000 : ℝ)
  | 12 => (5868120249 / 10000000000 : ℝ)
  | 13 => (2921087087 / 5000000000 : ℝ)
  | 14 => (5816283253 / 10000000000 : ℝ)
  | 15 => (1447611927 / 2500000000 : ℝ)
  | 16 => (5764667761 / 10000000000 : ℝ)
  | 17 => (5738943633 / 10000000000 : ℝ)
  | 18 => (5713275539 / 10000000000 : ℝ)
  | 19 => (2843831849 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch026Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1253405639 / 2000000000 : ℝ)
  | 1 => (6240134539 / 10000000000 : ℝ)
  | 2 => (3106646759 / 5000000000 : ℝ)
  | 3 => (773313173 / 1250000000 : ℝ)
  | 4 => (1539942597 / 2500000000 : ℝ)
  | 5 => (3066544387 / 5000000000 : ℝ)
  | 6 => (6106460787 / 10000000000 : ℝ)
  | 7 => (6079886673 / 10000000000 : ℝ)
  | 8 => (1513341667 / 2500000000 : ℝ)
  | 9 => (1205380203 / 2000000000 : ℝ)
  | 10 => (3000244973 / 5000000000 : ℝ)
  | 11 => (5974133703 / 10000000000 : ℝ)
  | 12 => (2973916257 / 5000000000 : ℝ)
  | 13 => (5921586611 / 10000000000 : ℝ)
  | 14 => (46057783 / 78125000 : ℝ)
  | 15 => (5869261579 / 10000000000 : ℝ)
  | 16 => (5843182903 / 10000000000 : ℝ)
  | 17 => (5817160413 / 10000000000 : ℝ)
  | 18 => (5791194337 / 10000000000 : ℝ)
  | 19 => (576528489 / 1000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch026_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch026Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch026Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell520_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell521_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell522_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell523_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell524_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell525_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell526_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell527_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell528_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell529_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell530_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell531_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell532_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell533_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell534_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell535_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell536_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell537_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell538_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell539_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper] at h ⊢
    exact h

end HodgeProofHP
