import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell260_leftExp :
    (13840306459 / 10000000000 : ℝ) ≤ Real.exp (13 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 40 : ℝ) (1010207999753 / 1000000000000 : ℝ)
    (13840306459 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell260_rightExp :
    Real.exp (261 / 800 : ℝ) ≤ (13857617661 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (261 / 800 : ℝ) (505123730887 / 500000000000 : ℝ)
    (13857617661 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell260_denomUpper :
    Real.exp (42722494640473973 / 10000000000000000 : ℝ) ≤ (71682702057 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42722494640473973 / 10000000000000000 : ℝ)
    (1142830175321 / 1000000000000 : ℝ) (71682702057 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell260_denomLower :
    (17817885279 / 250000000 : ℝ) ≤ Real.exp (5333121381142841 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5333121381142841 / 1250000000000000 : ℝ) (571312378617 /
    500000000000 : ℝ) (17817885279 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell260_product_lower :
    (5435074506142841 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell260_leftExp
    (by norm_num : (0 : ℝ) ≤ (13840306459 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell260_product_upper :
    Real.pi * Real.exp (261 / 800 : ℝ) ≤ (43534994640473973 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell260_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell260_endpointLower :
    (6910193151 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 80 : ℝ) (261 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5435074506142841 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell260_product_lower
  have hD : Real.exp (Real.pi * Real.exp (261 / 800 : ℝ) - (13 / 160 : ℝ)) ≤
      (71682702057 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell260_denomUpper
    linarith [hpThetaJensenCell260_product_upper]
  have hi : (1 / (71682702057 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (261 / 800 : ℝ) - (13 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71682702057 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71682702057 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 160 : ℝ) - Real.pi * Real.exp (261 / 800 : ℝ)) := by
    rw [show (13 / 160 : ℝ) - Real.pi * Real.exp (261 / 800 : ℝ) =
      -(Real.pi * Real.exp (261 / 800 : ℝ) - (13 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 40 : ℝ)) := by
    have h := hpThetaJensenCell260_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71682702057 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell260_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 80 : ℝ) (261 / 1600 : ℝ) ≤ (13980810567 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (261 / 800 : ℝ)) (43534994640473973 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (261 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell260_product_upper
  have hD : (17817885279 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 40 : ℝ) - (261 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell260_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell260_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 40 : ℝ) - (261 / 3200 : ℝ)) ≤
      (1 / (17817885279 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17817885279 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((261 / 3200 : ℝ) - Real.pi * Real.exp (13 / 40 : ℝ)) ≤
      (2 / (17817885279 / 250000000 : ℝ) : ℝ) := by
    rw [show (261 / 3200 : ℝ) - Real.pi * Real.exp (13 / 40 : ℝ) =
      -(Real.pi * Real.exp (13 / 40 : ℝ) - (261 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43534994640473973 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (43534994640473973 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell260_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 80 : ℝ) (261 / 1600 : ℝ)) :
    (6910193151 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13980810567 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell260_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell260_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell261_leftExp :
    (13857617659 / 10000000000 : ℝ) ≤ Real.exp (261 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (261 / 800 : ℝ) (1010247461773 / 1000000000000 : ℝ)
    (13857617659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell261_rightExp :
    Real.exp (131 / 400 : ℝ) ≤ (6937475257 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (131 / 400 : ℝ) (1010286925337 / 1000000000000 : ℝ)
    (6937475257 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell261_denomUpper :
    Real.exp (21386911205064401 / 5000000000000000 : ℝ) ≤ (720515792521 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21386911205064401 / 5000000000000000 : ℝ) (1143013499161
    / 1000000000000 : ℝ) (720515792521 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell261_denomLower :
    (716378150451 / 10000000000 : ℝ) ≤ Real.exp (5339528847071641 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5339528847071641 / 1250000000000000 : ℝ) (285701951281 /
    250000000000 : ℝ) (716378150451 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell261_product_lower :
    (5441872597071641 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (261 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell261_leftExp
    (by norm_num : (0 : ℝ) ≤ (13857617659 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell261_product_upper :
    Real.pi * Real.exp (131 / 400 : ℝ) ≤ (21794723705064401 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell261_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell261_endpointLower :
    (3448279281 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (261 / 1600 : ℝ) (131 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5441872597071641 / 1250000000000000 : ℝ) (Real.pi * Real.exp (261 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell261_product_lower
  have hD : Real.exp (Real.pi * Real.exp (131 / 400 : ℝ) - (261 / 3200 : ℝ)) ≤
      (720515792521 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell261_denomUpper
    linarith [hpThetaJensenCell261_product_upper]
  have hi : (1 / (720515792521 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (131 / 400 : ℝ) - (261 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (720515792521 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (720515792521 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((261 / 3200 : ℝ) - Real.pi * Real.exp (131 / 400 : ℝ)) := by
    rw [show (261 / 3200 : ℝ) - Real.pi * Real.exp (131 / 400 : ℝ) =
      -(Real.pi * Real.exp (131 / 400 : ℝ) - (261 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (261 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (261 / 800 : ℝ)) := by
    have h := hpThetaJensenCell261_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (720515792521 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell261_endpointUpper :
    hpThetaJensenKernelEndpointUpper (261 / 1600 : ℝ) (131 / 800 : ℝ) ≤ (13953302307 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (131 / 400 : ℝ)) (21794723705064401 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (131 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell261_product_upper
  have hD : (716378150451 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (261 / 800 : ℝ) - (131 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell261_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell261_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (261 / 800 : ℝ) - (131 / 1600 : ℝ)) ≤
      (1 / (716378150451 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (716378150451 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((131 / 1600 : ℝ) - Real.pi * Real.exp (261 / 800 : ℝ)) ≤
      (2 / (716378150451 / 10000000000 : ℝ) : ℝ) := by
    rw [show (131 / 1600 : ℝ) - Real.pi * Real.exp (261 / 800 : ℝ) =
      -(Real.pi * Real.exp (261 / 800 : ℝ) - (131 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21794723705064401 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21794723705064401 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell261_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (261 / 1600 : ℝ) (131 / 800 : ℝ)) :
    (3448279281 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13953302307 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell261_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell261_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell262_leftExp :
    (867184407 / 625000000 : ℝ) ≤ Real.exp (131 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (131 / 400 : ℝ) (126285865667 / 125000000000 : ℝ)
    (867184407 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell262_rightExp :
    Real.exp (263 / 800 : ℝ) ≤ (6946152523 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (263 / 800 : ℝ) (25258159761 / 25000000000 : ℝ)
    (6946152523 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell262_denomUpper :
    Real.exp (21412609143189139 / 5000000000000000 : ℝ) ≤ (181057119809 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21412609143189139 / 5000000000000000 : ℝ) (571598547859
    / 500000000000 : ℝ) (181057119809 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell262_denomLower :
    (180016152817 / 2500000000 : ℝ) ≤ Real.exp (334121551006993 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (334121551006993 / 78125000000000 : ℝ) (1142991125313 /
    1000000000000 : ℝ) (180016152817 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell262_product_lower :
    (340542449444493 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (131 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell262_leftExp
    (by norm_num : (0 : ℝ) ≤ (867184407 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell262_product_upper :
    Real.pi * Real.exp (263 / 800 : ℝ) ≤ (21821984143189139 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell262_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell262_endpointLower :
    (3441447687 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (131 / 800 : ℝ) (263 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (340542449444493 / 78125000000000 : ℝ) (Real.pi * Real.exp (131 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell262_product_lower
  have hD : Real.exp (Real.pi * Real.exp (263 / 800 : ℝ) - (131 / 1600 : ℝ)) ≤
      (181057119809 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell262_denomUpper
    linarith [hpThetaJensenCell262_product_upper]
  have hi : (1 / (181057119809 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (263 / 800 : ℝ) - (131 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (181057119809 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (181057119809 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((131 / 1600 : ℝ) - Real.pi * Real.exp (263 / 800 : ℝ)) := by
    rw [show (131 / 1600 : ℝ) - Real.pi * Real.exp (263 / 800 : ℝ) =
      -(Real.pi * Real.exp (263 / 800 : ℝ) - (131 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (131 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (131 / 400 : ℝ)) := by
    have h := hpThetaJensenCell262_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (181057119809 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell262_endpointUpper :
    hpThetaJensenKernelEndpointUpper (131 / 800 : ℝ) (263 / 1600 : ℝ) ≤ (6962868017 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (263 / 800 : ℝ)) (21821984143189139 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (263 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell262_product_upper
  have hD : (180016152817 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (131 / 400 : ℝ) - (263 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell262_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell262_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (131 / 400 : ℝ) - (263 / 3200 : ℝ)) ≤
      (1 / (180016152817 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (180016152817 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((263 / 3200 : ℝ) - Real.pi * Real.exp (131 / 400 : ℝ)) ≤
      (2 / (180016152817 / 2500000000 : ℝ) : ℝ) := by
    rw [show (263 / 3200 : ℝ) - Real.pi * Real.exp (131 / 400 : ℝ) =
      -(Real.pi * Real.exp (131 / 400 : ℝ) - (263 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21821984143189139 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21821984143189139 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell262_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (131 / 800 : ℝ) (263 / 1600 : ℝ)) :
    (3441447687 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6962868017 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell262_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell262_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell263_leftExp :
    (2778461009 / 2000000000 : ℝ) ≤ Real.exp (263 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (263 / 800 : ℝ) (1010326390439 / 1000000000000 : ℝ)
    (2778461009 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell263_rightExp :
    Real.exp (33 / 100 : ℝ) ≤ (2781936257 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 100 : ℝ) (505182928543 / 500000000000 : ℝ)
    (2781936257 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell263_denomUpper :
    Real.exp (8575336471437401 / 2000000000000000 : ℝ) ≤ (90995657633 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8575336471437401 / 2000000000000000 : ℝ) (1143380965429
    / 1000000000000 : ℝ) (90995657633 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell263_denomLower :
    (723774972111 / 10000000000 : ℝ) ≤ Real.exp (1070473859773291 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1070473859773291 / 250000000000000 : ℝ) (571587359113 /
    500000000000 : ℝ) (723774972111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell263_product_lower :
    (1091098859773291 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (263 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell263_leftExp
    (by norm_num : (0 : ℝ) ≤ (2778461009 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell263_product_upper :
    Real.pi * Real.exp (33 / 100 : ℝ) ≤ (8739711471437401 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell263_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell263_endpointLower :
    (274768153 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (263 / 1600 : ℝ) (33 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1091098859773291 / 250000000000000 : ℝ) (Real.pi * Real.exp (263 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell263_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 100 : ℝ) - (263 / 3200 : ℝ)) ≤
      (90995657633 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell263_denomUpper
    linarith [hpThetaJensenCell263_product_upper]
  have hi : (1 / (90995657633 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 100 : ℝ) - (263 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (90995657633 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (90995657633 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((263 / 3200 : ℝ) - Real.pi * Real.exp (33 / 100 : ℝ)) := by
    rw [show (263 / 3200 : ℝ) - Real.pi * Real.exp (33 / 100 : ℝ) =
      -(Real.pi * Real.exp (33 / 100 : ℝ) - (263 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (263 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (263 / 800 : ℝ)) := by
    have h := hpThetaJensenCell263_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (90995657633 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell263_endpointUpper :
    hpThetaJensenKernelEndpointUpper (263 / 1600 : ℝ) (33 / 200 : ℝ) ≤ (6949056117 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 100 : ℝ)) (8739711471437401 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell263_product_upper
  have hD : (723774972111 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (263 / 800 : ℝ) - (33 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell263_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell263_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (263 / 800 : ℝ) - (33 / 400 : ℝ)) ≤
      (1 / (723774972111 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (723774972111 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 400 : ℝ) - Real.pi * Real.exp (263 / 800 : ℝ)) ≤
      (2 / (723774972111 / 10000000000 : ℝ) : ℝ) := by
    rw [show (33 / 400 : ℝ) - Real.pi * Real.exp (263 / 800 : ℝ) =
      -(Real.pi * Real.exp (263 / 800 : ℝ) - (33 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8739711471437401 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (8739711471437401 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell263_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (263 / 1600 : ℝ) (33 / 200 : ℝ)) :
    (274768153 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6949056117 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell263_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell263_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell264_leftExp :
    (3477420321 / 2500000000 : ℝ) ≤ Real.exp (33 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 100 : ℝ) (202073171417 / 200000000000 : ℝ)
    (3477420321 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell264_rightExp :
    Real.exp (53 / 160 : ℝ) ≤ (6963539629 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 160 : ℝ) (1010405325273 / 1000000000000 : ℝ)
    (6963539629 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell264_denomUpper :
    Real.exp (21464107353688997 / 5000000000000000 : ℝ) ≤ (731726319623 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21464107353688997 / 5000000000000000 : ℝ) (1143565108719
    / 1000000000000 : ℝ) (731726319623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell264_denomLower :
    (727509412731 / 10000000000 : ℝ) ≤ Real.exp (1339700576386379 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1339700576386379 / 312500000000000 : ℝ) (285839646069 /
    250000000000 : ℝ) (727509412731 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell264_product_lower :
    (1365579482636379 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell264_leftExp
    (by norm_num : (0 : ℝ) ≤ (3477420321 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell264_product_upper :
    Real.pi * Real.exp (53 / 160 : ℝ) ≤ (21876607353688997 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell264_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell264_endpointLower :
    (1371096831 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 200 : ℝ) (53 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1365579482636379 / 312500000000000 : ℝ) (Real.pi * Real.exp (33 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell264_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 160 : ℝ) - (33 / 400 : ℝ)) ≤
      (731726319623 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell264_denomUpper
    linarith [hpThetaJensenCell264_product_upper]
  have hi : (1 / (731726319623 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 160 : ℝ) - (33 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (731726319623 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (731726319623 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 400 : ℝ) - Real.pi * Real.exp (53 / 160 : ℝ)) := by
    rw [show (33 / 400 : ℝ) - Real.pi * Real.exp (53 / 160 : ℝ) =
      -(Real.pi * Real.exp (53 / 160 : ℝ) - (33 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 100 : ℝ)) := by
    have h := hpThetaJensenCell264_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (731726319623 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell264_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 200 : ℝ) (53 / 320 : ℝ) ≤ (6935215699 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 160 : ℝ)) (21876607353688997 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell264_product_upper
  have hD : (727509412731 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 100 : ℝ) - (53 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell264_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell264_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 100 : ℝ) - (53 / 640 : ℝ)) ≤
      (1 / (727509412731 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (727509412731 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 640 : ℝ) - Real.pi * Real.exp (33 / 100 : ℝ)) ≤
      (2 / (727509412731 / 10000000000 : ℝ) : ℝ) := by
    rw [show (53 / 640 : ℝ) - Real.pi * Real.exp (33 / 100 : ℝ) =
      -(Real.pi * Real.exp (33 / 100 : ℝ) - (53 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21876607353688997 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21876607353688997 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell264_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 200 : ℝ) (53 / 320 : ℝ)) :
    (1371096831 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6935215699 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell264_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell264_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell265_leftExp :
    (13927079257 / 10000000000 : ℝ) ≤ Real.exp (53 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 160 : ℝ) (126300665659 / 125000000000 : ℝ)
    (13927079257 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell265_rightExp :
    Real.exp (133 / 400 : ℝ) ≤ (13944498993 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (133 / 400 : ℝ) (505222397501 / 500000000000 : ℝ)
    (13944498993 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell265_denomUpper :
    Real.exp (42979815424915849 / 10000000000000000 : ℝ) ≤ (735511838301 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42979815424915849 / 10000000000000000 : ℝ) (45749981041
    / 40000000000 : ℝ) (735511838301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell265_denomLower :
    (146253622971 / 2000000000 : ℝ) ≤ Real.exp (5365243847144643 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5365243847144643 / 1250000000000000 : ℝ) (1143542723899
    / 1000000000000 : ℝ) (146253622971 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell265_product_lower :
    (5469150097144643 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell265_leftExp
    (by norm_num : (0 : ℝ) ≤ (13927079257 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell265_product_upper :
    Real.pi * Real.exp (133 / 400 : ℝ) ≤ (43807940424915849 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell265_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell265_endpointLower :
    (6841736603 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 320 : ℝ) (133 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5469150097144643 / 1250000000000000 : ℝ) (Real.pi * Real.exp (53 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell265_product_lower
  have hD : Real.exp (Real.pi * Real.exp (133 / 400 : ℝ) - (53 / 640 : ℝ)) ≤
      (735511838301 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell265_denomUpper
    linarith [hpThetaJensenCell265_product_upper]
  have hi : (1 / (735511838301 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (133 / 400 : ℝ) - (53 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (735511838301 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (735511838301 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 640 : ℝ) - Real.pi * Real.exp (133 / 400 : ℝ)) := by
    rw [show (53 / 640 : ℝ) - Real.pi * Real.exp (133 / 400 : ℝ) =
      -(Real.pi * Real.exp (133 / 400 : ℝ) - (53 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 160 : ℝ)) := by
    have h := hpThetaJensenCell265_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (735511838301 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell265_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 320 : ℝ) (133 / 800 : ℝ) ≤ (1730336751 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (133 / 400 : ℝ)) (43807940424915849 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (133 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell265_product_upper
  have hD : (146253622971 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 160 : ℝ) - (133 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell265_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell265_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 160 : ℝ) - (133 / 1600 : ℝ)) ≤
      (1 / (146253622971 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (146253622971 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((133 / 1600 : ℝ) - Real.pi * Real.exp (53 / 160 : ℝ)) ≤
      (2 / (146253622971 / 2000000000 : ℝ) : ℝ) := by
    rw [show (133 / 1600 : ℝ) - Real.pi * Real.exp (53 / 160 : ℝ) =
      -(Real.pi * Real.exp (53 / 160 : ℝ) - (133 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43807940424915849 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (43807940424915849 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell265_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 320 : ℝ) (133 / 800 : ℝ)) :
    (6841736603 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1730336751 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell265_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell265_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell266_leftExp :
    (13944498991 / 10000000000 : ℝ) ≤ Real.exp (133 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (133 / 400 : ℝ) (1010444795001 / 1000000000000 : ℝ)
    (13944498991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell266_rightExp :
    Real.exp (267 / 800 : ℝ) ≤ (2792388103 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (267 / 800 : ℝ) (1010484266273 / 1000000000000 : ℝ)
    (2792388103 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell266_denomUpper :
    Real.exp (8606296917668079 / 2000000000000000 : ℝ) ≤ (739322001369 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8606296917668079 / 2000000000000000 : ℝ) (142991777219 /
    125000000000 : ℝ) (739322001369 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell266_denomLower :
    (735051261549 / 10000000000 : ℝ) ≤ Real.exp (5371693934266709 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5371693934266709 / 1250000000000000 : ℝ) (571863568761 /
    500000000000 : ℝ) (735051261549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell266_product_lower :
    (5475990809266709 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (133 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell266_leftExp
    (by norm_num : (0 : ℝ) ≤ (13944498991 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell266_product_upper :
    Real.pi * Real.exp (267 / 800 : ℝ) ≤ (8772546917668079 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell266_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell266_endpointLower :
    (853495177 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (133 / 800 : ℝ) (267 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5475990809266709 / 1250000000000000 : ℝ) (Real.pi * Real.exp (133 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell266_product_lower
  have hD : Real.exp (Real.pi * Real.exp (267 / 800 : ℝ) - (133 / 1600 : ℝ)) ≤
      (739322001369 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell266_denomUpper
    linarith [hpThetaJensenCell266_product_upper]
  have hi : (1 / (739322001369 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (267 / 800 : ℝ) - (133 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (739322001369 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (739322001369 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((133 / 1600 : ℝ) - Real.pi * Real.exp (267 / 800 : ℝ)) := by
    rw [show (133 / 1600 : ℝ) - Real.pi * Real.exp (267 / 800 : ℝ) =
      -(Real.pi * Real.exp (267 / 800 : ℝ) - (133 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (133 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (133 / 400 : ℝ)) := by
    have h := hpThetaJensenCell266_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (739322001369 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell266_endpointUpper :
    hpThetaJensenKernelEndpointUpper (133 / 800 : ℝ) (267 / 1600 : ℝ) ≤ (6907450273 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (267 / 800 : ℝ)) (8772546917668079 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (267 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell266_product_upper
  have hD : (735051261549 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (133 / 400 : ℝ) - (267 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell266_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell266_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (133 / 400 : ℝ) - (267 / 3200 : ℝ)) ≤
      (1 / (735051261549 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (735051261549 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((267 / 3200 : ℝ) - Real.pi * Real.exp (133 / 400 : ℝ)) ≤
      (2 / (735051261549 / 10000000000 : ℝ) : ℝ) := by
    rw [show (267 / 3200 : ℝ) - Real.pi * Real.exp (133 / 400 : ℝ) =
      -(Real.pi * Real.exp (133 / 400 : ℝ) - (267 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8772546917668079 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (8772546917668079 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell266_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (133 / 800 : ℝ) (267 / 1600 : ℝ)) :
    (853495177 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6907450273 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell266_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell266_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell267_leftExp :
    (6980970257 / 5000000000 : ℝ) ≤ Real.exp (267 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (267 / 800 : ℝ) (31577633321 / 31250000000 : ℝ)
    (6980970257 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell267_rightExp :
    Real.exp (67 / 200 : ℝ) ≤ (13979403853 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 200 : ℝ) (202104747817 / 200000000000 : ℝ)
    (13979403853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell267_denomUpper :
    Real.exp (43083222288757829 / 10000000000000000 : ℝ) ≤ (743156995513 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43083222288757829 / 10000000000000000 : ℝ)
    (1144119184347 / 1000000000000 : ℝ) (743156995513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell267_denomLower :
    (184714759407 / 2500000000 : ℝ) ≤ Real.exp (2689076288953643 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2689076288953643 / 625000000000000 : ℝ) (571955912791 /
    500000000000 : ℝ) (184714759407 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell267_product_lower :
    (2741420038953643 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (267 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell267_leftExp
    (by norm_num : (0 : ℝ) ≤ (6980970257 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell267_product_upper :
    Real.pi * Real.exp (67 / 200 : ℝ) ≤ (43917597288757829 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell267_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell267_endpointLower :
    (13628317663 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (267 / 1600 : ℝ) (67 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2741420038953643 / 625000000000000 : ℝ) (Real.pi * Real.exp (267 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell267_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 200 : ℝ) - (267 / 3200 : ℝ)) ≤
      (743156995513 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell267_denomUpper
    linarith [hpThetaJensenCell267_product_upper]
  have hi : (1 / (743156995513 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 200 : ℝ) - (267 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (743156995513 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (743156995513 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((267 / 3200 : ℝ) - Real.pi * Real.exp (67 / 200 : ℝ)) := by
    rw [show (267 / 3200 : ℝ) - Real.pi * Real.exp (67 / 200 : ℝ) =
      -(Real.pi * Real.exp (67 / 200 : ℝ) - (267 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (267 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (267 / 800 : ℝ)) := by
    have h := hpThetaJensenCell267_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (743156995513 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell267_endpointUpper :
    hpThetaJensenKernelEndpointUpper (267 / 1600 : ℝ) (67 / 400 : ℝ) ≤ (27574103 / 20000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 200 : ℝ)) (43917597288757829 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell267_product_upper
  have hD : (184714759407 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (267 / 800 : ℝ) - (67 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell267_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell267_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (267 / 800 : ℝ) - (67 / 800 : ℝ)) ≤
      (1 / (184714759407 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (184714759407 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 800 : ℝ) - Real.pi * Real.exp (267 / 800 : ℝ)) ≤
      (2 / (184714759407 / 2500000000 : ℝ) : ℝ) := by
    rw [show (67 / 800 : ℝ) - Real.pi * Real.exp (267 / 800 : ℝ) =
      -(Real.pi * Real.exp (267 / 800 : ℝ) - (67 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43917597288757829 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (43917597288757829 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell267_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (267 / 1600 : ℝ) (67 / 400 : ℝ)) :
    (13628317663 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (27574103 / 20000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell267_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell267_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell268_leftExp :
    (13979403851 / 10000000000 : ℝ) ≤ Real.exp (67 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 200 : ℝ) (252630934771 / 250000000000 : ℝ)
    (13979403851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell268_rightExp :
    Real.exp (269 / 800 : ℝ) ≤ (6998444517 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (269 / 800 : ℝ) (1579005021 / 1562500000 : ℝ)
    (6998444517 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell268_denomUpper :
    Real.exp (21567514305495581 / 5000000000000000 : ℝ) ≤ (747017008617 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21567514305495581 / 5000000000000000 : ℝ) (1144304426239
    / 1000000000000 : ℝ) (747017008617 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell268_denomLower :
    (371345814397 / 5000000000 : ℝ) ≤ Real.exp (5384619787883849 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5384619787883849 / 1250000000000000 : ℝ) (286024197121 /
    250000000000 : ℝ) (371345814397 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell268_product_lower :
    (5489697912883849 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell268_leftExp
    (by norm_num : (0 : ℝ) ≤ (13979403851 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell268_product_upper :
    Real.pi * Real.exp (269 / 800 : ℝ) ≤ (21986264305495581 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell268_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell268_endpointLower :
    (680032909 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 400 : ℝ) (269 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5489697912883849 / 1250000000000000 : ℝ) (Real.pi * Real.exp (67 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell268_product_lower
  have hD : Real.exp (Real.pi * Real.exp (269 / 800 : ℝ) - (67 / 800 : ℝ)) ≤
      (747017008617 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell268_denomUpper
    linarith [hpThetaJensenCell268_product_upper]
  have hi : (1 / (747017008617 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (269 / 800 : ℝ) - (67 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (747017008617 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (747017008617 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 800 : ℝ) - Real.pi * Real.exp (269 / 800 : ℝ)) := by
    rw [show (67 / 800 : ℝ) - Real.pi * Real.exp (269 / 800 : ℝ) =
      -(Real.pi * Real.exp (269 / 800 : ℝ) - (67 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 200 : ℝ)) := by
    have h := hpThetaJensenCell268_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (747017008617 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell268_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 400 : ℝ) (269 / 1600 : ℝ) ≤ (3439786841 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (269 / 800 : ℝ)) (21986264305495581 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (269 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell268_product_upper
  have hD : (371345814397 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 200 : ℝ) - (269 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell268_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell268_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 200 : ℝ) - (269 / 3200 : ℝ)) ≤
      (1 / (371345814397 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (371345814397 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((269 / 3200 : ℝ) - Real.pi * Real.exp (67 / 200 : ℝ)) ≤
      (2 / (371345814397 / 5000000000 : ℝ) : ℝ) := by
    rw [show (269 / 3200 : ℝ) - Real.pi * Real.exp (67 / 200 : ℝ) =
      -(Real.pi * Real.exp (67 / 200 : ℝ) - (269 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21986264305495581 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21986264305495581 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell268_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 400 : ℝ) (269 / 1600 : ℝ)) :
    (680032909 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3439786841 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell268_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell268_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell269_leftExp :
    (1749611129 / 1250000000 : ℝ) ≤ Real.exp (269 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (269 / 800 : ℝ) (1010563213439 / 1000000000000 : ℝ)
    (1749611129 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell269_rightExp :
    Real.exp (27 / 80 : ℝ) ≤ (3503599021 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 80 : ℝ) (126325336167 / 125000000000 : ℝ)
    (3503599021 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell269_denomUpper :
    Real.exp (10796725909180453 / 2500000000000000 : ℝ) ≤ (150180445971 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10796725909180453 / 2500000000000000 : ℝ) (1144489943843
    / 1000000000000 : ℝ) (150180445971 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell269_denomLower :
    (149309844687 / 2000000000 : ℝ) ≤ Real.exp (673886946997171 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (673886946997171 / 156250000000000 : ℝ) (1144282026687 /
    1000000000000 : ℝ) (149309844687 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell269_product_lower :
    (687070540747171 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (269 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell269_leftExp
    (by norm_num : (0 : ℝ) ≤ (1749611129 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell269_product_upper :
    Real.pi * Real.exp (27 / 80 : ℝ) ≤ (11006882159180453 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell269_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell269_endpointLower :
    (13572944877 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (269 / 1600 : ℝ) (27 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (687070540747171 / 156250000000000 : ℝ) (Real.pi * Real.exp (269 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell269_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 80 : ℝ) - (269 / 3200 : ℝ)) ≤
      (150180445971 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell269_denomUpper
    linarith [hpThetaJensenCell269_product_upper]
  have hi : (1 / (150180445971 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 80 : ℝ) - (269 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (150180445971 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (150180445971 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((269 / 3200 : ℝ) - Real.pi * Real.exp (27 / 80 : ℝ)) := by
    rw [show (269 / 3200 : ℝ) - Real.pi * Real.exp (27 / 80 : ℝ) =
      -(Real.pi * Real.exp (27 / 80 : ℝ) - (269 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (269 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (269 / 800 : ℝ)) := by
    have h := hpThetaJensenCell269_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (150180445971 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell269_endpointUpper :
    hpThetaJensenKernelEndpointUpper (269 / 1600 : ℝ) (27 / 160 : ℝ) ≤ (13731188613 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 80 : ℝ)) (11006882159180453 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell269_product_upper
  have hD : (149309844687 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (269 / 800 : ℝ) - (27 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell269_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell269_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (269 / 800 : ℝ) - (27 / 320 : ℝ)) ≤
      (1 / (149309844687 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (149309844687 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 320 : ℝ) - Real.pi * Real.exp (269 / 800 : ℝ)) ≤
      (2 / (149309844687 / 2000000000 : ℝ) : ℝ) := by
    rw [show (27 / 320 : ℝ) - Real.pi * Real.exp (269 / 800 : ℝ) =
      -(Real.pi * Real.exp (269 / 800 : ℝ) - (27 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11006882159180453 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (11006882159180453 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell269_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (269 / 1600 : ℝ) (27 / 160 : ℝ)) :
    (13572944877 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13731188613 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell269_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell269_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell270_leftExp :
    (14014396083 / 10000000000 : ℝ) ≤ Real.exp (27 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 80 : ℝ) (202120537867 / 200000000000 : ℝ)
    (14014396083 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell270_rightExp :
    Real.exp (271 / 800 : ℝ) ≤ (14031925033 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (271 / 800 : ℝ) (40425686671 / 40000000000 : ℝ)
    (14031925033 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell270_denomUpper :
    Real.exp (43238847460197569 / 10000000000000000 : ℝ) ≤ (94351606373 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43238847460197569 / 10000000000000000 : ℝ)
    (1144675737621 / 1000000000000 : ℝ) (94351606373 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell270_denomLower :
    (15008640213 / 200000000 : ℝ) ≤ Real.exp (5397579952398017 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5397579952398017 / 1250000000000000 : ℝ) (8941152661 /
    7812500000 : ℝ) (15008640213 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell270_product_lower :
    (5503439327398017 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell270_leftExp
    (by norm_num : (0 : ℝ) ≤ (14014396083 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell270_product_upper :
    Real.pi * Real.exp (271 / 800 : ℝ) ≤ (44082597460197569 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell270_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell270_endpointLower :
    (6772589113 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 160 : ℝ) (271 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5503439327398017 / 1250000000000000 : ℝ) (Real.pi * Real.exp (27 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell270_product_lower
  have hD : Real.exp (Real.pi * Real.exp (271 / 800 : ℝ) - (27 / 320 : ℝ)) ≤
      (94351606373 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell270_denomUpper
    linarith [hpThetaJensenCell270_product_upper]
  have hi : (1 / (94351606373 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (271 / 800 : ℝ) - (27 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (94351606373 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (94351606373 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 320 : ℝ) - Real.pi * Real.exp (271 / 800 : ℝ)) := by
    rw [show (27 / 320 : ℝ) - Real.pi * Real.exp (271 / 800 : ℝ) =
      -(Real.pi * Real.exp (271 / 800 : ℝ) - (27 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 80 : ℝ)) := by
    have h := hpThetaJensenCell270_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (94351606373 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell270_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 160 : ℝ) (271 / 1600 : ℝ) ≤ (13703175747 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (271 / 800 : ℝ)) (44082597460197569 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (271 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell270_product_upper
  have hD : (15008640213 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 80 : ℝ) - (271 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell270_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell270_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 80 : ℝ) - (271 / 3200 : ℝ)) ≤
      (1 / (15008640213 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (15008640213 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((271 / 3200 : ℝ) - Real.pi * Real.exp (27 / 80 : ℝ)) ≤
      (2 / (15008640213 / 200000000 : ℝ) : ℝ) := by
    rw [show (271 / 3200 : ℝ) - Real.pi * Real.exp (27 / 80 : ℝ) =
      -(Real.pi * Real.exp (27 / 80 : ℝ) - (271 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44082597460197569 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44082597460197569 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell270_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 160 : ℝ) (271 / 1600 : ℝ)) :
    (6772589113 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13703175747 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell270_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell270_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell271_leftExp :
    (1753990629 / 1250000000 : ℝ) ≤ Real.exp (271 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (271 / 800 : ℝ) (505321083387 / 500000000000 : ℝ)
    (1753990629 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell271_rightExp :
    Real.exp (17 / 50 : ℝ) ≤ (14049475907 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 50 : ℝ) (252670411439 / 250000000000 : ℝ)
    (14049475907 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell271_denomUpper :
    Real.exp (43290860163099851 / 10000000000000000 : ℝ) ≤ (75874906441 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43290860163099851 / 10000000000000000 : ℝ)
    (1144861807989 / 1000000000000 : ℝ) (75874906441 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell271_denomLower :
    (150868036319 / 2000000000 : ℝ) ≤ Real.exp (675509116017671 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (675509116017671 / 156250000000000 : ℝ) (572326665343 /
    500000000000 : ℝ) (150868036319 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell271_product_lower :
    (688790366017671 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (271 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell271_leftExp
    (by norm_num : (0 : ℝ) ≤ (1753990629 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell271_product_upper :
    Real.pi * Real.exp (17 / 50 : ℝ) ≤ (44137735163099851 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell271_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell271_endpointLower :
    (13517358717 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (271 / 1600 : ℝ) (17 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (688790366017671 / 156250000000000 : ℝ) (Real.pi * Real.exp (271 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell271_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 50 : ℝ) - (271 / 3200 : ℝ)) ≤
      (75874906441 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell271_denomUpper
    linarith [hpThetaJensenCell271_product_upper]
  have hi : (1 / (75874906441 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 50 : ℝ) - (271 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (75874906441 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (75874906441 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((271 / 3200 : ℝ) - Real.pi * Real.exp (17 / 50 : ℝ)) := by
    rw [show (271 / 3200 : ℝ) - Real.pi * Real.exp (17 / 50 : ℝ) =
      -(Real.pi * Real.exp (17 / 50 : ℝ) - (271 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (271 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (271 / 800 : ℝ)) := by
    have h := hpThetaJensenCell271_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (75874906441 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell271_endpointUpper :
    hpThetaJensenKernelEndpointUpper (271 / 1600 : ℝ) (17 / 100 : ℝ) ≤ (6837554623 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 50 : ℝ)) (44137735163099851 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell271_product_upper
  have hD : (150868036319 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (271 / 800 : ℝ) - (17 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell271_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell271_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (271 / 800 : ℝ) - (17 / 200 : ℝ)) ≤
      (1 / (150868036319 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (150868036319 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 200 : ℝ) - Real.pi * Real.exp (271 / 800 : ℝ)) ≤
      (2 / (150868036319 / 2000000000 : ℝ) : ℝ) := by
    rw [show (17 / 200 : ℝ) - Real.pi * Real.exp (271 / 800 : ℝ) =
      -(Real.pi * Real.exp (271 / 800 : ℝ) - (17 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44137735163099851 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44137735163099851 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell271_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (271 / 1600 : ℝ) (17 / 100 : ℝ)) :
    (13517358717 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6837554623 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell271_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell271_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell272_leftExp :
    (2809895181 / 2000000000 : ℝ) ≤ Real.exp (17 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 50 : ℝ) (202136329151 / 200000000000 : ℝ)
    (2809895181 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell272_rightExp :
    Real.exp (273 / 800 : ℝ) ≤ (3516762183 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (273 / 800 : ℝ) (1010721126279 / 1000000000000 : ℝ)
    (3516762183 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell272_denomUpper :
    Real.exp (10835735456777519 / 2500000000000000 : ℝ) ≤ (762711064223 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10835735456777519 / 2500000000000000 : ℝ) (572524077683
    / 500000000000 : ℝ) (762711064223 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell272_denomLower :
    (758273928573 / 10000000000 : ℝ) ≤ Real.exp (1082114902683519 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1082114902683519 / 250000000000000 : ℝ) (572419698669 /
    500000000000 : ℝ) (758273928573 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell272_product_lower :
    (1103443027683519 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell272_leftExp
    (by norm_num : (0 : ℝ) ≤ (2809895181 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell272_product_upper :
    Real.pi * Real.exp (273 / 800 : ℝ) ≤ (11048235456777519 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell272_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell272_endpointLower :
    (13489486839 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 100 : ℝ) (273 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1103443027683519 / 250000000000000 : ℝ) (Real.pi * Real.exp (17 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell272_product_lower
  have hD : Real.exp (Real.pi * Real.exp (273 / 800 : ℝ) - (17 / 200 : ℝ)) ≤
      (762711064223 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell272_denomUpper
    linarith [hpThetaJensenCell272_product_upper]
  have hi : (1 / (762711064223 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (273 / 800 : ℝ) - (17 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (762711064223 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (762711064223 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 200 : ℝ) - Real.pi * Real.exp (273 / 800 : ℝ)) := by
    rw [show (17 / 200 : ℝ) - Real.pi * Real.exp (273 / 800 : ℝ) =
      -(Real.pi * Real.exp (273 / 800 : ℝ) - (17 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 50 : ℝ)) := by
    have h := hpThetaJensenCell272_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (762711064223 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell272_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 100 : ℝ) (273 / 1600 : ℝ) ≤ (13646989603 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (273 / 800 : ℝ)) (11048235456777519 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (273 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell272_product_upper
  have hD : (758273928573 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 50 : ℝ) - (273 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell272_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell272_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 50 : ℝ) - (273 / 3200 : ℝ)) ≤
      (1 / (758273928573 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (758273928573 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((273 / 3200 : ℝ) - Real.pi * Real.exp (17 / 50 : ℝ)) ≤
      (2 / (758273928573 / 10000000000 : ℝ) : ℝ) := by
    rw [show (273 / 3200 : ℝ) - Real.pi * Real.exp (17 / 50 : ℝ) =
      -(Real.pi * Real.exp (17 / 50 : ℝ) - (273 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11048235456777519 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (11048235456777519 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell272_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 100 : ℝ) (273 / 1600 : ℝ)) :
    (13489486839 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13646989603 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell272_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell272_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell273_leftExp :
    (14067048731 / 10000000000 : ℝ) ≤ Real.exp (273 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (273 / 800 : ℝ) (505360563139 / 500000000000 : ℝ)
    (14067048731 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell273_rightExp :
    Real.exp (137 / 400 : ℝ) ≤ (7042321769 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (137 / 400 : ℝ) (126345076043 / 125000000000 : ℝ)
    (7042321769 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell273_denomUpper :
    Real.exp (21697546273238017 / 5000000000000000 : ℝ) ≤ (766699047071 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21697546273238017 / 5000000000000000 : ℝ) (572617390107
    / 500000000000 : ℝ) (766699047071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell273_denomLower :
    (190558361563 / 2500000000 : ℝ) ≤ Real.exp (5417084719614969 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5417084719614969 / 1250000000000000 : ℝ) (143128217627 /
    125000000000 : ℝ) (190558361563 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell273_product_lower :
    (5524115969614969 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (273 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell273_leftExp
    (by norm_num : (0 : ℝ) ≤ (14067048731 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell273_product_upper :
    Real.pi * Real.exp (137 / 400 : ℝ) ≤ (22124108773238017 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell273_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell273_endpointLower :
    (13461563071 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (273 / 1600 : ℝ) (137 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5524115969614969 / 1250000000000000 : ℝ) (Real.pi * Real.exp (273 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell273_product_lower
  have hD : Real.exp (Real.pi * Real.exp (137 / 400 : ℝ) - (273 / 3200 : ℝ)) ≤
      (766699047071 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell273_denomUpper
    linarith [hpThetaJensenCell273_product_upper]
  have hi : (1 / (766699047071 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (137 / 400 : ℝ) - (273 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (766699047071 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (766699047071 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((273 / 3200 : ℝ) - Real.pi * Real.exp (137 / 400 : ℝ)) := by
    rw [show (273 / 3200 : ℝ) - Real.pi * Real.exp (137 / 400 : ℝ) =
      -(Real.pi * Real.exp (137 / 400 : ℝ) - (273 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (273 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (273 / 800 : ℝ)) := by
    have h := hpThetaJensenCell273_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (766699047071 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell273_endpointUpper :
    hpThetaJensenKernelEndpointUpper (273 / 1600 : ℝ) (137 / 800 : ℝ) ≤ (13618817307 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (137 / 400 : ℝ)) (22124108773238017 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (137 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell273_product_upper
  have hD : (190558361563 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (273 / 800 : ℝ) - (137 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell273_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell273_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (273 / 800 : ℝ) - (137 / 1600 : ℝ)) ≤
      (1 / (190558361563 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (190558361563 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((137 / 1600 : ℝ) - Real.pi * Real.exp (273 / 800 : ℝ)) ≤
      (2 / (190558361563 / 2500000000 : ℝ) : ℝ) := by
    rw [show (137 / 1600 : ℝ) - Real.pi * Real.exp (273 / 800 : ℝ) =
      -(Real.pi * Real.exp (273 / 800 : ℝ) - (137 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22124108773238017 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22124108773238017 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell273_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (273 / 1600 : ℝ) (137 / 800 : ℝ)) :
    (13461563071 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13618817307 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell273_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell273_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell274_leftExp :
    (880290221 / 625000000 : ℝ) ≤ Real.exp (137 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (137 / 400 : ℝ) (1010760608343 / 1000000000000 : ℝ)
    (880290221 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell274_rightExp :
    Real.exp (11 / 32 : ℝ) ≤ (282045207 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 32 : ℝ) (1010800091951 / 1000000000000 : ℝ)
    (282045207 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell274_denomUpper :
    Real.exp (868946247994751 / 200000000000000 : ℝ) ≤ (770713210069 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (868946247994751 / 200000000000000 : ℝ) (1145421682939 /
    1000000000000 : ℝ) (770713210069 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell274_denomLower :
    (766218930181 / 10000000000 : ℝ) ≤ Real.exp (338975222308979 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (338975222308979 / 78125000000000 : ℝ) (143151545267 /
    125000000000 : ℝ) (766218930181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell274_product_lower :
    (345689089496479 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (137 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell274_leftExp
    (by norm_num : (0 : ℝ) ≤ (880290221 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell274_product_upper :
    Real.pi * Real.exp (11 / 32 : ℝ) ≤ (886071247994751 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell274_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell274_endpointLower :
    (2686717581 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (137 / 800 : ℝ) (11 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (345689089496479 / 78125000000000 : ℝ) (Real.pi * Real.exp (137 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell274_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 32 : ℝ) - (137 / 1600 : ℝ)) ≤
      (770713210069 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell274_denomUpper
    linarith [hpThetaJensenCell274_product_upper]
  have hi : (1 / (770713210069 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 32 : ℝ) - (137 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (770713210069 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (770713210069 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((137 / 1600 : ℝ) - Real.pi * Real.exp (11 / 32 : ℝ)) := by
    rw [show (137 / 1600 : ℝ) - Real.pi * Real.exp (11 / 32 : ℝ) =
      -(Real.pi * Real.exp (11 / 32 : ℝ) - (137 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (137 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (137 / 400 : ℝ)) := by
    have h := hpThetaJensenCell274_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (770713210069 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell274_endpointUpper :
    hpThetaJensenKernelEndpointUpper (137 / 800 : ℝ) (11 / 64 : ℝ) ≤ (849412053 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 32 : ℝ)) (886071247994751 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell274_product_upper
  have hD : (766218930181 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (137 / 400 : ℝ) - (11 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell274_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell274_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (137 / 400 : ℝ) - (11 / 128 : ℝ)) ≤
      (1 / (766218930181 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (766218930181 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 128 : ℝ) - Real.pi * Real.exp (137 / 400 : ℝ)) ≤
      (2 / (766218930181 / 10000000000 : ℝ) : ℝ) := by
    rw [show (11 / 128 : ℝ) - Real.pi * Real.exp (137 / 400 : ℝ) =
      -(Real.pi * Real.exp (137 / 400 : ℝ) - (11 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (886071247994751 / 200000000000000 : ℝ) ^ 2 - 6 *
      (886071247994751 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell274_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (137 / 800 : ℝ) (11 / 64 : ℝ)) :
    (2686717581 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (849412053 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell274_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell274_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell275_leftExp :
    (14102260349 / 10000000000 : ℝ) ≤ Real.exp (11 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 32 : ℝ) (20216001839 / 20000000000 : ℝ)
    (14102260349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell275_rightExp :
    Real.exp (69 / 200 : ℝ) ≤ (14119899197 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (69 / 200 : ℝ) (1010839577101 / 1000000000000 : ℝ)
    (14119899197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell275_denomUpper :
    Real.exp (43499601478000821 / 10000000000000000 : ℝ) ≤ (774753753009 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43499601478000821 / 10000000000000000 : ℝ) (572804431997
    / 500000000000 : ℝ) (774753753009 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell275_denomLower :
    (770230578353 / 10000000000 : ℝ) ≤ Real.exp (5430131036791951 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5430131036791951 / 1250000000000000 : ℝ) (1145399261151
    / 1000000000000 : ℝ) (770230578353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell275_product_lower :
    (5537943536791951 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell275_leftExp
    (by norm_num : (0 : ℝ) ≤ (14102260349 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell275_product_upper :
    Real.pi * Real.exp (69 / 200 : ℝ) ≤ (44358976478000821 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell275_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell275_endpointLower :
    (6702780913 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 64 : ℝ) (69 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5537943536791951 / 1250000000000000 : ℝ) (Real.pi * Real.exp (11 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell275_product_lower
  have hD : Real.exp (Real.pi * Real.exp (69 / 200 : ℝ) - (11 / 128 : ℝ)) ≤
      (774753753009 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell275_denomUpper
    linarith [hpThetaJensenCell275_product_upper]
  have hi : (1 / (774753753009 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (69 / 200 : ℝ) - (11 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (774753753009 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (774753753009 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 128 : ℝ) - Real.pi * Real.exp (69 / 200 : ℝ)) := by
    rw [show (11 / 128 : ℝ) - Real.pi * Real.exp (69 / 200 : ℝ) =
      -(Real.pi * Real.exp (69 / 200 : ℝ) - (11 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 32 : ℝ)) := by
    have h := hpThetaJensenCell275_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (774753753009 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell275_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 64 : ℝ) (69 / 400 : ℝ) ≤ (1695289589 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (69 / 200 : ℝ)) (44358976478000821 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (69 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell275_product_upper
  have hD : (770230578353 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 32 : ℝ) - (69 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell275_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell275_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 32 : ℝ) - (69 / 800 : ℝ)) ≤
      (1 / (770230578353 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (770230578353 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((69 / 800 : ℝ) - Real.pi * Real.exp (11 / 32 : ℝ)) ≤
      (2 / (770230578353 / 10000000000 : ℝ) : ℝ) := by
    rw [show (69 / 800 : ℝ) - Real.pi * Real.exp (11 / 32 : ℝ) =
      -(Real.pi * Real.exp (11 / 32 : ℝ) - (69 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44358976478000821 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44358976478000821 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell275_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 64 : ℝ) (69 / 400 : ℝ)) :
    (6702780913 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1695289589 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell275_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell275_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell276_leftExp :
    (3529974799 / 2500000000 : ℝ) ≤ Real.exp (69 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (69 / 200 : ℝ) (10108395771 / 10000000000 : ℝ)
    (3529974799 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell276_rightExp :
    Real.exp (277 / 800 : ℝ) ≤ (14137560107 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (277 / 800 : ℝ) (1010879063793 / 1000000000000 : ℝ)
    (14137560107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell276_denomUpper :
    Real.exp (43551959869230451 / 10000000000000000 : ℝ) ≤ (38941043857 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43551959869230451 / 10000000000000000 : ℝ)
    (1145796323821 / 1000000000000 : ℝ) (38941043857 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell276_denomLower :
    (24195893427 / 312500000 : ℝ) ≤ Real.exp (1359166792342501 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1359166792342501 / 312500000000000 : ℝ) (572793219239 /
    500000000000 : ℝ) (24195893427 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell276_product_lower :
    (1386217573592501 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (69 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell276_leftExp
    (by norm_num : (0 : ℝ) ≤ (3529974799 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell276_product_upper :
    Real.pi * Real.exp (277 / 800 : ℝ) ≤ (44414459869230451 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell276_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell276_endpointLower :
    (2675497063 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 400 : ℝ) (277 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1386217573592501 / 312500000000000 : ℝ) (Real.pi * Real.exp (69 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell276_product_lower
  have hD : Real.exp (Real.pi * Real.exp (277 / 800 : ℝ) - (69 / 800 : ℝ)) ≤
      (38941043857 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell276_denomUpper
    linarith [hpThetaJensenCell276_product_upper]
  have hi : (1 / (38941043857 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (277 / 800 : ℝ) - (69 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38941043857 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38941043857 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((69 / 800 : ℝ) - Real.pi * Real.exp (277 / 800 : ℝ)) := by
    rw [show (69 / 800 : ℝ) - Real.pi * Real.exp (277 / 800 : ℝ) =
      -(Real.pi * Real.exp (277 / 800 : ℝ) - (69 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (69 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (69 / 200 : ℝ)) := by
    have h := hpThetaJensenCell276_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38941043857 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell276_endpointUpper :
    hpThetaJensenKernelEndpointUpper (69 / 400 : ℝ) (277 / 1600 : ℝ) ≤ (67669947 / 50000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (277 / 800 : ℝ)) (44414459869230451 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (277 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell276_product_upper
  have hD : (24195893427 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (69 / 200 : ℝ) - (277 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell276_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell276_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (69 / 200 : ℝ) - (277 / 3200 : ℝ)) ≤
      (1 / (24195893427 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (24195893427 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((277 / 3200 : ℝ) - Real.pi * Real.exp (69 / 200 : ℝ)) ≤
      (2 / (24195893427 / 312500000 : ℝ) : ℝ) := by
    rw [show (277 / 3200 : ℝ) - Real.pi * Real.exp (69 / 200 : ℝ) =
      -(Real.pi * Real.exp (69 / 200 : ℝ) - (277 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44414459869230451 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44414459869230451 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell276_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (69 / 400 : ℝ) (277 / 1600 : ℝ)) :
    (2675497063 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (67669947 / 50000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell276_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell276_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell277_leftExp :
    (7068780053 / 5000000000 : ℝ) ≤ Real.exp (277 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (277 / 800 : ℝ) (63179941487 / 62500000000 : ℝ)
    (7068780053 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell277_rightExp :
    Real.exp (139 / 400 : ℝ) ≤ (14155243107 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (139 / 400 : ℝ) (252729638007 / 250000000000 : ℝ)
    (14155243107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell277_denomUpper :
    Real.exp (43604387658249451 / 10000000000000000 : ℝ) ≤ (39145739257 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43604387658249451 / 10000000000000000 : ℝ)
    (1145984062849 / 1000000000000 : ℝ) (39145739257 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell277_denomLower :
    (389166582759 / 5000000000 : ℝ) ≤ Real.exp (2721605983033047 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2721605983033047 / 625000000000000 : ℝ) (286443473643 /
    250000000000 : ℝ) (389166582759 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell277_product_lower :
    (2775902858033047 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (277 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell277_leftExp
    (by norm_num : (0 : ℝ) ≤ (7068780053 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell277_product_upper :
    Real.pi * Real.exp (139 / 400 : ℝ) ≤ (44470012658249451 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell277_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell277_endpointLower :
    (2669871773 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (277 / 1600 : ℝ) (139 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2775902858033047 / 625000000000000 : ℝ) (Real.pi * Real.exp (277 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell277_product_lower
  have hD : Real.exp (Real.pi * Real.exp (139 / 400 : ℝ) - (277 / 3200 : ℝ)) ≤
      (39145739257 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell277_denomUpper
    linarith [hpThetaJensenCell277_product_upper]
  have hi : (1 / (39145739257 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (139 / 400 : ℝ) - (277 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (39145739257 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (39145739257 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((277 / 3200 : ℝ) - Real.pi * Real.exp (139 / 400 : ℝ)) := by
    rw [show (277 / 3200 : ℝ) - Real.pi * Real.exp (139 / 400 : ℝ) =
      -(Real.pi * Real.exp (139 / 400 : ℝ) - (277 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (277 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (277 / 800 : ℝ)) := by
    have h := hpThetaJensenCell277_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (39145739257 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell277_endpointUpper :
    hpThetaJensenKernelEndpointUpper (277 / 1600 : ℝ) (139 / 800 : ℝ) ≤ (105512589 / 78125000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (139 / 400 : ℝ)) (44470012658249451 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (139 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell277_product_upper
  have hD : (389166582759 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (277 / 800 : ℝ) - (139 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell277_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell277_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (277 / 800 : ℝ) - (139 / 1600 : ℝ)) ≤
      (1 / (389166582759 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (389166582759 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((139 / 1600 : ℝ) - Real.pi * Real.exp (277 / 800 : ℝ)) ≤
      (2 / (389166582759 / 5000000000 : ℝ) : ℝ) := by
    rw [show (139 / 1600 : ℝ) - Real.pi * Real.exp (277 / 800 : ℝ) =
      -(Real.pi * Real.exp (277 / 800 : ℝ) - (139 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44470012658249451 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44470012658249451 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell277_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (277 / 1600 : ℝ) (139 / 800 : ℝ)) :
    (2669871773 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (105512589 / 78125000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell277_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell277_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell278_leftExp :
    (7077621553 / 5000000000 : ℝ) ≤ Real.exp (139 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (139 / 400 : ℝ) (1010918552027 / 1000000000000 : ℝ)
    (7077621553 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell278_rightExp :
    Real.exp (279 / 800 : ℝ) ≤ (55363079 / 39062500 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (279 / 800 : ℝ) (202191608361 / 200000000000 : ℝ)
    (55363079 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell278_denomUpper :
    Real.exp (170534706757347 / 39062500000000 : ℝ) ≤ (49189730093 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (170534706757347 / 39062500000000 : ℝ) (1146172081511 /
    1000000000000 : ℝ) (49189730093 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell278_denomLower :
    (782424508463 / 10000000000 : ℝ) ≤ Real.exp (2724882718741547 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2724882718741547 / 625000000000000 : ℝ) (572980814931 /
    500000000000 : ℝ) (782424508463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell278_product_lower :
    (2779374906241547 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (139 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell278_leftExp
    (by norm_num : (0 : ℝ) ≤ (7077621553 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell278_product_upper :
    Real.pi * Real.exp (279 / 800 : ℝ) ≤ (173928261444847 / 39062500000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell278_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell278_endpointLower :
    (3330295741 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (139 / 800 : ℝ) (279 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2779374906241547 / 625000000000000 : ℝ) (Real.pi * Real.exp (139 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell278_product_lower
  have hD : Real.exp (Real.pi * Real.exp (279 / 800 : ℝ) - (139 / 1600 : ℝ)) ≤
      (49189730093 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell278_denomUpper
    linarith [hpThetaJensenCell278_product_upper]
  have hi : (1 / (49189730093 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (279 / 800 : ℝ) - (139 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (49189730093 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (49189730093 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((139 / 1600 : ℝ) - Real.pi * Real.exp (279 / 800 : ℝ)) := by
    rw [show (139 / 1600 : ℝ) - Real.pi * Real.exp (279 / 800 : ℝ) =
      -(Real.pi * Real.exp (279 / 800 : ℝ) - (139 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (139 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (139 / 400 : ℝ)) := by
    have h := hpThetaJensenCell278_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (49189730093 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell278_endpointUpper :
    hpThetaJensenKernelEndpointUpper (139 / 800 : ℝ) (279 / 1600 : ℝ) ≤ (842323949 / 625000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (279 / 800 : ℝ)) (173928261444847 / 39062500000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (279 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell278_product_upper
  have hD : (782424508463 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (139 / 400 : ℝ) - (279 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell278_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell278_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (139 / 400 : ℝ) - (279 / 3200 : ℝ)) ≤
      (1 / (782424508463 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (782424508463 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((279 / 3200 : ℝ) - Real.pi * Real.exp (139 / 400 : ℝ)) ≤
      (2 / (782424508463 / 10000000000 : ℝ) : ℝ) := by
    rw [show (279 / 3200 : ℝ) - Real.pi * Real.exp (139 / 400 : ℝ) =
      -(Real.pi * Real.exp (139 / 400 : ℝ) - (279 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (173928261444847 / 39062500000000 : ℝ) ^ 2 - 6 *
      (173928261444847 / 39062500000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell278_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (139 / 800 : ℝ) (279 / 1600 : ℝ)) :
    (3330295741 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (842323949 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell278_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell278_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell279_leftExp :
    (14172948223 / 10000000000 : ℝ) ≤ Real.exp (279 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (279 / 800 : ℝ) (252739510451 / 250000000000 : ℝ)
    (14172948223 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell279_rightExp :
    Real.exp (7 / 20 : ℝ) ≤ (14190675487 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 20 : ℝ) (1617596053 / 1600000000 : ℝ)
    (14190675487 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell279_denomUpper :
    Real.exp (43709451775230791 / 10000000000000000 : ℝ) ≤ (395591886411 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43709451775230791 / 10000000000000000 : ℝ)
    (1146360380259 / 1000000000000 : ℝ) (395591886411 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell279_denomLower :
    (78654282283 / 1000000000 : ℝ) ≤ Real.exp (5456327594223877 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5456327594223877 / 1250000000000000 : ℝ) (57307482239 /
    50000000000 : ℝ) (78654282283 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell279_product_lower :
    (5565702594223877 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (279 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell279_leftExp
    (by norm_num : (0 : ℝ) ≤ (14172948223 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell279_product_upper :
    Real.pi * Real.exp (7 / 20 : ℝ) ≤ (44581326775230791 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell279_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell279_endpointLower :
    (2658591619 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (279 / 1600 : ℝ) (7 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5565702594223877 / 1250000000000000 : ℝ) (Real.pi * Real.exp (279 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell279_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 20 : ℝ) - (279 / 3200 : ℝ)) ≤
      (395591886411 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell279_denomUpper
    linarith [hpThetaJensenCell279_product_upper]
  have hi : (1 / (395591886411 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 20 : ℝ) - (279 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (395591886411 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (395591886411 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((279 / 3200 : ℝ) - Real.pi * Real.exp (7 / 20 : ℝ)) := by
    rw [show (279 / 3200 : ℝ) - Real.pi * Real.exp (7 / 20 : ℝ) =
      -(Real.pi * Real.exp (7 / 20 : ℝ) - (279 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (279 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (279 / 800 : ℝ)) := by
    have h := hpThetaJensenCell279_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (395591886411 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell279_endpointUpper :
    hpThetaJensenKernelEndpointUpper (279 / 1600 : ℝ) (7 / 40 : ℝ) ≤ (13448705271 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 20 : ℝ)) (44581326775230791 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell279_product_upper
  have hD : (78654282283 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (279 / 800 : ℝ) - (7 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell279_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell279_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (279 / 800 : ℝ) - (7 / 80 : ℝ)) ≤
      (1 / (78654282283 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (78654282283 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 80 : ℝ) - Real.pi * Real.exp (279 / 800 : ℝ)) ≤
      (2 / (78654282283 / 1000000000 : ℝ) : ℝ) := by
    rw [show (7 / 80 : ℝ) - Real.pi * Real.exp (279 / 800 : ℝ) =
      -(Real.pi * Real.exp (279 / 800 : ℝ) - (7 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44581326775230791 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44581326775230791 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell279_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (279 / 1600 : ℝ) (7 / 40 : ℝ)) :
    (2658591619 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13448705271 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell279_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell279_endpointUpper

def hpThetaJensenCellsBatch013Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6910193151 / 5000000000 : ℝ)
  | 1 => (3448279281 / 2500000000 : ℝ)
  | 2 => (3441447687 / 2500000000 : ℝ)
  | 3 => (274768153 / 200000000 : ℝ)
  | 4 => (1371096831 / 1000000000 : ℝ)
  | 5 => (6841736603 / 5000000000 : ℝ)
  | 6 => (853495177 / 625000000 : ℝ)
  | 7 => (13628317663 / 10000000000 : ℝ)
  | 8 => (680032909 / 500000000 : ℝ)
  | 9 => (13572944877 / 10000000000 : ℝ)
  | 10 => (6772589113 / 5000000000 : ℝ)
  | 11 => (13517358717 / 10000000000 : ℝ)
  | 12 => (13489486839 / 10000000000 : ℝ)
  | 13 => (13461563071 / 10000000000 : ℝ)
  | 14 => (2686717581 / 2000000000 : ℝ)
  | 15 => (6702780913 / 5000000000 : ℝ)
  | 16 => (2675497063 / 2000000000 : ℝ)
  | 17 => (2669871773 / 2000000000 : ℝ)
  | 18 => (3330295741 / 2500000000 : ℝ)
  | 19 => (2658591619 / 2000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch013Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13980810567 / 10000000000 : ℝ)
  | 1 => (13953302307 / 10000000000 : ℝ)
  | 2 => (6962868017 / 5000000000 : ℝ)
  | 3 => (6949056117 / 5000000000 : ℝ)
  | 4 => (6935215699 / 5000000000 : ℝ)
  | 5 => (1730336751 / 1250000000 : ℝ)
  | 6 => (6907450273 / 5000000000 : ℝ)
  | 7 => (27574103 / 20000000 : ℝ)
  | 8 => (3439786841 / 2500000000 : ℝ)
  | 9 => (13731188613 / 10000000000 : ℝ)
  | 10 => (13703175747 / 10000000000 : ℝ)
  | 11 => (6837554623 / 5000000000 : ℝ)
  | 12 => (13646989603 / 10000000000 : ℝ)
  | 13 => (13618817307 / 10000000000 : ℝ)
  | 14 => (849412053 / 625000000 : ℝ)
  | 15 => (1695289589 / 1250000000 : ℝ)
  | 16 => (67669947 / 50000000 : ℝ)
  | 17 => (105512589 / 78125000 : ℝ)
  | 18 => (842323949 / 625000000 : ℝ)
  | 19 => (13448705271 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch013_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch013Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch013Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell260_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell261_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell262_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell263_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell264_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell265_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell266_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell267_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell268_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell269_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell270_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell271_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell272_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell273_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell274_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell275_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell276_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell277_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell278_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell279_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper] at h ⊢
    exact h

end HodgeProofHP
