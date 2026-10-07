import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell320_leftExp :
    (233097609 / 156250000 : ℝ) ≤ Real.exp (2 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2 / 5 : ℝ) (50628922577 / 50000000000 : ℝ) (233097609 /
    156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell320_rightExp :
    Real.exp (321 / 800 : ℝ) ≤ (2987381289 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (321 / 800 : ℝ) (1012618006159 / 1000000000000 : ℝ)
    (2987381289 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell320_denomUpper :
    Real.exp (9185136145853377 / 2000000000000000 : ℝ) ≤ (123434620133 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9185136145853377 / 2000000000000000 : ℝ) (577163651283 /
    500000000000 : ℝ) (123434620133 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell320_denomLower :
    (39255882417 / 400000000 : ℝ) ≤ Real.exp (44788984720533 / 9765625000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (44788984720533 / 9765625000000 : ℝ) (1154104537539 /
    1000000000000 : ℝ) (39255882417 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell320_product_lower :
    (91537197956691 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (2 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell320_leftExp
    (by norm_num : (0 : ℝ) ≤ (233097609 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell320_product_upper :
    Real.pi * Real.exp (321 / 800 : ℝ) ≤ (9385136145853377 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell320_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell320_endpointLower :
    (151245479 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 5 : ℝ) (321 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (91537197956691 / 19531250000000 : ℝ) (Real.pi * Real.exp (2 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell320_product_lower
  have hD : Real.exp (Real.pi * Real.exp (321 / 800 : ℝ) - (1 / 10 : ℝ)) ≤
      (123434620133 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell320_denomUpper
    linarith [hpThetaJensenCell320_product_upper]
  have hi : (1 / (123434620133 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (321 / 800 : ℝ) - (1 / 10 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (123434620133 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (123434620133 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 10 : ℝ) - Real.pi * Real.exp (321 / 800 : ℝ)) := by
    rw [show (1 / 10 : ℝ) - Real.pi * Real.exp (321 / 800 : ℝ) =
      -(Real.pi * Real.exp (321 / 800 : ℝ) - (1 / 10 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (2 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (2 / 5 : ℝ)) := by
    have h := hpThetaJensenCell320_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (123434620133 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell320_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 5 : ℝ) (321 / 1600 : ℝ) ≤ (12244419637 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (321 / 800 : ℝ)) (9385136145853377 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (321 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell320_product_upper
  have hD : (39255882417 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (2 / 5 : ℝ) - (321 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell320_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell320_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (2 / 5 : ℝ) - (321 / 3200 : ℝ)) ≤
      (1 / (39255882417 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (39255882417 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((321 / 3200 : ℝ) - Real.pi * Real.exp (2 / 5 : ℝ)) ≤
      (2 / (39255882417 / 400000000 : ℝ) : ℝ) := by
    rw [show (321 / 3200 : ℝ) - Real.pi * Real.exp (2 / 5 : ℝ) =
      -(Real.pi * Real.exp (2 / 5 : ℝ) - (321 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9385136145853377 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (9385136145853377 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell320_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 5 : ℝ) (321 / 1600 : ℝ)) :
    (151245479 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12244419637 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell320_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell320_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell321_leftExp :
    (3734226611 / 2500000000 : ℝ) ≤ Real.exp (321 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (321 / 800 : ℝ) (506309003079 / 500000000000 : ℝ)
    (3734226611 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell321_rightExp :
    Real.exp (161 / 400 : ℝ) ≤ (14955589253 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (161 / 400 : ℝ) (1012657562323 / 1000000000000 : ℝ)
    (14955589253 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell321_denomUpper :
    Real.exp (45981249508100029 / 10000000000000000 : ℝ) ≤ (39719180973 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (45981249508100029 / 10000000000000000 : ℝ)
    (1154527771717 / 1000000000000 : ℝ) (39719180973 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell321_denomLower :
    (493429253191 / 5000000000 : ℝ) ≤ Real.exp (1434981743413089 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1434981743413089 / 312500000000000 : ℝ) (577152351719 /
    500000000000 : ℝ) (493429253191 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell321_product_lower :
    (1466427055913089 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (321 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell321_leftExp
    (by norm_num : (0 : ℝ) ≤ (3734226611 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell321_product_upper :
    Real.pi * Real.exp (161 / 400 : ℝ) ≤ (46984374508100029 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell321_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell321_endpointLower :
    (482792029 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (321 / 1600 : ℝ) (161 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1466427055913089 / 312500000000000 : ℝ) (Real.pi * Real.exp (321 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell321_product_lower
  have hD : Real.exp (Real.pi * Real.exp (161 / 400 : ℝ) - (321 / 3200 : ℝ)) ≤
      (39719180973 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell321_denomUpper
    linarith [hpThetaJensenCell321_product_upper]
  have hi : (1 / (39719180973 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (161 / 400 : ℝ) - (321 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (39719180973 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (39719180973 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((321 / 3200 : ℝ) - Real.pi * Real.exp (161 / 400 : ℝ)) := by
    rw [show (321 / 3200 : ℝ) - Real.pi * Real.exp (161 / 400 : ℝ) =
      -(Real.pi * Real.exp (161 / 400 : ℝ) - (321 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (321 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (321 / 800 : ℝ)) := by
    have h := hpThetaJensenCell321_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (39719180973 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell321_endpointUpper :
    hpThetaJensenKernelEndpointUpper (321 / 1600 : ℝ) (161 / 800 : ℝ) ≤ (2442860283 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (161 / 400 : ℝ)) (46984374508100029 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (161 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell321_product_upper
  have hD : (493429253191 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (321 / 800 : ℝ) - (161 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell321_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell321_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (321 / 800 : ℝ) - (161 / 1600 : ℝ)) ≤
      (1 / (493429253191 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (493429253191 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((161 / 1600 : ℝ) - Real.pi * Real.exp (321 / 800 : ℝ)) ≤
      (2 / (493429253191 / 5000000000 : ℝ) : ℝ) := by
    rw [show (161 / 1600 : ℝ) - Real.pi * Real.exp (321 / 800 : ℝ) =
      -(Real.pi * Real.exp (321 / 800 : ℝ) - (161 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46984374508100029 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (46984374508100029 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell321_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (321 / 1600 : ℝ) (161 / 800 : ℝ)) :
    (482792029 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2442860283 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell321_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell321_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell322_leftExp :
    (3738897313 / 2500000000 : ℝ) ≤ Real.exp (161 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (161 / 400 : ℝ) (506328781161 / 500000000000 : ℝ)
    (3738897313 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell322_rightExp :
    Real.exp (323 / 800 : ℝ) ≤ (14974295429 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (323 / 800 : ℝ) (31646785001 / 31250000000 : ℝ)
    (14974295429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell322_denomUpper :
    Real.exp (46036891699678397 / 10000000000000000 : ℝ) ≤ (998520080161 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46036891699678397 / 10000000000000000 : ℝ) (230945708119
    / 200000000000 : ℝ) (998520080161 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell322_denomLower :
    (992357621549 / 10000000000 : ℝ) ≤ Real.exp (1436718267167787 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1436718267167787 / 312500000000000 : ℝ) (1154505168597 /
    1000000000000 : ℝ) (992357621549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell322_product_lower :
    (1468261235917787 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (161 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell322_leftExp
    (by norm_num : (0 : ℝ) ≤ (3738897313 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell322_product_upper :
    Real.pi * Real.exp (323 / 800 : ℝ) ≤ (47043141699678397 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell322_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell322_endpointLower :
    (12039935331 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (161 / 800 : ℝ) (323 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1468261235917787 / 312500000000000 : ℝ) (Real.pi * Real.exp (161 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell322_product_lower
  have hD : Real.exp (Real.pi * Real.exp (323 / 800 : ℝ) - (161 / 1600 : ℝ)) ≤
      (998520080161 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell322_denomUpper
    linarith [hpThetaJensenCell322_product_upper]
  have hi : (1 / (998520080161 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (323 / 800 : ℝ) - (161 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (998520080161 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (998520080161 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((161 / 1600 : ℝ) - Real.pi * Real.exp (323 / 800 : ℝ)) := by
    rw [show (161 / 1600 : ℝ) - Real.pi * Real.exp (323 / 800 : ℝ) =
      -(Real.pi * Real.exp (323 / 800 : ℝ) - (161 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (161 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (161 / 400 : ℝ)) := by
    have h := hpThetaJensenCell322_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (998520080161 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell322_endpointUpper :
    hpThetaJensenKernelEndpointUpper (161 / 800 : ℝ) (323 / 1600 : ℝ) ≤ (12184154821 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (323 / 800 : ℝ)) (47043141699678397 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (323 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell322_product_upper
  have hD : (992357621549 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (161 / 400 : ℝ) - (323 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell322_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell322_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (161 / 400 : ℝ) - (323 / 3200 : ℝ)) ≤
      (1 / (992357621549 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (992357621549 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((323 / 3200 : ℝ) - Real.pi * Real.exp (161 / 400 : ℝ)) ≤
      (2 / (992357621549 / 10000000000 : ℝ) : ℝ) := by
    rw [show (323 / 3200 : ℝ) - Real.pi * Real.exp (161 / 400 : ℝ) =
      -(Real.pi * Real.exp (161 / 400 : ℝ) - (323 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47043141699678397 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47043141699678397 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell322_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (161 / 800 : ℝ) (323 / 1600 : ℝ)) :
    (12039935331 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12184154821 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell322_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell322_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell323_leftExp :
    (14974295427 / 10000000000 : ℝ) ≤ Real.exp (323 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (323 / 800 : ℝ) (1012697120031 / 1000000000000 : ℝ)
    (14974295427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell323_rightExp :
    Real.exp (81 / 200 : ℝ) ≤ (14993025001 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81 / 200 : ℝ) (202547335857 / 200000000000 : ℝ)
    (14993025001 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell323_denomUpper :
    Real.exp (46092607391966593 / 10000000000000000 : ℝ) ≤ (1004098930949 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46092607391966593 / 10000000000000000 : ℝ)
    (1154929609661 / 1000000000000 : ℝ) (1004098930949 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell323_denomLower :
    (997894705169 / 10000000000 : ℝ) ≤ Real.exp (5753828339887473 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5753828339887473 / 1250000000000000 : ℝ) (577352966733 /
    500000000000 : ℝ) (997894705169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell323_product_lower :
    (5880390839887473 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (323 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell323_leftExp
    (by norm_num : (0 : ℝ) ≤ (14974295427 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell323_product_upper :
    Real.pi * Real.exp (81 / 200 : ℝ) ≤ (47101982391966593 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell323_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell323_endpointLower :
    (1201004263 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (323 / 1600 : ℝ) (81 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5880390839887473 / 1250000000000000 : ℝ) (Real.pi * Real.exp (323 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell323_product_lower
  have hD : Real.exp (Real.pi * Real.exp (81 / 200 : ℝ) - (323 / 3200 : ℝ)) ≤
      (1004098930949 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell323_denomUpper
    linarith [hpThetaJensenCell323_product_upper]
  have hi : (1 / (1004098930949 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (81 / 200 : ℝ) - (323 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1004098930949 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1004098930949 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((323 / 3200 : ℝ) - Real.pi * Real.exp (81 / 200 : ℝ)) := by
    rw [show (323 / 3200 : ℝ) - Real.pi * Real.exp (81 / 200 : ℝ) =
      -(Real.pi * Real.exp (81 / 200 : ℝ) - (323 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (323 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (323 / 800 : ℝ)) := by
    have h := hpThetaJensenCell323_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1004098930949 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell323_endpointUpper :
    hpThetaJensenKernelEndpointUpper (323 / 1600 : ℝ) (81 / 400 : ℝ) ≤ (2430796071 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (81 / 200 : ℝ)) (47101982391966593 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (81 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell323_product_upper
  have hD : (997894705169 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (323 / 800 : ℝ) - (81 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell323_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell323_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (323 / 800 : ℝ) - (81 / 800 : ℝ)) ≤
      (1 / (997894705169 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (997894705169 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((81 / 800 : ℝ) - Real.pi * Real.exp (323 / 800 : ℝ)) ≤
      (2 / (997894705169 / 10000000000 : ℝ) : ℝ) := by
    rw [show (81 / 800 : ℝ) - Real.pi * Real.exp (323 / 800 : ℝ) =
      -(Real.pi * Real.exp (323 / 800 : ℝ) - (81 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47101982391966593 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47101982391966593 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell323_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (323 / 1600 : ℝ) (81 / 400 : ℝ)) :
    (1201004263 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2430796071 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell323_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell323_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell324_leftExp :
    (599721 / 400000 : ℝ) ≤ Real.exp (81 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (81 / 200 : ℝ) (253184169821 / 250000000000 : ℝ) (599721
    / 400000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell324_rightExp :
    Real.exp (13 / 32 : ℝ) ≤ (15011778001 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 32 : ℝ) (202555248017 / 200000000000 : ℝ)
    (15011778001 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell324_denomUpper :
    Real.exp (46148396685495593 / 10000000000000000 : ℝ) ≤ (1009716383079 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46148396685495593 / 10000000000000000 : ℝ) (36097843107
    / 31250000000 : ℝ) (1009716383079 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell324_denomLower :
    (501735030171 / 5000000000 : ℝ) ≤ Real.exp (230431711979 / 50000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (230431711979 / 50000000000 : ℝ) (1154906998539 /
    1000000000000 : ℝ) (501735030171 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell324_product_lower :
    (235509836979 / 50000000000 : ℝ) ≤ Real.pi * Real.exp (81 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell324_leftExp
    (by norm_num : (0 : ℝ) ≤ (599721 / 400000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell324_product_upper :
    Real.pi * Real.exp (13 / 32 : ℝ) ≤ (47160896685495593 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell324_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell324_endpointLower :
    (11980123107 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 400 : ℝ) (13 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (235509836979 / 50000000000 : ℝ) (Real.pi * Real.exp (81 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell324_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 32 : ℝ) - (81 / 800 : ℝ)) ≤
      (1009716383079 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell324_denomUpper
    linarith [hpThetaJensenCell324_product_upper]
  have hi : (1 / (1009716383079 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 32 : ℝ) - (81 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1009716383079 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1009716383079 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((81 / 800 : ℝ) - Real.pi * Real.exp (13 / 32 : ℝ)) := by
    rw [show (81 / 800 : ℝ) - Real.pi * Real.exp (13 / 32 : ℝ) =
      -(Real.pi * Real.exp (13 / 32 : ℝ) - (81 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (81 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (81 / 200 : ℝ)) := by
    have h := hpThetaJensenCell324_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1009716383079 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell324_endpointUpper :
    hpThetaJensenKernelEndpointUpper (81 / 400 : ℝ) (13 / 64 : ℝ) ≤ (2424755703 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 32 : ℝ)) (47160896685495593 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell324_product_upper
  have hD : (501735030171 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (81 / 200 : ℝ) - (13 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell324_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell324_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (81 / 200 : ℝ) - (13 / 128 : ℝ)) ≤
      (1 / (501735030171 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (501735030171 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 128 : ℝ) - Real.pi * Real.exp (81 / 200 : ℝ)) ≤
      (2 / (501735030171 / 5000000000 : ℝ) : ℝ) := by
    rw [show (13 / 128 : ℝ) - Real.pi * Real.exp (81 / 200 : ℝ) =
      -(Real.pi * Real.exp (81 / 200 : ℝ) - (13 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47160896685495593 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47160896685495593 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell324_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (81 / 400 : ℝ) (13 / 64 : ℝ)) :
    (11980123107 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2424755703 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell324_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell324_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell325_leftExp :
    (15011777999 / 10000000000 : ℝ) ≤ Real.exp (13 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 32 : ℝ) (253194060021 / 250000000000 : ℝ)
    (15011777999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell325_rightExp :
    Real.exp (163 / 400 : ℝ) ≤ (1878819307 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (163 / 400 : ℝ) (1012815802429 / 1000000000000 : ℝ)
    (1878819307 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell325_denomUpper :
    Real.exp (5775532458136051 / 1250000000000000 : ℝ) ≤ (126921592997 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5775532458136051 / 1250000000000000 : ℝ) (1155332650333
    / 1000000000000 : ℝ) (126921592997 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell325_denomLower :
    (63067749501 / 625000000 : ℝ) ≤ Real.exp (5767766458429301 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5767766458429301 / 1250000000000000 : ℝ) (28877709107 /
    25000000000 : ℝ) (63067749501 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell325_product_lower :
    (5895110208429301 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell325_leftExp
    (by norm_num : (0 : ℝ) ≤ (15011777999 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell325_product_upper :
    Real.pi * Real.exp (163 / 400 : ℝ) ≤ (5902485583136051 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell325_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell325_endpointLower :
    (11950177261 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 64 : ℝ) (163 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5895110208429301 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell325_product_lower
  have hD : Real.exp (Real.pi * Real.exp (163 / 400 : ℝ) - (13 / 128 : ℝ)) ≤
      (126921592997 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell325_denomUpper
    linarith [hpThetaJensenCell325_product_upper]
  have hi : (1 / (126921592997 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (163 / 400 : ℝ) - (13 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (126921592997 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (126921592997 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 128 : ℝ) - Real.pi * Real.exp (163 / 400 : ℝ)) := by
    rw [show (13 / 128 : ℝ) - Real.pi * Real.exp (163 / 400 : ℝ) =
      -(Real.pi * Real.exp (163 / 400 : ℝ) - (13 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 32 : ℝ)) := by
    have h := hpThetaJensenCell325_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (126921592997 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell325_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 64 : ℝ) (163 / 800 : ℝ) ≤ (3023387449 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (163 / 400 : ℝ)) (5902485583136051 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (163 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell325_product_upper
  have hD : (63067749501 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 32 : ℝ) - (163 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell325_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell325_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 32 : ℝ) - (163 / 1600 : ℝ)) ≤
      (1 / (63067749501 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (63067749501 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((163 / 1600 : ℝ) - Real.pi * Real.exp (13 / 32 : ℝ)) ≤
      (2 / (63067749501 / 625000000 : ℝ) : ℝ) := by
    rw [show (163 / 1600 : ℝ) - Real.pi * Real.exp (13 / 32 : ℝ) =
      -(Real.pi * Real.exp (13 / 32 : ℝ) - (163 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5902485583136051 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (5902485583136051 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell325_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 64 : ℝ) (163 / 800 : ℝ)) :
    (11950177261 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3023387449 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell325_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell325_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell326_leftExp :
    (3006110891 / 2000000000 : ℝ) ≤ Real.exp (163 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (163 / 400 : ℝ) (253203950607 / 250000000000 : ℝ)
    (3006110891 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell326_rightExp :
    Real.exp (327 / 800 : ℝ) ≤ (15049354397 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (327 / 800 : ℝ) (1012855366319 / 1000000000000 : ℝ)
    (15049354397 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell326_denomUpper :
    Real.exp (46260196428134421 / 10000000000000000 : ℝ) ≤ (1021068325221 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46260196428134421 / 10000000000000000 : ℝ) (144441827861
    / 125000000000 : ℝ) (1021068325221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell326_denomLower :
    (1014736808737 / 10000000000 : ℝ) ≤ Real.exp (1154949865784809 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1154949865784809 / 250000000000000 : ℝ) (231062006237 /
    200000000000 : ℝ) (1014736808737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell326_product_lower :
    (1180496740784809 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (163 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell326_leftExp
    (by norm_num : (0 : ℝ) ≤ (3006110891 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell326_product_upper :
    Real.pi * Real.exp (327 / 800 : ℝ) ≤ (47278946428134421 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell326_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell326_endpointLower :
    (596010279 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (163 / 800 : ℝ) (327 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1180496740784809 / 250000000000000 : ℝ) (Real.pi * Real.exp (163 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell326_product_lower
  have hD : Real.exp (Real.pi * Real.exp (327 / 800 : ℝ) - (163 / 1600 : ℝ)) ≤
      (1021068325221 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell326_denomUpper
    linarith [hpThetaJensenCell326_product_upper]
  have hi : (1 / (1021068325221 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (327 / 800 : ℝ) - (163 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1021068325221 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1021068325221 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((163 / 1600 : ℝ) - Real.pi * Real.exp (327 / 800 : ℝ)) := by
    rw [show (163 / 1600 : ℝ) - Real.pi * Real.exp (327 / 800 : ℝ) =
      -(Real.pi * Real.exp (327 / 800 : ℝ) - (163 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (163 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (163 / 400 : ℝ)) := by
    have h := hpThetaJensenCell326_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1021068325221 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell326_endpointUpper :
    hpThetaJensenKernelEndpointUpper (163 / 800 : ℝ) (327 / 1600 : ℝ) ≤ (1206329469 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (327 / 800 : ℝ)) (47278946428134421 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (327 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell326_product_upper
  have hD : (1014736808737 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (163 / 400 : ℝ) - (327 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell326_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell326_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (163 / 400 : ℝ) - (327 / 3200 : ℝ)) ≤
      (1 / (1014736808737 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1014736808737 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((327 / 3200 : ℝ) - Real.pi * Real.exp (163 / 400 : ℝ)) ≤
      (2 / (1014736808737 / 10000000000 : ℝ) : ℝ) := by
    rw [show (327 / 3200 : ℝ) - Real.pi * Real.exp (163 / 400 : ℝ) =
      -(Real.pi * Real.exp (163 / 400 : ℝ) - (327 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47278946428134421 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47278946428134421 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell326_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (163 / 800 : ℝ) (327 / 1600 : ℝ)) :
    (596010279 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1206329469 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell326_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell326_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell327_leftExp :
    (3009870879 / 2000000000 : ℝ) ≤ Real.exp (327 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (327 / 800 : ℝ) (506427683159 / 500000000000 : ℝ)
    (3009870879 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell327_rightExp :
    Real.exp (41 / 100 : ℝ) ≤ (3767044463 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 100 : ℝ) (202578986351 / 200000000000 : ℝ)
    (3767044463 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell327_denomUpper :
    Real.exp (11579051765649559 / 2500000000000000 : ℝ) ≤ (51340172003 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11579051765649559 / 2500000000000000 : ℝ) (23114737951 /
    20000000000 : ℝ) (51340172003 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell327_denomLower :
    (204085764109 / 2000000000 : ℝ) ≤ Real.exp (1156348284312421 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1156348284312421 / 250000000000000 : ℝ) (577755999853 /
    500000000000 : ℝ) (204085764109 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell327_product_lower :
    (1181973284312421 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (327 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell327_leftExp
    (by norm_num : (0 : ℝ) ≤ (3009870879 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell327_product_upper :
    Real.pi * Real.exp (41 / 100 : ℝ) ≤ (11834520515649559 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell327_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell327_endpointLower :
    (2972552139 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (327 / 1600 : ℝ) (41 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1181973284312421 / 250000000000000 : ℝ) (Real.pi * Real.exp (327 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell327_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 100 : ℝ) - (327 / 3200 : ℝ)) ≤
      (51340172003 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell327_denomUpper
    linarith [hpThetaJensenCell327_product_upper]
  have hi : (1 / (51340172003 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 100 : ℝ) - (327 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51340172003 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51340172003 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((327 / 3200 : ℝ) - Real.pi * Real.exp (41 / 100 : ℝ)) := by
    rw [show (327 / 3200 : ℝ) - Real.pi * Real.exp (41 / 100 : ℝ) =
      -(Real.pi * Real.exp (41 / 100 : ℝ) - (327 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (327 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (327 / 800 : ℝ)) := by
    have h := hpThetaJensenCell327_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51340172003 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell327_endpointUpper :
    hpThetaJensenKernelEndpointUpper (327 / 1600 : ℝ) (41 / 200 : ℝ) ≤ (12033013701 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 100 : ℝ)) (11834520515649559 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell327_product_upper
  have hD : (204085764109 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (327 / 800 : ℝ) - (41 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell327_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell327_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (327 / 800 : ℝ) - (41 / 400 : ℝ)) ≤
      (1 / (204085764109 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (204085764109 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 400 : ℝ) - Real.pi * Real.exp (327 / 800 : ℝ)) ≤
      (2 / (204085764109 / 2000000000 : ℝ) : ℝ) := by
    rw [show (41 / 400 : ℝ) - Real.pi * Real.exp (327 / 800 : ℝ) =
      -(Real.pi * Real.exp (327 / 800 : ℝ) - (41 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11834520515649559 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (11834520515649559 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell327_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (327 / 1600 : ℝ) (41 / 200 : ℝ)) :
    (2972552139 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12033013701 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell327_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell327_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell328_leftExp :
    (15068177851 / 10000000000 : ℝ) ≤ Real.exp (41 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 100 : ℝ) (506447465877 / 500000000000 : ℝ)
    (15068177851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell328_rightExp :
    Real.exp (329 / 800 : ℝ) ≤ (15087024851 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (329 / 800 : ℝ) (63308406171 / 62500000000 : ℝ)
    (15087024851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell328_denomUpper :
    Real.exp (46372291662727643 / 10000000000000000 : ℝ) ≤ (6453615033 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46372291662727643 / 10000000000000000 : ℝ)
    (1155939474807 / 1000000000000 : ℝ) (6453615033 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell328_denomLower :
    (1026160341841 / 10000000000 : ℝ) ≤ Real.exp (5788742748909849 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5788742748909849 / 1250000000000000 : ℝ) (72232141897 /
    62500000000 : ℝ) (1026160341841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell328_product_lower :
    (5917258373909849 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell328_leftExp
    (by norm_num : (0 : ℝ) ≤ (15068177851 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell328_product_upper :
    Real.pi * Real.exp (329 / 800 : ℝ) ≤ (47397291662727643 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell328_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell328_endpointLower :
    (2965046671 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 200 : ℝ) (329 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5917258373909849 / 1250000000000000 : ℝ) (Real.pi * Real.exp (41 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell328_product_lower
  have hD : Real.exp (Real.pi * Real.exp (329 / 800 : ℝ) - (41 / 400 : ℝ)) ≤
      (6453615033 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell328_denomUpper
    linarith [hpThetaJensenCell328_product_upper]
  have hi : (1 / (6453615033 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (329 / 800 : ℝ) - (41 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6453615033 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6453615033 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 400 : ℝ) - Real.pi * Real.exp (329 / 800 : ℝ)) := by
    rw [show (41 / 400 : ℝ) - Real.pi * Real.exp (329 / 800 : ℝ) =
      -(Real.pi * Real.exp (329 / 800 : ℝ) - (41 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 100 : ℝ)) := by
    have h := hpThetaJensenCell328_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6453615033 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell328_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 200 : ℝ) (329 / 1600 : ℝ) ≤ (6001353657 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (329 / 800 : ℝ)) (47397291662727643 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (329 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell328_product_upper
  have hD : (1026160341841 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 100 : ℝ) - (329 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell328_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell328_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 100 : ℝ) - (329 / 3200 : ℝ)) ≤
      (1 / (1026160341841 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1026160341841 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((329 / 3200 : ℝ) - Real.pi * Real.exp (41 / 100 : ℝ)) ≤
      (2 / (1026160341841 / 10000000000 : ℝ) : ℝ) := by
    rw [show (329 / 3200 : ℝ) - Real.pi * Real.exp (41 / 100 : ℝ) =
      -(Real.pi * Real.exp (41 / 100 : ℝ) - (329 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47397291662727643 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47397291662727643 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell328_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 200 : ℝ) (329 / 1600 : ℝ)) :
    (2965046671 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6001353657 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell328_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell328_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell329_leftExp :
    (301740497 / 200000000 : ℝ) ≤ Real.exp (329 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (329 / 800 : ℝ) (202586899747 / 200000000000 : ℝ)
    (301740497 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell329_rightExp :
    Real.exp (33 / 80 : ℝ) ≤ (14751851 / 9765625 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 80 : ℝ) (506487033631 / 500000000000 : ℝ)
    (14751851 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell329_denomUpper :
    Real.exp (90680567036661 / 19531250000000 : ℝ) ≤ (1038393540491 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (90680567036661 / 19531250000000 : ℝ) (1156142355147 /
    1000000000000 : ℝ) (1038393540491 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell329_denomLower :
    (515965844099 / 5000000000 : ℝ) ≤ Real.exp (115915066431403 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (115915066431403 / 25000000000000 : ℝ) (46236673743 /
    40000000000 : ℝ) (515965844099 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell329_product_lower :
    (118493191431403 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (329 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell329_leftExp
    (by norm_num : (0 : ℝ) ≤ (301740497 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell329_product_upper :
    Real.pi * Real.exp (33 / 80 : ℝ) ≤ (46344311838643 / 9765625000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell329_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell329_endpointLower :
    (5915070223 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (329 / 1600 : ℝ) (33 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (118493191431403 / 25000000000000 : ℝ) (Real.pi * Real.exp (329 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell329_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 80 : ℝ) - (329 / 3200 : ℝ)) ≤
      (1038393540491 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell329_denomUpper
    linarith [hpThetaJensenCell329_product_upper]
  have hi : (1 / (1038393540491 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 80 : ℝ) - (329 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1038393540491 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1038393540491 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((329 / 3200 : ℝ) - Real.pi * Real.exp (33 / 80 : ℝ)) := by
    rw [show (329 / 3200 : ℝ) - Real.pi * Real.exp (33 / 80 : ℝ) =
      -(Real.pi * Real.exp (33 / 80 : ℝ) - (329 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (329 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (329 / 800 : ℝ)) := by
    have h := hpThetaJensenCell329_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1038393540491 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell329_endpointUpper :
    hpThetaJensenKernelEndpointUpper (329 / 1600 : ℝ) (33 / 160 : ℝ) ≤ (2993094009 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 80 : ℝ)) (46344311838643 / 9765625000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell329_product_upper
  have hD : (515965844099 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (329 / 800 : ℝ) - (33 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell329_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell329_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (329 / 800 : ℝ) - (33 / 320 : ℝ)) ≤
      (1 / (515965844099 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (515965844099 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 320 : ℝ) - Real.pi * Real.exp (329 / 800 : ℝ)) ≤
      (2 / (515965844099 / 5000000000 : ℝ) : ℝ) := by
    rw [show (33 / 320 : ℝ) - Real.pi * Real.exp (329 / 800 : ℝ) =
      -(Real.pi * Real.exp (329 / 800 : ℝ) - (33 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46344311838643 / 9765625000000 : ℝ) ^ 2 - 6 *
      (46344311838643 / 9765625000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell329_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (329 / 1600 : ℝ) (33 / 160 : ℝ)) :
    (5915070223 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2993094009 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell329_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell329_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell330_leftExp :
    (7552947711 / 5000000000 : ℝ) ≤ Real.exp (33 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 80 : ℝ) (1012974067261 / 1000000000000 : ℝ)
    (7552947711 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell330_rightExp :
    Real.exp (331 / 800 : ℝ) ≤ (18905987 / 12500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (331 / 800 : ℝ) (202602727467 / 200000000000 : ℝ)
    (18905987 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell330_denomUpper :
    Real.exp (58105853917291 / 12500000000000 : ℝ) ≤ (1044249167737 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58105853917291 / 12500000000000 : ℝ) (289086384761 /
    250000000000 : ℝ) (1044249167737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell330_denomLower :
    (1037743178989 / 10000000000 : ℝ) ≤ Real.exp (2901386575661989 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2901386575661989 / 625000000000000 : ℝ) (578059859931 /
    500000000000 : ℝ) (1037743178989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell330_product_lower :
    (2966035013161989 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell330_leftExp
    (by norm_num : (0 : ℝ) ≤ (7552947711 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell330_product_upper :
    Real.pi * Real.exp (331 / 800 : ℝ) ≤ (59394916417291 / 12500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell330_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell330_endpointLower :
    (11800070339 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 160 : ℝ) (331 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2966035013161989 / 625000000000000 : ℝ) (Real.pi * Real.exp (33 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell330_product_lower
  have hD : Real.exp (Real.pi * Real.exp (331 / 800 : ℝ) - (33 / 320 : ℝ)) ≤
      (1044249167737 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell330_denomUpper
    linarith [hpThetaJensenCell330_product_upper]
  have hi : (1 / (1044249167737 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (331 / 800 : ℝ) - (33 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1044249167737 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1044249167737 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 320 : ℝ) - Real.pi * Real.exp (331 / 800 : ℝ)) := by
    rw [show (33 / 320 : ℝ) - Real.pi * Real.exp (331 / 800 : ℝ) =
      -(Real.pi * Real.exp (331 / 800 : ℝ) - (33 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 80 : ℝ)) := by
    have h := hpThetaJensenCell330_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1044249167737 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell330_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 160 : ℝ) (331 / 1600 : ℝ) ≤ (11942020357 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (331 / 800 : ℝ)) (59394916417291 / 12500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (331 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell330_product_upper
  have hD : (1037743178989 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 80 : ℝ) - (331 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell330_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell330_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 80 : ℝ) - (331 / 3200 : ℝ)) ≤
      (1 / (1037743178989 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1037743178989 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((331 / 3200 : ℝ) - Real.pi * Real.exp (33 / 80 : ℝ)) ≤
      (2 / (1037743178989 / 10000000000 : ℝ) : ℝ) := by
    rw [show (331 / 3200 : ℝ) - Real.pi * Real.exp (33 / 80 : ℝ) =
      -(Real.pi * Real.exp (33 / 80 : ℝ) - (331 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59394916417291 / 12500000000000 : ℝ) ^ 2 - 6 *
      (59394916417291 / 12500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell330_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 160 : ℝ) (331 / 1600 : ℝ)) :
    (11800070339 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11942020357 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell330_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell330_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell331_leftExp :
    (7562394799 / 5000000000 : ℝ) ≤ Real.exp (331 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (331 / 800 : ℝ) (506506818667 / 500000000000 : ℝ)
    (7562394799 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell331_rightExp :
    Real.exp (83 / 200 : ℝ) ≤ (946481713 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83 / 200 : ℝ) (1013053208953 / 1000000000000 : ℝ)
    (946481713 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell331_denomUpper :
    Real.exp (2908811886688809 / 625000000000000 : ℝ) ≤ (1050145612077 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2908811886688809 / 625000000000000 : ℝ) (1156549026977 /
    1000000000000 : ℝ) (1050145612077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell331_denomLower :
    (1043595136833 / 10000000000 : ℝ) ≤ Real.exp (2904901125172501 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2904901125172501 / 625000000000000 : ℝ) (578161449857 /
    500000000000 : ℝ) (1043595136833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell331_product_lower :
    (2969744875172501 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (331 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell331_leftExp
    (by norm_num : (0 : ℝ) ≤ (7562394799 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell331_product_upper :
    Real.pi * Real.exp (83 / 200 : ℝ) ≤ (2973460324188809 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell331_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell331_endpointLower :
    (2353995371 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (331 / 1600 : ℝ) (83 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2969744875172501 / 625000000000000 : ℝ) (Real.pi * Real.exp (331 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell331_product_lower
  have hD : Real.exp (Real.pi * Real.exp (83 / 200 : ℝ) - (331 / 3200 : ℝ)) ≤
      (1050145612077 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell331_denomUpper
    linarith [hpThetaJensenCell331_product_upper]
  have hi : (1 / (1050145612077 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (83 / 200 : ℝ) - (331 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1050145612077 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1050145612077 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((331 / 3200 : ℝ) - Real.pi * Real.exp (83 / 200 : ℝ)) := by
    rw [show (331 / 3200 : ℝ) - Real.pi * Real.exp (83 / 200 : ℝ) =
      -(Real.pi * Real.exp (83 / 200 : ℝ) - (331 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (331 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (331 / 800 : ℝ)) := by
    have h := hpThetaJensenCell331_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1050145612077 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell331_endpointUpper :
    hpThetaJensenKernelEndpointUpper (331 / 1600 : ℝ) (83 / 400 : ℝ) ≤ (11911640767 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (83 / 200 : ℝ)) (2973460324188809 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (83 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell331_product_upper
  have hD : (1043595136833 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (331 / 800 : ℝ) - (83 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell331_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell331_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (331 / 800 : ℝ) - (83 / 800 : ℝ)) ≤
      (1 / (1043595136833 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1043595136833 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((83 / 800 : ℝ) - Real.pi * Real.exp (331 / 800 : ℝ)) ≤
      (2 / (1043595136833 / 10000000000 : ℝ) : ℝ) := by
    rw [show (83 / 800 : ℝ) - Real.pi * Real.exp (331 / 800 : ℝ) =
      -(Real.pi * Real.exp (331 / 800 : ℝ) - (83 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2973460324188809 / 625000000000000 : ℝ) ^ 2 - 6 *
      (2973460324188809 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell331_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (331 / 1600 : ℝ) (83 / 400 : ℝ)) :
    (2353995371 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11911640767 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell331_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell331_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell332_leftExp :
    (7571853703 / 5000000000 : ℝ) ≤ Real.exp (83 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (83 / 200 : ℝ) (126631651119 / 125000000000 : ℝ)
    (7571853703 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell332_rightExp :
    Real.exp (333 / 800 : ℝ) ≤ (7581324439 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (333 / 800 : ℝ) (1013092782117 / 1000000000000 : ℝ)
    (7581324439 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell332_denomUpper :
    Real.exp (23298685788291327 / 5000000000000000 : ℝ) ≤ (528041600861 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23298685788291327 / 5000000000000000 : ℝ) (578376409717
    / 500000000000 : ℝ) (528041600861 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell332_denomLower :
    (262371971531 / 2500000000 : ℝ) ≤ Real.exp (2908420314814397 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2908420314814397 / 625000000000000 : ℝ) (578263191797 /
    500000000000 : ℝ) (262371971531 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell332_product_lower :
    (2973459377314397 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (83 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell332_leftExp
    (by norm_num : (0 : ℝ) ≤ (7571853703 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell332_product_upper :
    Real.pi * Real.exp (333 / 800 : ℝ) ≤ (23817435788291327 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell332_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell332_endpointLower :
    (11739860481 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 400 : ℝ) (333 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2973459377314397 / 625000000000000 : ℝ) (Real.pi * Real.exp (83 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell332_product_lower
  have hD : Real.exp (Real.pi * Real.exp (333 / 800 : ℝ) - (83 / 800 : ℝ)) ≤
      (528041600861 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell332_denomUpper
    linarith [hpThetaJensenCell332_product_upper]
  have hi : (1 / (528041600861 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (333 / 800 : ℝ) - (83 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (528041600861 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (528041600861 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((83 / 800 : ℝ) - Real.pi * Real.exp (333 / 800 : ℝ)) := by
    rw [show (83 / 800 : ℝ) - Real.pi * Real.exp (333 / 800 : ℝ) =
      -(Real.pi * Real.exp (333 / 800 : ℝ) - (83 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (83 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (83 / 200 : ℝ)) := by
    have h := hpThetaJensenCell332_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (528041600861 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell332_endpointUpper :
    hpThetaJensenKernelEndpointUpper (83 / 400 : ℝ) (333 / 1600 : ℝ) ≤ (5940618883 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (333 / 800 : ℝ)) (23817435788291327 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (333 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell332_product_upper
  have hD : (262371971531 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (83 / 200 : ℝ) - (333 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell332_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell332_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (83 / 200 : ℝ) - (333 / 3200 : ℝ)) ≤
      (1 / (262371971531 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (262371971531 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((333 / 3200 : ℝ) - Real.pi * Real.exp (83 / 200 : ℝ)) ≤
      (2 / (262371971531 / 2500000000 : ℝ) : ℝ) := by
    rw [show (333 / 3200 : ℝ) - Real.pi * Real.exp (83 / 200 : ℝ) =
      -(Real.pi * Real.exp (83 / 200 : ℝ) - (333 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23817435788291327 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (23817435788291327 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell332_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (83 / 400 : ℝ) (333 / 1600 : ℝ)) :
    (11739860481 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5940618883 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell332_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell332_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell333_leftExp :
    (15162648877 / 10000000000 : ℝ) ≤ Real.exp (333 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (333 / 800 : ℝ) (253273195529 / 250000000000 : ℝ)
    (15162648877 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell333_rightExp :
    Real.exp (167 / 400 : ℝ) ≤ (15181614039 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (167 / 400 : ℝ) (506566178413 / 500000000000 : ℝ)
    (15181614039 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell333_denomUpper :
    Real.exp (46653827393624127 / 10000000000000000 : ℝ) ≤ (106206226749 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46653827393624127 / 10000000000000000 : ℝ) (289239229223
    / 250000000000 : ℝ) (106206226749 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell333_denomLower :
    (1055421755279 / 10000000000 : ℝ) ≤ Real.exp (5823888301349023 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5823888301349023 / 1250000000000000 : ℝ) (289182543001 /
    250000000000 : ℝ) (1055421755279 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell333_product_lower :
    (5954357051349023 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (333 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell333_leftExp
    (by norm_num : (0 : ℝ) ≤ (15162648877 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell333_product_upper :
    Real.pi * Real.exp (167 / 400 : ℝ) ≤ (47694452393624127 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell333_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell333_endpointLower :
    (11709721711 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (333 / 1600 : ℝ) (167 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5954357051349023 / 1250000000000000 : ℝ) (Real.pi * Real.exp (333 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell333_product_lower
  have hD : Real.exp (Real.pi * Real.exp (167 / 400 : ℝ) - (333 / 3200 : ℝ)) ≤
      (106206226749 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell333_denomUpper
    linarith [hpThetaJensenCell333_product_upper]
  have hi : (1 / (106206226749 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (167 / 400 : ℝ) - (333 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (106206226749 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (106206226749 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((333 / 3200 : ℝ) - Real.pi * Real.exp (167 / 400 : ℝ)) := by
    rw [show (333 / 3200 : ℝ) - Real.pi * Real.exp (167 / 400 : ℝ) =
      -(Real.pi * Real.exp (167 / 400 : ℝ) - (333 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (333 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (333 / 800 : ℝ)) := by
    have h := hpThetaJensenCell333_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (106206226749 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell333_endpointUpper :
    hpThetaJensenKernelEndpointUpper (333 / 1600 : ℝ) (167 / 800 : ℝ) ≤ (11850811843 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (167 / 400 : ℝ)) (47694452393624127 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (167 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell333_product_upper
  have hD : (1055421755279 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (333 / 800 : ℝ) - (167 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell333_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell333_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (333 / 800 : ℝ) - (167 / 1600 : ℝ)) ≤
      (1 / (1055421755279 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1055421755279 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((167 / 1600 : ℝ) - Real.pi * Real.exp (333 / 800 : ℝ)) ≤
      (2 / (1055421755279 / 10000000000 : ℝ) : ℝ) := by
    rw [show (167 / 1600 : ℝ) - Real.pi * Real.exp (333 / 800 : ℝ) =
      -(Real.pi * Real.exp (333 / 800 : ℝ) - (167 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47694452393624127 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47694452393624127 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell333_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (333 / 1600 : ℝ) (167 / 800 : ℝ)) :
    (11709721711 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11850811843 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell333_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell333_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell334_leftExp :
    (7590807019 / 5000000000 : ℝ) ≤ Real.exp (167 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (167 / 400 : ℝ) (40525294273 / 40000000000 : ℝ)
    (7590807019 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell334_rightExp :
    Real.exp (67 / 160 : ℝ) ≤ (15200602923 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 160 : ℝ) (506585966541 / 500000000000 : ℝ)
    (15200602923 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell334_denomUpper :
    Real.exp (46710357738676339 / 10000000000000000 : ℝ) ≤ (1068083144213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46710357738676339 / 10000000000000000 : ℝ) (144645164983
    / 125000000000 : ℝ) (1068083144213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell334_denomLower :
    (530698537119 / 5000000000 : ℝ) ≤ Real.exp (2915472638054281 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2915472638054281 / 625000000000000 : ℝ) (578467132699 /
    500000000000 : ℝ) (530698537119 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell334_product_lower :
    (2980902325554281 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (167 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell334_leftExp
    (by norm_num : (0 : ℝ) ≤ (7590807019 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell334_product_upper :
    Real.pi * Real.exp (67 / 160 : ℝ) ≤ (47754107738676339 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell334_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell334_endpointLower :
    (5839780511 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (167 / 800 : ℝ) (67 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2980902325554281 / 625000000000000 : ℝ) (Real.pi * Real.exp (167 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell334_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 160 : ℝ) - (167 / 1600 : ℝ)) ≤
      (1068083144213 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell334_denomUpper
    linarith [hpThetaJensenCell334_product_upper]
  have hi : (1 / (1068083144213 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 160 : ℝ) - (167 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1068083144213 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1068083144213 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((167 / 1600 : ℝ) - Real.pi * Real.exp (67 / 160 : ℝ)) := by
    rw [show (167 / 1600 : ℝ) - Real.pi * Real.exp (67 / 160 : ℝ) =
      -(Real.pi * Real.exp (67 / 160 : ℝ) - (167 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (167 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (167 / 400 : ℝ)) := by
    have h := hpThetaJensenCell334_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1068083144213 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell334_endpointUpper :
    hpThetaJensenKernelEndpointUpper (167 / 800 : ℝ) (67 / 320 : ℝ) ≤ (738772719 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 160 : ℝ)) (47754107738676339 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell334_product_upper
  have hD : (530698537119 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (167 / 400 : ℝ) - (67 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell334_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell334_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (167 / 400 : ℝ) - (67 / 640 : ℝ)) ≤
      (1 / (530698537119 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (530698537119 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 640 : ℝ) - Real.pi * Real.exp (167 / 400 : ℝ)) ≤
      (2 / (530698537119 / 5000000000 : ℝ) : ℝ) := by
    rw [show (67 / 640 : ℝ) - Real.pi * Real.exp (167 / 400 : ℝ) =
      -(Real.pi * Real.exp (167 / 400 : ℝ) - (67 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47754107738676339 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47754107738676339 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell334_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (167 / 800 : ℝ) (67 / 320 : ℝ)) :
    (5839780511 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (738772719 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell334_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell334_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell335_leftExp :
    (15200602921 / 10000000000 : ℝ) ≤ Real.exp (67 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 160 : ℝ) (1013171933081 / 1000000000000 : ℝ)
    (15200602921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell335_rightExp :
    Real.exp (21 / 50 : ℝ) ≤ (15219615557 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 50 : ℝ) (253302877721 / 250000000000 : ℝ)
    (15219615557 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell335_denomUpper :
    Real.exp (46766962696562301 / 10000000000000000 : ℝ) ≤ (107414616803 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46766962696562301 / 10000000000000000 : ℝ) (578683014403
    / 500000000000 : ℝ) (107414616803 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell335_denomLower :
    (1067414177587 / 10000000000 : ℝ) ≤ Real.exp (5838011566473779 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5838011566473779 / 1250000000000000 : ℝ) (36160583259 /
    31250000000 : ℝ) (1067414177587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell335_product_lower :
    (5969261566473779 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell335_leftExp
    (by norm_num : (0 : ℝ) ≤ (15200602921 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell335_product_upper :
    Real.pi * Real.exp (21 / 50 : ℝ) ≤ (47813837696562301 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell335_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell335_endpointLower :
    (11649378917 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 320 : ℝ) (21 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5969261566473779 / 1250000000000000 : ℝ) (Real.pi * Real.exp (67 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell335_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 50 : ℝ) - (67 / 640 : ℝ)) ≤
      (107414616803 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell335_denomUpper
    linarith [hpThetaJensenCell335_product_upper]
  have hi : (1 / (107414616803 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 50 : ℝ) - (67 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (107414616803 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (107414616803 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 640 : ℝ) - Real.pi * Real.exp (21 / 50 : ℝ)) := by
    rw [show (67 / 640 : ℝ) - Real.pi * Real.exp (21 / 50 : ℝ) =
      -(Real.pi * Real.exp (21 / 50 : ℝ) - (67 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 160 : ℝ)) := by
    have h := hpThetaJensenCell335_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (107414616803 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell335_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 320 : ℝ) (21 / 100 : ℝ) ≤ (11789893231 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 50 : ℝ)) (47813837696562301 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell335_product_upper
  have hD : (1067414177587 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 160 : ℝ) - (21 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell335_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell335_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 160 : ℝ) - (21 / 200 : ℝ)) ≤
      (1 / (1067414177587 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1067414177587 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 200 : ℝ) - Real.pi * Real.exp (67 / 160 : ℝ)) ≤
      (2 / (1067414177587 / 10000000000 : ℝ) : ℝ) := by
    rw [show (21 / 200 : ℝ) - Real.pi * Real.exp (67 / 160 : ℝ) =
      -(Real.pi * Real.exp (67 / 160 : ℝ) - (21 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47813837696562301 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47813837696562301 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell335_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 320 : ℝ) (21 / 100 : ℝ)) :
    (11649378917 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11789893231 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell335_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell335_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell336_leftExp :
    (3804903889 / 2500000000 : ℝ) ≤ Real.exp (21 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 50 : ℝ) (1013211510883 / 1000000000000 : ℝ)
    (3804903889 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell336_rightExp :
    Real.exp (337 / 800 : ℝ) ≤ (15238651971 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (337 / 800 : ℝ) (1013251090231 / 1000000000000 : ℝ)
    (15238651971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell336_denomUpper :
    Real.exp (46823642361529803 / 10000000000000000 : ℝ) ≤ (1080251679089 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46823642361529803 / 10000000000000000 : ℝ) (72348190263
    / 62500000000 : ℝ) (1080251679089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell336_denomLower :
    (53673670113 / 500000000 : ℝ) ≤ Real.exp (1461271796056411 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1461271796056411 / 312500000000000 : ℝ) (289335842291 /
    250000000000 : ℝ) (53673670113 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell336_product_lower :
    (1494181952306411 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell336_leftExp
    (by norm_num : (0 : ℝ) ≤ (3804903889 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell336_product_upper :
    Real.pi * Real.exp (337 / 800 : ℝ) ≤ (47873642361529803 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell336_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell336_endpointLower :
    (2323835177 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 100 : ℝ) (337 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1494181952306411 / 312500000000000 : ℝ) (Real.pi * Real.exp (21 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell336_product_lower
  have hD : Real.exp (Real.pi * Real.exp (337 / 800 : ℝ) - (21 / 200 : ℝ)) ≤
      (1080251679089 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell336_denomUpper
    linarith [hpThetaJensenCell336_product_upper]
  have hi : (1 / (1080251679089 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (337 / 800 : ℝ) - (21 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1080251679089 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1080251679089 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 200 : ℝ) - Real.pi * Real.exp (337 / 800 : ℝ)) := by
    rw [show (21 / 200 : ℝ) - Real.pi * Real.exp (337 / 800 : ℝ) =
      -(Real.pi * Real.exp (337 / 800 : ℝ) - (21 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 50 : ℝ)) := by
    have h := hpThetaJensenCell336_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1080251679089 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell336_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 100 : ℝ) (337 / 1600 : ℝ) ≤ (2351880303 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (337 / 800 : ℝ)) (47873642361529803 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (337 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell336_product_upper
  have hD : (53673670113 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 50 : ℝ) - (337 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell336_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell336_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 50 : ℝ) - (337 / 3200 : ℝ)) ≤
      (1 / (53673670113 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (53673670113 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((337 / 3200 : ℝ) - Real.pi * Real.exp (21 / 50 : ℝ)) ≤
      (2 / (53673670113 / 500000000 : ℝ) : ℝ) := by
    rw [show (337 / 3200 : ℝ) - Real.pi * Real.exp (21 / 50 : ℝ) =
      -(Real.pi * Real.exp (21 / 50 : ℝ) - (337 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47873642361529803 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47873642361529803 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell336_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 100 : ℝ) (337 / 1600 : ℝ)) :
    (2323835177 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2351880303 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell336_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell336_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell337_leftExp :
    (1523865197 / 1000000000 : ℝ) ≤ Real.exp (337 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (337 / 800 : ℝ) (101325109023 / 100000000000 : ℝ)
    (1523865197 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell337_rightExp :
    Real.exp (169 / 400 : ℝ) ≤ (15257712197 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (169 / 400 : ℝ) (8106325369 / 8000000000 : ℝ)
    (15257712197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell337_denomUpper :
    Real.exp (46880396834109821 / 10000000000000000 : ℝ) ≤ (135800002663 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46880396834109821 / 10000000000000000 : ℝ) (144722045823
    / 125000000000 : ℝ) (135800002663 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell337_denomLower :
    (539787543623 / 5000000000 : ℝ) ≤ Real.exp (585217213996703 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (585217213996703 / 125000000000000 : ℝ) (289387095121 /
    250000000000 : ℝ) (539787543623 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell337_product_lower :
    (598420338996703 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (337 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell337_leftExp
    (by norm_num : (0 : ℝ) ≤ (1523865197 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell337_product_upper :
    Real.pi * Real.exp (169 / 400 : ℝ) ≤ (47933521834109821 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell337_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell337_endpointLower :
    (28972381 / 25000000 : ℝ) ≤ hpThetaTraceEndpointLower (337 / 1600 : ℝ) (169 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (598420338996703 / 125000000000000 : ℝ) (Real.pi * Real.exp (337 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell337_product_lower
  have hD : Real.exp (Real.pi * Real.exp (169 / 400 : ℝ) - (337 / 3200 : ℝ)) ≤
      (135800002663 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell337_denomUpper
    linarith [hpThetaJensenCell337_product_upper]
  have hi : (1 / (135800002663 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (169 / 400 : ℝ) - (337 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (135800002663 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (135800002663 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((337 / 3200 : ℝ) - Real.pi * Real.exp (169 / 400 : ℝ)) := by
    rw [show (337 / 3200 : ℝ) - Real.pi * Real.exp (169 / 400 : ℝ) =
      -(Real.pi * Real.exp (169 / 400 : ℝ) - (337 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (337 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (337 / 800 : ℝ)) := by
    have h := hpThetaJensenCell337_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (135800002663 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell337_endpointUpper :
    hpThetaJensenKernelEndpointUpper (337 / 1600 : ℝ) (169 / 800 : ℝ) ≤ (366527777 / 312500000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (169 / 400 : ℝ)) (47933521834109821 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (169 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell337_product_upper
  have hD : (539787543623 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (337 / 800 : ℝ) - (169 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell337_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell337_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (337 / 800 : ℝ) - (169 / 1600 : ℝ)) ≤
      (1 / (539787543623 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (539787543623 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((169 / 1600 : ℝ) - Real.pi * Real.exp (337 / 800 : ℝ)) ≤
      (2 / (539787543623 / 5000000000 : ℝ) : ℝ) := by
    rw [show (169 / 1600 : ℝ) - Real.pi * Real.exp (337 / 800 : ℝ) =
      -(Real.pi * Real.exp (337 / 800 : ℝ) - (169 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47933521834109821 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (47933521834109821 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell337_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (337 / 1600 : ℝ) (169 / 800 : ℝ)) :
    (28972381 / 25000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (366527777 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell337_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell337_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell338_leftExp :
    (3051542439 / 2000000000 : ℝ) ≤ Real.exp (169 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (169 / 400 : ℝ) (253322667781 / 250000000000 : ℝ)
    (3051542439 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell338_rightExp :
    Real.exp (339 / 800 : ℝ) ≤ (7638398131 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (339 / 800 : ℝ) (202666050713 / 200000000000 : ℝ)
    (7638398131 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell338_denomUpper :
    Real.exp (23468613099562683 / 5000000000000000 : ℝ) ≤ (1092591539989 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23468613099562683 / 5000000000000000 : ℝ) (144747749549
    / 125000000000 : ℝ) (1092591539989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell338_denomLower :
    (54285978809 / 500000000 : ℝ) ≤ Real.exp (1171853289252861 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1171853289252861 / 250000000000000 : ℝ) (28943842469 /
    25000000000 : ℝ) (54285978809 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell338_product_lower :
    (1198337664252861 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (169 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell338_leftExp
    (by norm_num : (0 : ℝ) ≤ (3051542439 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell338_product_upper :
    Real.pi * Real.exp (339 / 800 : ℝ) ≤ (23996738099562683 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell338_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell338_endpointLower :
    (2311741793 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (169 / 800 : ℝ) (339 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1198337664252861 / 250000000000000 : ℝ) (Real.pi * Real.exp (169 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell338_product_lower
  have hD : Real.exp (Real.pi * Real.exp (339 / 800 : ℝ) - (169 / 1600 : ℝ)) ≤
      (1092591539989 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell338_denomUpper
    linarith [hpThetaJensenCell338_product_upper]
  have hi : (1 / (1092591539989 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (339 / 800 : ℝ) - (169 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1092591539989 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1092591539989 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((169 / 1600 : ℝ) - Real.pi * Real.exp (339 / 800 : ℝ)) := by
    rw [show (169 / 1600 : ℝ) - Real.pi * Real.exp (339 / 800 : ℝ) =
      -(Real.pi * Real.exp (339 / 800 : ℝ) - (169 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (169 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (169 / 400 : ℝ)) := by
    have h := hpThetaJensenCell338_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1092591539989 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell338_endpointUpper :
    hpThetaJensenKernelEndpointUpper (169 / 800 : ℝ) (339 / 1600 : ℝ) ≤ (11698355757 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (339 / 800 : ℝ)) (23996738099562683 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (339 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell338_product_upper
  have hD : (54285978809 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (169 / 400 : ℝ) - (339 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell338_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell338_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (169 / 400 : ℝ) - (339 / 3200 : ℝ)) ≤
      (1 / (54285978809 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (54285978809 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((339 / 3200 : ℝ) - Real.pi * Real.exp (169 / 400 : ℝ)) ≤
      (2 / (54285978809 / 500000000 : ℝ) : ℝ) := by
    rw [show (339 / 3200 : ℝ) - Real.pi * Real.exp (169 / 400 : ℝ) =
      -(Real.pi * Real.exp (169 / 400 : ℝ) - (339 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23996738099562683 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (23996738099562683 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell338_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (169 / 800 : ℝ) (339 / 1600 : ℝ)) :
    (2311741793 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11698355757 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell338_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell338_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell339_leftExp :
    (15276796261 / 10000000000 : ℝ) ≤ Real.exp (339 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (339 / 800 : ℝ) (253332563391 / 250000000000 : ℝ)
    (15276796261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell339_rightExp :
    Real.exp (17 / 40 : ℝ) ≤ (15295904197 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 40 : ℝ) (1013369837551 / 1000000000000 : ℝ)
    (15295904197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell339_denomUpper :
    Real.exp (46994130553965821 / 10000000000000000 : ℝ) ≤ (274706646219 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46994130553965821 / 10000000000000000 : ℝ) (579093967067
    / 500000000000 : ℝ) (274706646219 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell339_denomLower :
    (1091907215179 / 10000000000 : ℝ) ≤ Real.exp (5866370114898439 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5866370114898439 / 1250000000000000 : ℝ) (289489831121 /
    250000000000 : ℝ) (1091907215179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell339_product_lower :
    (5999182614898439 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (339 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell339_leftExp
    (by norm_num : (0 : ℝ) ≤ (15276796261 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell339_product_upper :
    Real.pi * Real.exp (17 / 40 : ℝ) ≤ (48053505553965821 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell339_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell339_endpointLower :
    (720527879 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (339 / 1600 : ℝ) (17 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5999182614898439 / 1250000000000000 : ℝ) (Real.pi * Real.exp (339 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell339_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 40 : ℝ) - (339 / 3200 : ℝ)) ≤
      (274706646219 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell339_denomUpper
    linarith [hpThetaJensenCell339_product_upper]
  have hi : (1 / (274706646219 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 40 : ℝ) - (339 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (274706646219 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (274706646219 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((339 / 3200 : ℝ) - Real.pi * Real.exp (17 / 40 : ℝ)) := by
    rw [show (339 / 3200 : ℝ) - Real.pi * Real.exp (17 / 40 : ℝ) =
      -(Real.pi * Real.exp (17 / 40 : ℝ) - (339 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (339 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (339 / 800 : ℝ)) := by
    have h := hpThetaJensenCell339_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (274706646219 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell339_endpointUpper :
    hpThetaJensenKernelEndpointUpper (339 / 1600 : ℝ) (17 / 80 : ℝ) ≤ (11667802687 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 40 : ℝ)) (48053505553965821 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell339_product_upper
  have hD : (1091907215179 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (339 / 800 : ℝ) - (17 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell339_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell339_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (339 / 800 : ℝ) - (17 / 160 : ℝ)) ≤
      (1 / (1091907215179 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1091907215179 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 160 : ℝ) - Real.pi * Real.exp (339 / 800 : ℝ)) ≤
      (2 / (1091907215179 / 10000000000 : ℝ) : ℝ) := by
    rw [show (17 / 160 : ℝ) - Real.pi * Real.exp (339 / 800 : ℝ) =
      -(Real.pi * Real.exp (339 / 800 : ℝ) - (17 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48053505553965821 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (48053505553965821 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell339_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (339 / 1600 : ℝ) (17 / 80 : ℝ)) :
    (720527879 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11667802687 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell339_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell339_endpointUpper

def hpThetaJensenCellsBatch016Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (151245479 / 125000000 : ℝ)
  | 1 => (482792029 / 400000000 : ℝ)
  | 2 => (12039935331 / 10000000000 : ℝ)
  | 3 => (1201004263 / 1000000000 : ℝ)
  | 4 => (11980123107 / 10000000000 : ℝ)
  | 5 => (11950177261 / 10000000000 : ℝ)
  | 6 => (596010279 / 500000000 : ℝ)
  | 7 => (2972552139 / 2500000000 : ℝ)
  | 8 => (2965046671 / 2500000000 : ℝ)
  | 9 => (5915070223 / 5000000000 : ℝ)
  | 10 => (11800070339 / 10000000000 : ℝ)
  | 11 => (2353995371 / 2000000000 : ℝ)
  | 12 => (11739860481 / 10000000000 : ℝ)
  | 13 => (11709721711 / 10000000000 : ℝ)
  | 14 => (5839780511 / 5000000000 : ℝ)
  | 15 => (11649378917 / 10000000000 : ℝ)
  | 16 => (2323835177 / 2000000000 : ℝ)
  | 17 => (28972381 / 25000000 : ℝ)
  | 18 => (2311741793 / 2000000000 : ℝ)
  | 19 => (720527879 / 625000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch016Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (12244419637 / 10000000000 : ℝ)
  | 1 => (2442860283 / 2000000000 : ℝ)
  | 2 => (12184154821 / 10000000000 : ℝ)
  | 3 => (2430796071 / 2000000000 : ℝ)
  | 4 => (2424755703 / 2000000000 : ℝ)
  | 5 => (3023387449 / 2500000000 : ℝ)
  | 6 => (1206329469 / 1000000000 : ℝ)
  | 7 => (12033013701 / 10000000000 : ℝ)
  | 8 => (6001353657 / 5000000000 : ℝ)
  | 9 => (2993094009 / 2500000000 : ℝ)
  | 10 => (11942020357 / 10000000000 : ℝ)
  | 11 => (11911640767 / 10000000000 : ℝ)
  | 12 => (5940618883 / 5000000000 : ℝ)
  | 13 => (11850811843 / 10000000000 : ℝ)
  | 14 => (738772719 / 625000000 : ℝ)
  | 15 => (11789893231 / 10000000000 : ℝ)
  | 16 => (2351880303 / 2000000000 : ℝ)
  | 17 => (366527777 / 312500000 : ℝ)
  | 18 => (11698355757 / 10000000000 : ℝ)
  | 19 => (11667802687 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch016_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch016Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch016Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell320_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell321_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell322_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell323_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell324_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell325_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell326_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell327_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell328_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell329_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell330_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell331_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell332_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell333_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell334_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell335_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell336_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell337_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell338_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell339_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper] at h ⊢
    exact h

end HodgeProofHP
