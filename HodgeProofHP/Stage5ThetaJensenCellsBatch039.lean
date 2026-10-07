import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell780_leftExp :
    (26511672109 / 10000000000 : ℝ) ≤ Real.exp (39 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 40 : ℝ) (1030937672743 / 1000000000000 : ℝ)
    (26511672109 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell780_rightExp :
    Real.exp (781 / 800 : ℝ) ≤ (13272416211 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (781 / 800 : ℝ) (1030977944533 / 1000000000000 : ℝ)
    (13272416211 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell780_denomUpper :
    Real.exp (40477779861564123 / 5000000000000000 : ℝ) ≤ (32798598516729 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40477779861564123 / 5000000000000000 : ℝ) (1257681061 /
    976562500 : ℝ) (32798598516729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell780_denomLower :
    (16224230487193 / 5000000000 : ℝ) ≤ Real.exp (10106029000532191 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10106029000532191 / 1250000000000000 : ℝ) (1287433529967
    / 1000000000000 : ℝ) (16224230487193 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell780_product_lower :
    (10411107125532191 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell780_leftExp
    (by norm_num : (0 : ℝ) ≤ (26511672109 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell780_product_upper :
    Real.pi * Real.exp (781 / 800 : ℝ) ≤ (41696529861564123 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell780_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell780_endpointLower :
    (277460677 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 80 : ℝ) (781 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10411107125532191 / 1250000000000000 : ℝ) (Real.pi * Real.exp (39 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell780_product_lower
  have hD : Real.exp (Real.pi * Real.exp (781 / 800 : ℝ) - (39 / 160 : ℝ)) ≤
      (32798598516729 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell780_denomUpper
    linarith [hpThetaJensenCell780_product_upper]
  have hi : (1 / (32798598516729 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (781 / 800 : ℝ) - (39 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32798598516729 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32798598516729 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 160 : ℝ) - Real.pi * Real.exp (781 / 800 : ℝ)) := by
    rw [show (39 / 160 : ℝ) - Real.pi * Real.exp (781 / 800 : ℝ) =
      -(Real.pi * Real.exp (781 / 800 : ℝ) - (39 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 40 : ℝ)) := by
    have h := hpThetaJensenCell780_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32798598516729 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell780_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 80 : ℝ) (781 / 1600 : ℝ) ≤ (1409873181 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (781 / 800 : ℝ)) (41696529861564123 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (781 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell780_product_upper
  have hD : (16224230487193 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 40 : ℝ) - (781 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell780_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell780_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 40 : ℝ) - (781 / 3200 : ℝ)) ≤
      (1 / (16224230487193 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16224230487193 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((781 / 3200 : ℝ) - Real.pi * Real.exp (39 / 40 : ℝ)) ≤
      (2 / (16224230487193 / 5000000000 : ℝ) : ℝ) := by
    rw [show (781 / 3200 : ℝ) - Real.pi * Real.exp (39 / 40 : ℝ) =
      -(Real.pi * Real.exp (39 / 40 : ℝ) - (781 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (41696529861564123 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (41696529861564123 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell780_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 80 : ℝ) (781 / 1600 : ℝ)) :
    (277460677 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1409873181 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell780_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell780_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell781_leftExp :
    (1327241621 / 500000000 : ℝ) ≤ Real.exp (781 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (781 / 800 : ℝ) (257744486133 / 250000000000 : ℝ)
    (1327241621 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell781_rightExp :
    Real.exp (391 / 400 : ℝ) ≤ (26578034209 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (391 / 400 : ℝ) (128877277237 / 125000000000 : ℝ)
    (26578034209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell781_denomUpper :
    Real.exp (81056741224754937 / 10000000000000000 : ℝ) ≤ (16566072124801 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81056741224754937 / 10000000000000000 : ℝ)
    (1288272683837 / 1000000000000 : ℝ) (16566072124801 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell781_denomLower :
    (4097252345941 / 1250000000 : ℝ) ≤ Real.exp (505933019825079 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (505933019825079 / 62500000000000 : ℝ) (1287840146233 /
    1000000000000 : ℝ) (4097252345941 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell781_product_lower :
    (521206457325079 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (781 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell781_leftExp
    (by norm_num : (0 : ℝ) ≤ (1327241621 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell781_product_upper :
    Real.pi * Real.exp (391 / 400 : ℝ) ≤ (83497366224754937 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell781_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell781_endpointLower :
    (688576319 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (781 / 1600 : ℝ) (391 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (521206457325079 / 62500000000000 : ℝ) (Real.pi * Real.exp (781 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell781_product_lower
  have hD : Real.exp (Real.pi * Real.exp (391 / 400 : ℝ) - (781 / 3200 : ℝ)) ≤
      (16566072124801 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell781_denomUpper
    linarith [hpThetaJensenCell781_product_upper]
  have hi : (1 / (16566072124801 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (391 / 400 : ℝ) - (781 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16566072124801 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16566072124801 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((781 / 3200 : ℝ) - Real.pi * Real.exp (391 / 400 : ℝ)) := by
    rw [show (781 / 3200 : ℝ) - Real.pi * Real.exp (391 / 400 : ℝ) =
      -(Real.pi * Real.exp (391 / 400 : ℝ) - (781 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (781 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (781 / 800 : ℝ)) := by
    have h := hpThetaJensenCell781_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16566072124801 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell781_endpointUpper :
    hpThetaJensenKernelEndpointUpper (781 / 1600 : ℝ) (391 / 800 : ℝ) ≤ (1399574949 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (391 / 400 : ℝ)) (83497366224754937 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (391 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell781_product_upper
  have hD : (4097252345941 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (781 / 800 : ℝ) - (391 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell781_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell781_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (781 / 800 : ℝ) - (391 / 1600 : ℝ)) ≤
      (1 / (4097252345941 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4097252345941 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((391 / 1600 : ℝ) - Real.pi * Real.exp (781 / 800 : ℝ)) ≤
      (2 / (4097252345941 / 1250000000 : ℝ) : ℝ) := by
    rw [show (391 / 1600 : ℝ) - Real.pi * Real.exp (781 / 800 : ℝ) =
      -(Real.pi * Real.exp (781 / 800 : ℝ) - (391 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (83497366224754937 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (83497366224754937 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell781_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (781 / 1600 : ℝ) (391 / 800 : ℝ)) :
    (688576319 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1399574949 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell781_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell781_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell782_leftExp :
    (830563569 / 312500000 : ℝ) ≤ Real.exp (391 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (391 / 400 : ℝ) (206203643579 / 200000000000 : ℝ)
    (830563569 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell782_rightExp :
    Real.exp (783 / 800 : ℝ) ≤ (6652819381 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (783 / 800 : ℝ) (1031058492831 / 1000000000000 : ℝ)
    (6652819381 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell782_denomUpper :
    Real.exp (20289513297613933 / 2500000000000000 : ℝ) ≤ (669390372651 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20289513297613933 / 2500000000000000 : ℝ) (644340307701
    / 500000000000 : ℝ) (669390372651 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell782_denomLower :
    (16555677557173 / 5000000000 : ℝ) ≤ Real.exp (316603377513981 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (316603377513981 / 39062500000000 : ℝ) (161030926937 /
    125000000000 : ℝ) (16555677557173 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell782_product_lower :
    (326161482982731 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (391 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell782_leftExp
    (by norm_num : (0 : ℝ) ≤ (830563569 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell782_product_upper :
    Real.pi * Real.exp (783 / 800 : ℝ) ≤ (20900450797613933 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell782_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell782_endpointLower :
    (341764439 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (391 / 800 : ℝ) (783 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (326161482982731 / 39062500000000 : ℝ) (Real.pi * Real.exp (391 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell782_product_lower
  have hD : Real.exp (Real.pi * Real.exp (783 / 800 : ℝ) - (391 / 1600 : ℝ)) ≤
      (669390372651 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell782_denomUpper
    linarith [hpThetaJensenCell782_product_upper]
  have hi : (1 / (669390372651 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (783 / 800 : ℝ) - (391 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (669390372651 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (669390372651 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((391 / 1600 : ℝ) - Real.pi * Real.exp (783 / 800 : ℝ)) := by
    rw [show (391 / 1600 : ℝ) - Real.pi * Real.exp (783 / 800 : ℝ) =
      -(Real.pi * Real.exp (783 / 800 : ℝ) - (391 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (391 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (391 / 400 : ℝ)) := by
    have h := hpThetaJensenCell782_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (669390372651 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell782_endpointUpper :
    hpThetaJensenKernelEndpointUpper (391 / 800 : ℝ) (783 / 1600 : ℝ) ≤ (173666657 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (783 / 800 : ℝ)) (20900450797613933 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (783 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell782_product_upper
  have hD : (16555677557173 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (391 / 400 : ℝ) - (783 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell782_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell782_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (391 / 400 : ℝ) - (783 / 3200 : ℝ)) ≤
      (1 / (16555677557173 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16555677557173 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((783 / 3200 : ℝ) - Real.pi * Real.exp (391 / 400 : ℝ)) ≤
      (2 / (16555677557173 / 5000000000 : ℝ) : ℝ) := by
    rw [show (783 / 3200 : ℝ) - Real.pi * Real.exp (391 / 400 : ℝ) =
      -(Real.pi * Real.exp (391 / 400 : ℝ) - (783 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20900450797613933 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (20900450797613933 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell782_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (391 / 800 : ℝ) (783 / 1600 : ℝ)) :
    (341764439 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (173666657 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell782_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell782_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell783_leftExp :
    (26611277523 / 10000000000 : ℝ) ≤ Real.exp (783 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (783 / 800 : ℝ) (103105849283 / 100000000000 : ℝ)
    (26611277523 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell783_rightExp :
    Real.exp (49 / 50 : ℝ) ≤ (1332228121 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 50 : ℝ) (51554938467 / 50000000000 : ℝ)
    (1332228121 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell783_denomUpper :
    Real.exp (4062974789336753 / 500000000000000 : ℝ) ≤ (3381077006443 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4062974789336753 / 500000000000000 : ℝ) (322272300593 /
    250000000000 : ℝ) (3381077006443 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell783_denomLower :
    (33448517696839 / 10000000000 : ℝ) ≤ Real.exp (10143972072004577 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10143972072004577 / 1250000000000000 : ℝ) (644327669463
    / 500000000000 : ℝ) (33448517696839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell783_product_lower :
    (10450222072004577 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (783 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell783_leftExp
    (by norm_num : (0 : ℝ) ≤ (26611277523 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell783_product_upper :
    Real.pi * Real.exp (49 / 50 : ℝ) ≤ (4185318539336753 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell783_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell783_endpointLower :
    (67850929 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (783 / 1600 : ℝ) (49 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10450222072004577 / 1250000000000000 : ℝ) (Real.pi * Real.exp (783 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell783_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 50 : ℝ) - (783 / 3200 : ℝ)) ≤
      (3381077006443 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell783_denomUpper
    linarith [hpThetaJensenCell783_product_upper]
  have hi : (1 / (3381077006443 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 50 : ℝ) - (783 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3381077006443 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3381077006443 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((783 / 3200 : ℝ) - Real.pi * Real.exp (49 / 50 : ℝ)) := by
    rw [show (783 / 3200 : ℝ) - Real.pi * Real.exp (49 / 50 : ℝ) =
      -(Real.pi * Real.exp (49 / 50 : ℝ) - (783 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (783 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (783 / 800 : ℝ)) := by
    have h := hpThetaJensenCell783_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3381077006443 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell783_endpointUpper :
    hpThetaJensenKernelEndpointUpper (783 / 1600 : ℝ) (49 / 100 : ℝ) ≤ (689573971 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 50 : ℝ)) (4185318539336753 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell783_product_upper
  have hD : (33448517696839 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (783 / 800 : ℝ) - (49 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell783_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell783_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (783 / 800 : ℝ) - (49 / 200 : ℝ)) ≤
      (1 / (33448517696839 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (33448517696839 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 200 : ℝ) - Real.pi * Real.exp (783 / 800 : ℝ)) ≤
      (2 / (33448517696839 / 10000000000 : ℝ) : ℝ) := by
    rw [show (49 / 200 : ℝ) - Real.pi * Real.exp (783 / 800 : ℝ) =
      -(Real.pi * Real.exp (783 / 800 : ℝ) - (49 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4185318539336753 / 500000000000000 : ℝ) ^ 2 - 6 *
      (4185318539336753 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell783_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (783 / 1600 : ℝ) (49 / 100 : ℝ)) :
    (67850929 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (689573971 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell783_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell783_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell784_leftExp :
    (13322281209 / 5000000000 : ℝ) ≤ Real.exp (49 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 50 : ℝ) (1031098769339 / 1000000000000 : ℝ)
    (13322281209 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell784_rightExp :
    Real.exp (157 / 160 : ℝ) ≤ (6669472237 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (157 / 160 : ℝ) (1031139047423 / 1000000000000 : ℝ)
    (6669472237 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell784_denomUpper :
    Real.exp (20340267293453541 / 2500000000000000 : ℝ) ≤ (273247580661 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20340267293453541 / 2500000000000000 : ℝ) (1289498445933
    / 1000000000000 : ℝ) (273247580661 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell784_denomLower :
    (16894777441173 / 5000000000 : ℝ) ≤ Real.exp (5078326195993091 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5078326195993091 / 625000000000000 : ℝ) (257812783547 /
    200000000000 : ℝ) (16894777441173 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell784_product_lower :
    (5231646508493091 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell784_leftExp
    (by norm_num : (0 : ℝ) ≤ (13322281209 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell784_product_upper :
    Real.pi * Real.exp (157 / 160 : ℝ) ≤ (20952767293453541 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell784_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell784_endpointLower :
    (336758737 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 100 : ℝ) (157 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5231646508493091 / 625000000000000 : ℝ) (Real.pi * Real.exp (49 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell784_product_lower
  have hD : Real.exp (Real.pi * Real.exp (157 / 160 : ℝ) - (49 / 200 : ℝ)) ≤
      (273247580661 / 80000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell784_denomUpper
    linarith [hpThetaJensenCell784_product_upper]
  have hi : (1 / (273247580661 / 80000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (157 / 160 : ℝ) - (49 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (273247580661 / 80000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (273247580661 / 80000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 200 : ℝ) - Real.pi * Real.exp (157 / 160 : ℝ)) := by
    rw [show (49 / 200 : ℝ) - Real.pi * Real.exp (157 / 160 : ℝ) =
      -(Real.pi * Real.exp (157 / 160 : ℝ) - (49 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 50 : ℝ)) := by
    have h := hpThetaJensenCell784_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (273247580661 / 80000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell784_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 100 : ℝ) (157 / 320 : ℝ) ≤ (684509423 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (157 / 160 : ℝ)) (20952767293453541 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (157 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell784_product_upper
  have hD : (16894777441173 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 50 : ℝ) - (157 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell784_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell784_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 50 : ℝ) - (157 / 640 : ℝ)) ≤
      (1 / (16894777441173 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (16894777441173 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((157 / 640 : ℝ) - Real.pi * Real.exp (49 / 50 : ℝ)) ≤
      (2 / (16894777441173 / 5000000000 : ℝ) : ℝ) := by
    rw [show (157 / 640 : ℝ) - Real.pi * Real.exp (49 / 50 : ℝ) =
      -(Real.pi * Real.exp (49 / 50 : ℝ) - (157 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20952767293453541 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (20952767293453541 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell784_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 100 : ℝ) (157 / 320 : ℝ)) :
    (336758737 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (684509423 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell784_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell784_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell785_leftExp :
    (13338944473 / 5000000000 : ℝ) ≤ Real.exp (157 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (157 / 160 : ℝ) (515569523711 / 500000000000 : ℝ)
    (13338944473 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell785_rightExp :
    Real.exp (393 / 400 : ℝ) ≤ (667781429 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (393 / 400 : ℝ) (515589663539 / 500000000000 : ℝ)
    (667781429 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell785_denomUpper :
    Real.exp (2036569337876397 / 250000000000000 : ℝ) ≤ (17252550454187 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2036569337876397 / 250000000000000 : ℝ) (1289908347287 /
    1000000000000 : ℝ) (17252550454187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell785_denomLower :
    (34134515699161 / 10000000000 : ℝ) ≤ Real.exp (5084674530602627 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5084674530602627 / 625000000000000 : ℝ) (257894630627 /
    200000000000 : ℝ) (34134515699161 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell785_product_lower :
    (5238190155602627 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (157 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell785_leftExp
    (by norm_num : (0 : ℝ) ≤ (13338944473 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell785_product_upper :
    Real.pi * Real.exp (393 / 400 : ℝ) ≤ (2097897462876397 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell785_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell785_endpointLower :
    (1337106701 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (157 / 320 : ℝ) (393 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5238190155602627 / 625000000000000 : ℝ) (Real.pi * Real.exp (157 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell785_product_lower
  have hD : Real.exp (Real.pi * Real.exp (393 / 400 : ℝ) - (157 / 640 : ℝ)) ≤
      (17252550454187 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell785_denomUpper
    linarith [hpThetaJensenCell785_product_upper]
  have hi : (1 / (17252550454187 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (393 / 400 : ℝ) - (157 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17252550454187 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17252550454187 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((157 / 640 : ℝ) - Real.pi * Real.exp (393 / 400 : ℝ)) := by
    rw [show (157 / 640 : ℝ) - Real.pi * Real.exp (393 / 400 : ℝ) =
      -(Real.pi * Real.exp (393 / 400 : ℝ) - (157 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (157 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (157 / 160 : ℝ)) := by
    have h := hpThetaJensenCell785_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17252550454187 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell785_endpointUpper :
    hpThetaJensenKernelEndpointUpper (157 / 320 : ℝ) (393 / 800 : ℝ) ≤ (339736451 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (393 / 400 : ℝ)) (2097897462876397 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (393 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell785_product_upper
  have hD : (34134515699161 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (157 / 160 : ℝ) - (393 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell785_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell785_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (157 / 160 : ℝ) - (393 / 1600 : ℝ)) ≤
      (1 / (34134515699161 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (34134515699161 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((393 / 1600 : ℝ) - Real.pi * Real.exp (157 / 160 : ℝ)) ≤
      (2 / (34134515699161 / 10000000000 : ℝ) : ℝ) := by
    rw [show (393 / 1600 : ℝ) - Real.pi * Real.exp (157 / 160 : ℝ) =
      -(Real.pi * Real.exp (157 / 160 : ℝ) - (393 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2097897462876397 / 250000000000000 : ℝ) ^ 2 - 6 *
      (2097897462876397 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell785_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (157 / 320 : ℝ) (393 / 800 : ℝ)) :
    (1337106701 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (339736451 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell785_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell785_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell786_leftExp :
    (13355628579 / 5000000000 : ℝ) ≤ Real.exp (393 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (393 / 400 : ℝ) (1031179327077 / 1000000000000 : ℝ)
    (13355628579 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell786_rightExp :
    Real.exp (787 / 800 : ℝ) ≤ (26744667109 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (787 / 800 : ℝ) (257804902077 / 250000000000 : ℝ)
    (26744667109 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell786_denomUpper :
    Real.exp (81564608976964637 / 10000000000000000 : ℝ) ≤ (8714570113873 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81564608976964637 / 10000000000000000 : ℝ) (25806378153
    / 20000000000 : ℝ) (8714570113873 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell786_denomLower :
    (34483449825651 / 10000000000 : ℝ) ≤ Real.exp (5091031049844721 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5091031049844721 / 625000000000000 : ℝ) (644941523157 /
    500000000000 : ℝ) (34483449825651 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell786_product_lower :
    (5244741987344721 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (393 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell786_leftExp
    (by norm_num : (0 : ℝ) ≤ (13355628579 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell786_product_upper :
    Real.pi * Real.exp (787 / 800 : ℝ) ≤ (84020858976964637 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell786_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell786_endpointLower :
    (53089347 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (393 / 800 : ℝ) (787 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5244741987344721 / 625000000000000 : ℝ) (Real.pi * Real.exp (393 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell786_product_lower
  have hD : Real.exp (Real.pi * Real.exp (787 / 800 : ℝ) - (393 / 1600 : ℝ)) ≤
      (8714570113873 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell786_denomUpper
    linarith [hpThetaJensenCell786_product_upper]
  have hi : (1 / (8714570113873 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (787 / 800 : ℝ) - (393 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8714570113873 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8714570113873 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((393 / 1600 : ℝ) - Real.pi * Real.exp (787 / 800 : ℝ)) := by
    rw [show (393 / 1600 : ℝ) - Real.pi * Real.exp (787 / 800 : ℝ) =
      -(Real.pi * Real.exp (787 / 800 : ℝ) - (393 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (393 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (393 / 400 : ℝ)) := by
    have h := hpThetaJensenCell786_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8714570113873 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell786_endpointUpper :
    hpThetaJensenKernelEndpointUpper (393 / 800 : ℝ) (787 / 1600 : ℝ) ≤ (674464327 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (787 / 800 : ℝ)) (84020858976964637 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (787 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell786_product_upper
  have hD : (34483449825651 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (393 / 400 : ℝ) - (787 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell786_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell786_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (393 / 400 : ℝ) - (787 / 3200 : ℝ)) ≤
      (1 / (34483449825651 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (34483449825651 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((787 / 3200 : ℝ) - Real.pi * Real.exp (393 / 400 : ℝ)) ≤
      (2 / (34483449825651 / 10000000000 : ℝ) : ℝ) := by
    rw [show (787 / 3200 : ℝ) - Real.pi * Real.exp (393 / 400 : ℝ) =
      -(Real.pi * Real.exp (393 / 400 : ℝ) - (787 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (84020858976964637 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (84020858976964637 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell786_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (393 / 800 : ℝ) (787 / 1600 : ℝ)) :
    (53089347 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (674464327 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell786_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell786_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell787_leftExp :
    (26744667107 / 10000000000 : ℝ) ≤ Real.exp (787 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (787 / 800 : ℝ) (1031219608307 / 1000000000000 : ℝ)
    (26744667107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell787_rightExp :
    Real.exp (197 / 200 : ℝ) ≤ (5355623769 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (197 / 200 : ℝ) (103125989111 / 100000000000 : ℝ)
    (5355623769 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell787_denomUpper :
    Real.exp (16333315143324017 / 2000000000000000 : ℝ) ≤ (34390173141 / 9765625 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16333315143324017 / 2000000000000000 : ℝ) (1290730128201
    / 1000000000000 : ℝ) (34390173141 / 9765625 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell787_denomLower :
    (435455095571 / 125000000 : ℝ) ≤ Real.exp (10194791528251793 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10194791528251793 / 1250000000000000 : ℝ) (129029359849
    / 100000000000 : ℝ) (435455095571 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell787_product_lower :
    (10502604028251793 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (787 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell787_leftExp
    (by norm_num : (0 : ℝ) ≤ (26744667107 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell787_product_upper :
    Real.pi * Real.exp (197 / 200 : ℝ) ≤ (16825190143324017 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell787_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell787_endpointLower :
    (1317415711 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (787 / 1600 : ℝ) (197 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10502604028251793 / 1250000000000000 : ℝ) (Real.pi * Real.exp (787 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell787_product_lower
  have hD : Real.exp (Real.pi * Real.exp (197 / 200 : ℝ) - (787 / 3200 : ℝ)) ≤
      (34390173141 / 9765625 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell787_denomUpper
    linarith [hpThetaJensenCell787_product_upper]
  have hi : (1 / (34390173141 / 9765625 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (197 / 200 : ℝ) - (787 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (34390173141 / 9765625 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (34390173141 / 9765625 : ℝ) : ℝ) ≤
      2 * Real.exp ((787 / 3200 : ℝ) - Real.pi * Real.exp (197 / 200 : ℝ)) := by
    rw [show (787 / 3200 : ℝ) - Real.pi * Real.exp (197 / 200 : ℝ) =
      -(Real.pi * Real.exp (197 / 200 : ℝ) - (787 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (787 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (787 / 800 : ℝ)) := by
    have h := hpThetaJensenCell787_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (34390173141 / 9765625 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell787_endpointUpper :
    hpThetaJensenKernelEndpointUpper (787 / 1600 : ℝ) (197 / 400 : ℝ) ≤ (1338967233 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (197 / 200 : ℝ)) (16825190143324017 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (197 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell787_product_upper
  have hD : (435455095571 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (787 / 800 : ℝ) - (197 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell787_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell787_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (787 / 800 : ℝ) - (197 / 800 : ℝ)) ≤
      (1 / (435455095571 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (435455095571 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((197 / 800 : ℝ) - Real.pi * Real.exp (787 / 800 : ℝ)) ≤
      (2 / (435455095571 / 125000000 : ℝ) : ℝ) := by
    rw [show (197 / 800 : ℝ) - Real.pi * Real.exp (787 / 800 : ℝ) =
      -(Real.pi * Real.exp (787 / 800 : ℝ) - (197 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16825190143324017 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (16825190143324017 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell787_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (787 / 1600 : ℝ) (197 / 400 : ℝ)) :
    (1317415711 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1338967233 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell787_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell787_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell788_leftExp :
    (26778118843 / 10000000000 : ℝ) ≤ Real.exp (197 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (197 / 200 : ℝ) (1031259891109 / 1000000000000 : ℝ)
    (26778118843 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell788_rightExp :
    Real.exp (789 / 800 : ℝ) ≤ (26811612423 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (789 / 800 : ℝ) (1031300175487 / 1000000000000 : ℝ)
    (26811612423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell788_denomUpper :
    Real.exp (81768673906809839 / 10000000000000000 : ℝ) ≤ (35576923262251 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (81768673906809839 / 10000000000000000 : ℝ) (645571005093
    / 500000000000 : ℝ) (35576923262251 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell788_denomLower :
    (35193440197869 / 10000000000 : ℝ) ≤ Real.exp (10207537366527257 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10207537366527257 / 1250000000000000 : ℝ) (32267620271 /
    25000000000 : ℝ) (35193440197869 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell788_product_lower :
    (10515740491527257 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (197 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell788_leftExp
    (by norm_num : (0 : ℝ) ≤ (26778118843 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell788_product_upper :
    Real.pi * Real.exp (789 / 800 : ℝ) ≤ (84231173906809839 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell788_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell788_endpointLower :
    (1307652643 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (197 / 400 : ℝ) (789 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10515740491527257 / 1250000000000000 : ℝ) (Real.pi * Real.exp (197 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell788_product_lower
  have hD : Real.exp (Real.pi * Real.exp (789 / 800 : ℝ) - (197 / 800 : ℝ)) ≤
      (35576923262251 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell788_denomUpper
    linarith [hpThetaJensenCell788_product_upper]
  have hi : (1 / (35576923262251 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (789 / 800 : ℝ) - (197 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (35576923262251 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (35576923262251 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((197 / 800 : ℝ) - Real.pi * Real.exp (789 / 800 : ℝ)) := by
    rw [show (197 / 800 : ℝ) - Real.pi * Real.exp (789 / 800 : ℝ) =
      -(Real.pi * Real.exp (789 / 800 : ℝ) - (197 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (197 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (197 / 200 : ℝ)) := by
    have h := hpThetaJensenCell788_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (35576923262251 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell788_endpointUpper :
    hpThetaJensenKernelEndpointUpper (197 / 400 : ℝ) (789 / 1600 : ℝ) ≤ (664530689 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (789 / 800 : ℝ)) (84231173906809839 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (789 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell788_product_upper
  have hD : (35193440197869 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (197 / 200 : ℝ) - (789 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell788_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell788_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (197 / 200 : ℝ) - (789 / 3200 : ℝ)) ≤
      (1 / (35193440197869 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35193440197869 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((789 / 3200 : ℝ) - Real.pi * Real.exp (197 / 200 : ℝ)) ≤
      (2 / (35193440197869 / 10000000000 : ℝ) : ℝ) := by
    rw [show (789 / 3200 : ℝ) - Real.pi * Real.exp (197 / 200 : ℝ) =
      -(Real.pi * Real.exp (197 / 200 : ℝ) - (789 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (84231173906809839 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (84231173906809839 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell788_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (197 / 400 : ℝ) (789 / 1600 : ℝ)) :
    (1307652643 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (664530689 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell788_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell788_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell789_leftExp :
    (26811612421 / 10000000000 : ℝ) ≤ Real.exp (789 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (789 / 800 : ℝ) (515650087743 / 500000000000 : ℝ)
    (26811612421 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell789_rightExp :
    Real.exp (79 / 80 : ℝ) ≤ (13422573947 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (79 / 80 : ℝ) (1031340461437 / 1000000000000 : ℝ)
    (13422573947 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell789_denomUpper :
    Real.exp (40935451853877571 / 5000000000000000 : ℝ) ≤ (7188498170413 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (40935451853877571 / 5000000000000000 : ℝ) (1291554554801
    / 1000000000000 : ℝ) (7188498170413 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell789_denomLower :
    (35554599281731 / 10000000000 : ℝ) ≤ Real.exp (10220299636114279 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10220299636114279 / 1250000000000000 : ℝ) (1291116684611
    / 1000000000000 : ℝ) (35554599281731 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell789_product_lower :
    (10528893386114279 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (789 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell789_leftExp
    (by norm_num : (0 : ℝ) ≤ (26811612421 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell789_product_upper :
    Real.pi * Real.exp (79 / 80 : ℝ) ≤ (42168264353877571 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell789_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell789_endpointLower :
    (1297944309 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (789 / 1600 : ℝ) (79 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10528893386114279 / 1250000000000000 : ℝ) (Real.pi * Real.exp (789 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell789_product_lower
  have hD : Real.exp (Real.pi * Real.exp (79 / 80 : ℝ) - (789 / 3200 : ℝ)) ≤
      (7188498170413 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell789_denomUpper
    linarith [hpThetaJensenCell789_product_upper]
  have hi : (1 / (7188498170413 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (79 / 80 : ℝ) - (789 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7188498170413 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7188498170413 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((789 / 3200 : ℝ) - Real.pi * Real.exp (79 / 80 : ℝ)) := by
    rw [show (789 / 3200 : ℝ) - Real.pi * Real.exp (79 / 80 : ℝ) =
      -(Real.pi * Real.exp (79 / 80 : ℝ) - (789 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (789 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (789 / 800 : ℝ)) := by
    have h := hpThetaJensenCell789_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7188498170413 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell789_endpointUpper :
    hpThetaJensenKernelEndpointUpper (789 / 1600 : ℝ) (79 / 160 : ℝ) ≤ (329802731 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (79 / 80 : ℝ)) (42168264353877571 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (79 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell789_product_upper
  have hD : (35554599281731 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (789 / 800 : ℝ) - (79 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell789_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell789_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (789 / 800 : ℝ) - (79 / 320 : ℝ)) ≤
      (1 / (35554599281731 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35554599281731 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((79 / 320 : ℝ) - Real.pi * Real.exp (789 / 800 : ℝ)) ≤
      (2 / (35554599281731 / 10000000000 : ℝ) : ℝ) := by
    rw [show (79 / 320 : ℝ) - Real.pi * Real.exp (789 / 800 : ℝ) =
      -(Real.pi * Real.exp (789 / 800 : ℝ) - (79 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42168264353877571 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (42168264353877571 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell789_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (789 / 1600 : ℝ) (79 / 160 : ℝ)) :
    (1297944309 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (329802731 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell789_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell789_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell790_leftExp :
    (6711286973 / 2500000000 : ℝ) ≤ Real.exp (79 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (79 / 80 : ℝ) (257835115359 / 250000000000 : ℝ)
    (6711286973 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell790_rightExp :
    Real.exp (791 / 800 : ℝ) ≤ (2687872531 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (791 / 800 : ℝ) (6446129681 / 6250000000 : ℝ)
    (2687872531 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell790_denomUpper :
    Real.exp (8197326528281883 / 1000000000000000 : ℝ) ≤ (18156146649181 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8197326528281883 / 1000000000000000 : ℝ) (161495970407 /
    125000000000 : ℝ) (18156146649181 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell790_denomLower :
    (35919937362387 / 10000000000 : ℝ) ≤ Real.exp (2558269589260127 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2558269589260127 / 312500000000000 : ℝ) (645764610499 /
    500000000000 : ℝ) (35919937362387 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell790_product_lower :
    (2635515683010127 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (79 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell790_leftExp
    (by norm_num : (0 : ℝ) ≤ (6711286973 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell790_product_upper :
    Real.pi * Real.exp (791 / 800 : ℝ) ≤ (8444201528281883 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell790_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell790_endpointLower :
    (257658109 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 160 : ℝ) (791 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2635515683010127 / 312500000000000 : ℝ) (Real.pi * Real.exp (79 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell790_product_lower
  have hD : Real.exp (Real.pi * Real.exp (791 / 800 : ℝ) - (79 / 320 : ℝ)) ≤
      (18156146649181 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell790_denomUpper
    linarith [hpThetaJensenCell790_product_upper]
  have hi : (1 / (18156146649181 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (791 / 800 : ℝ) - (79 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18156146649181 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18156146649181 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((79 / 320 : ℝ) - Real.pi * Real.exp (791 / 800 : ℝ)) := by
    rw [show (79 / 320 : ℝ) - Real.pi * Real.exp (791 / 800 : ℝ) =
      -(Real.pi * Real.exp (791 / 800 : ℝ) - (79 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (79 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (79 / 80 : ℝ)) := by
    have h := hpThetaJensenCell790_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18156146649181 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell790_endpointUpper :
    hpThetaJensenKernelEndpointUpper (79 / 160 : ℝ) (791 / 1600 : ℝ) ≤ (261883141 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (791 / 800 : ℝ)) (8444201528281883 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (791 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell790_product_upper
  have hD : (35919937362387 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (79 / 80 : ℝ) - (791 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell790_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell790_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (79 / 80 : ℝ) - (791 / 3200 : ℝ)) ≤
      (1 / (35919937362387 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35919937362387 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((791 / 3200 : ℝ) - Real.pi * Real.exp (79 / 80 : ℝ)) ≤
      (2 / (35919937362387 / 10000000000 : ℝ) : ℝ) := by
    rw [show (791 / 3200 : ℝ) - Real.pi * Real.exp (79 / 80 : ℝ) =
      -(Real.pi * Real.exp (79 / 80 : ℝ) - (791 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8444201528281883 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (8444201528281883 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell790_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (79 / 160 : ℝ) (791 / 1600 : ℝ)) :
    (257658109 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (261883141 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell790_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell790_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell791_leftExp :
    (6719681327 / 2500000000 : ℝ) ≤ Real.exp (791 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (791 / 800 : ℝ) (1031380748959 / 1000000000000 : ℝ)
    (6719681327 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell791_rightExp :
    Real.exp (99 / 100 : ℝ) ≤ (1076493789 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (99 / 100 : ℝ) (515710519029 / 500000000000 : ℝ)
    (1076493789 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell791_denomUpper :
    Real.exp (3283030352065877 / 400000000000000 : ℝ) ≤ (36686384592061 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3283030352065877 / 400000000000000 : ℝ) (129238163679 /
    100000000000 : ℝ) (36686384592061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell791_denomLower :
    (36289507640723 / 10000000000 : ℝ) ≤ Real.exp (2561468387431573 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2561468387431573 / 312500000000000 : ℝ) (1291942421213 /
    1000000000000 : ℝ) (36289507640723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell791_product_lower :
    (2638812137431573 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (791 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell791_leftExp
    (by norm_num : (0 : ℝ) ≤ (6719681327 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell791_product_upper :
    Real.pi * Real.exp (99 / 100 : ℝ) ≤ (3381905352065877 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell791_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell791_endpointLower :
    (639345593 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (791 / 1600 : ℝ) (99 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2638812137431573 / 312500000000000 : ℝ) (Real.pi * Real.exp (791 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell791_product_lower
  have hD : Real.exp (Real.pi * Real.exp (99 / 100 : ℝ) - (791 / 3200 : ℝ)) ≤
      (36686384592061 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell791_denomUpper
    linarith [hpThetaJensenCell791_product_upper]
  have hi : (1 / (36686384592061 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (99 / 100 : ℝ) - (791 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (36686384592061 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (36686384592061 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((791 / 3200 : ℝ) - Real.pi * Real.exp (99 / 100 : ℝ)) := by
    rw [show (791 / 3200 : ℝ) - Real.pi * Real.exp (99 / 100 : ℝ) =
      -(Real.pi * Real.exp (99 / 100 : ℝ) - (791 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (791 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (791 / 800 : ℝ)) := by
    have h := hpThetaJensenCell791_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (36686384592061 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell791_endpointUpper :
    hpThetaJensenKernelEndpointUpper (791 / 1600 : ℝ) (99 / 200 : ℝ) ≤ (324918889 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (99 / 100 : ℝ)) (3381905352065877 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (99 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell791_product_upper
  have hD : (36289507640723 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (791 / 800 : ℝ) - (99 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell791_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell791_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (791 / 800 : ℝ) - (99 / 400 : ℝ)) ≤
      (1 / (36289507640723 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (36289507640723 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((99 / 400 : ℝ) - Real.pi * Real.exp (791 / 800 : ℝ)) ≤
      (2 / (36289507640723 / 10000000000 : ℝ) : ℝ) := by
    rw [show (99 / 400 : ℝ) - Real.pi * Real.exp (791 / 800 : ℝ) =
      -(Real.pi * Real.exp (791 / 800 : ℝ) - (99 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3381905352065877 / 400000000000000 : ℝ) ^ 2 - 6 *
      (3381905352065877 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell791_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (791 / 1600 : ℝ) (99 / 200 : ℝ)) :
    (639345593 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (324918889 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell791_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell791_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell792_leftExp :
    (26912344723 / 10000000000 : ℝ) ≤ Real.exp (99 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (99 / 100 : ℝ) (1031421038057 / 1000000000000 : ℝ)
    (26912344723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell792_rightExp :
    Real.exp (793 / 800 : ℝ) ≤ (26946006189 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (793 / 800 : ℝ) (1031461328729 / 1000000000000 : ℝ)
    (26946006189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell792_denomUpper :
    Real.exp (82178384421319077 / 10000000000000000 : ℝ) ≤ (18532409710563 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (82178384421319077 / 10000000000000000 : ℝ)
    (1292796176591 / 1000000000000 : ℝ) (18532409710563 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell792_denomLower :
    (18331682035987 / 5000000000 : ℝ) ≤ Real.exp (10258685235377377 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10258685235377377 / 1250000000000000 : ℝ) (1292356286493
    / 1000000000000 : ℝ) (18331682035987 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell792_product_lower :
    (10568450860377377 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (99 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell792_leftExp
    (by norm_num : (0 : ℝ) ≤ (26912344723 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell792_product_upper :
    Real.pi * Real.exp (793 / 800 : ℝ) ≤ (84653384421319077 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell792_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell792_endpointLower :
    (1269146067 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 200 : ℝ) (793 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10568450860377377 / 1250000000000000 : ℝ) (Real.pi * Real.exp (99 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell792_product_lower
  have hD : Real.exp (Real.pi * Real.exp (793 / 800 : ℝ) - (99 / 400 : ℝ)) ≤
      (18532409710563 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell792_denomUpper
    linarith [hpThetaJensenCell792_product_upper]
  have hi : (1 / (18532409710563 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (793 / 800 : ℝ) - (99 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18532409710563 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18532409710563 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((99 / 400 : ℝ) - Real.pi * Real.exp (793 / 800 : ℝ)) := by
    rw [show (99 / 400 : ℝ) - Real.pi * Real.exp (793 / 800 : ℝ) =
      -(Real.pi * Real.exp (793 / 800 : ℝ) - (99 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (99 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (99 / 100 : ℝ)) := by
    have h := hpThetaJensenCell792_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18532409710563 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell792_endpointUpper :
    hpThetaJensenKernelEndpointUpper (99 / 200 : ℝ) (793 / 1600 : ℝ) ≤ (1289990311 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (793 / 800 : ℝ)) (84653384421319077 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (793 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell792_product_upper
  have hD : (18331682035987 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (99 / 100 : ℝ) - (793 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell792_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell792_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (99 / 100 : ℝ) - (793 / 3200 : ℝ)) ≤
      (1 / (18331682035987 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18331682035987 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((793 / 3200 : ℝ) - Real.pi * Real.exp (99 / 100 : ℝ)) ≤
      (2 / (18331682035987 / 5000000000 : ℝ) : ℝ) := by
    rw [show (793 / 3200 : ℝ) - Real.pi * Real.exp (99 / 100 : ℝ) =
      -(Real.pi * Real.exp (99 / 100 : ℝ) - (793 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (84653384421319077 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (84653384421319077 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell792_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (99 / 200 : ℝ) (793 / 1600 : ℝ)) :
    (1269146067 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1289990311 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell792_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell792_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell793_leftExp :
    (6736501547 / 2500000000 : ℝ) ≤ Real.exp (793 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (793 / 800 : ℝ) (128932666091 / 125000000000 : ℝ)
    (6736501547 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell793_rightExp :
    Real.exp (397 / 400 : ℝ) ≤ (26979709757 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (397 / 400 : ℝ) (515750810487 / 500000000000 : ℝ)
    (26979709757 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell793_denomUpper :
    Real.exp (82281142314622901 / 10000000000000000 : ℝ) ≤ (18723826644253 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (82281142314622901 / 10000000000000000 : ℝ) (646605691957
    / 500000000000 : ℝ) (18723826644253 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell793_denomLower :
    (37041561322577 / 10000000000 : ℝ) ≤ Real.exp (2567878358505353 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2567878358505353 / 312500000000000 : ℝ) (32319270451 /
    25000000000 : ℝ) (37041561322577 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell793_product_lower :
    (2645417421005353 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (793 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell793_leftExp
    (by norm_num : (0 : ℝ) ≤ (6736501547 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell793_product_upper :
    Real.pi * Real.exp (397 / 400 : ℝ) ≤ (84759267314622901 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell793_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell793_endpointLower :
    (629827511 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (793 / 1600 : ℝ) (397 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2645417421005353 / 312500000000000 : ℝ) (Real.pi * Real.exp (793 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell793_product_lower
  have hD : Real.exp (Real.pi * Real.exp (397 / 400 : ℝ) - (793 / 3200 : ℝ)) ≤
      (18723826644253 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell793_denomUpper
    linarith [hpThetaJensenCell793_product_upper]
  have hi : (1 / (18723826644253 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (397 / 400 : ℝ) - (793 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18723826644253 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18723826644253 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((793 / 3200 : ℝ) - Real.pi * Real.exp (397 / 400 : ℝ)) := by
    rw [show (793 / 3200 : ℝ) - Real.pi * Real.exp (397 / 400 : ℝ) =
      -(Real.pi * Real.exp (397 / 400 : ℝ) - (793 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (793 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (793 / 800 : ℝ)) := by
    have h := hpThetaJensenCell793_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18723826644253 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell793_endpointUpper :
    hpThetaJensenKernelEndpointUpper (793 / 1600 : ℝ) (397 / 800 : ℝ) ≤ (640179901 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (397 / 400 : ℝ)) (84759267314622901 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (397 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell793_product_upper
  have hD : (37041561322577 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (793 / 800 : ℝ) - (397 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell793_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell793_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (793 / 800 : ℝ) - (397 / 1600 : ℝ)) ≤
      (1 / (37041561322577 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (37041561322577 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((397 / 1600 : ℝ) - Real.pi * Real.exp (793 / 800 : ℝ)) ≤
      (2 / (37041561322577 / 10000000000 : ℝ) : ℝ) := by
    rw [show (397 / 1600 : ℝ) - Real.pi * Real.exp (793 / 800 : ℝ) =
      -(Real.pi * Real.exp (793 / 800 : ℝ) - (397 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (84759267314622901 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (84759267314622901 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell793_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (793 / 1600 : ℝ) (397 / 800 : ℝ)) :
    (629827511 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (640179901 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell793_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell793_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell794_leftExp :
    (6744927439 / 2500000000 : ℝ) ≤ Real.exp (397 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (397 / 400 : ℝ) (1031501620973 / 1000000000000 : ℝ)
    (6744927439 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell794_rightExp :
    Real.exp (159 / 160 : ℝ) ≤ (27013455481 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (159 / 160 : ℝ) (1031541914793 / 1000000000000 : ℝ)
    (27013455481 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell794_denomUpper :
    Real.exp (82384032644921233 / 10000000000000000 : ℝ) ≤ (37834942428961 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (82384032644921233 / 10000000000000000 : ℝ)
    (1293627259977 / 1000000000000 : ℝ) (37834942428961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell794_denomLower :
    (3742415483599 / 1000000000 : ℝ) ≤ Real.exp (2571089541617861 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2571089541617861 / 312500000000000 : ℝ) (646593008541 /
    500000000000 : ℝ) (3742415483599 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell794_product_lower :
    (2648726260367861 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (397 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell794_leftExp
    (by norm_num : (0 : ℝ) ≤ (6744927439 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell794_product_upper :
    Real.pi * Real.exp (159 / 160 : ℝ) ≤ (84865282644921233 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell794_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell794_endpointLower :
    (250043577 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (397 / 800 : ℝ) (159 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2648726260367861 / 312500000000000 : ℝ) (Real.pi * Real.exp (397 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell794_product_lower
  have hD : Real.exp (Real.pi * Real.exp (159 / 160 : ℝ) - (397 / 1600 : ℝ)) ≤
      (37834942428961 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell794_denomUpper
    linarith [hpThetaJensenCell794_product_upper]
  have hi : (1 / (37834942428961 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (159 / 160 : ℝ) - (397 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (37834942428961 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (37834942428961 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((397 / 1600 : ℝ) - Real.pi * Real.exp (159 / 160 : ℝ)) := by
    rw [show (397 / 1600 : ℝ) - Real.pi * Real.exp (159 / 160 : ℝ) =
      -(Real.pi * Real.exp (159 / 160 : ℝ) - (397 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (397 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (397 / 400 : ℝ)) := by
    have h := hpThetaJensenCell794_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (37834942428961 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell794_endpointUpper :
    hpThetaJensenKernelEndpointUpper (397 / 800 : ℝ) (159 / 320 : ℝ) ≤ (158847983 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (159 / 160 : ℝ)) (84865282644921233 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (159 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell794_product_upper
  have hD : (3742415483599 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (397 / 400 : ℝ) - (159 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell794_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell794_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (397 / 400 : ℝ) - (159 / 640 : ℝ)) ≤
      (1 / (3742415483599 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3742415483599 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((159 / 640 : ℝ) - Real.pi * Real.exp (397 / 400 : ℝ)) ≤
      (2 / (3742415483599 / 1000000000 : ℝ) : ℝ) := by
    rw [show (159 / 640 : ℝ) - Real.pi * Real.exp (397 / 400 : ℝ) =
      -(Real.pi * Real.exp (397 / 400 : ℝ) - (159 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (84865282644921233 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (84865282644921233 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell794_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (397 / 800 : ℝ) (159 / 320 : ℝ)) :
    (250043577 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (158847983 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell794_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell794_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell795_leftExp :
    (27013455479 / 10000000000 : ℝ) ≤ Real.exp (159 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (159 / 160 : ℝ) (128942739349 / 125000000000 : ℝ)
    (27013455479 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell795_rightExp :
    Real.exp (199 / 200 : ℝ) ≤ (13523621707 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (199 / 200 : ℝ) (515791105093 / 500000000000 : ℝ)
    (13523621707 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell795_denomUpper :
    Real.exp (41243527789359251 / 5000000000000000 : ℝ) ≤ (38226743867787 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41243527789359251 / 5000000000000000 : ℝ) (1294043806013
    / 1000000000000 : ℝ) (38226743867787 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell795_denomLower :
    (18905600406111 / 5000000000 : ℝ) ≤ Real.exp (10297219453147821 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10297219453147821 / 1250000000000000 : ℝ) (646800942419
    / 500000000000 : ℝ) (18905600406111 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell795_product_lower :
    (10608156953147821 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (159 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell795_leftExp
    (by norm_num : (0 : ℝ) ≤ (27013455479 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell795_product_upper :
    Real.pi * Real.exp (199 / 200 : ℝ) ≤ (42485715289359251 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell795_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell795_endpointLower :
    (1240834489 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (159 / 320 : ℝ) (199 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10608156953147821 / 1250000000000000 : ℝ) (Real.pi * Real.exp (159 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell795_product_lower
  have hD : Real.exp (Real.pi * Real.exp (199 / 200 : ℝ) - (159 / 640 : ℝ)) ≤
      (38226743867787 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell795_denomUpper
    linarith [hpThetaJensenCell795_product_upper]
  have hi : (1 / (38226743867787 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (199 / 200 : ℝ) - (159 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (38226743867787 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (38226743867787 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((159 / 640 : ℝ) - Real.pi * Real.exp (199 / 200 : ℝ)) := by
    rw [show (159 / 640 : ℝ) - Real.pi * Real.exp (199 / 200 : ℝ) =
      -(Real.pi * Real.exp (199 / 200 : ℝ) - (159 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (159 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (159 / 160 : ℝ)) := by
    have h := hpThetaJensenCell795_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (38226743867787 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell795_endpointUpper :
    hpThetaJensenKernelEndpointUpper (159 / 320 : ℝ) (199 / 400 : ℝ) ≤ (1261262327 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (199 / 200 : ℝ)) (42485715289359251 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (199 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell795_product_upper
  have hD : (18905600406111 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (159 / 160 : ℝ) - (199 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell795_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell795_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (159 / 160 : ℝ) - (199 / 800 : ℝ)) ≤
      (1 / (18905600406111 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18905600406111 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((199 / 800 : ℝ) - Real.pi * Real.exp (159 / 160 : ℝ)) ≤
      (2 / (18905600406111 / 5000000000 : ℝ) : ℝ) := by
    rw [show (199 / 800 : ℝ) - Real.pi * Real.exp (159 / 160 : ℝ) =
      -(Real.pi * Real.exp (159 / 160 : ℝ) - (199 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42485715289359251 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (42485715289359251 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell795_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (159 / 320 : ℝ) (199 / 400 : ℝ)) :
    (1240834489 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1261262327 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell795_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell795_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell796_leftExp :
    (6761810853 / 2500000000 : ℝ) ≤ Real.exp (199 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (199 / 200 : ℝ) (206316442037 / 200000000000 : ℝ)
    (6761810853 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell796_rightExp :
    Real.exp (797 / 800 : ℝ) ≤ (27081073607 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (797 / 800 : ℝ) (1031622507153 / 1000000000000 : ℝ)
    (27081073607 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell796_denomUpper :
    Real.exp (82590211276235951 / 10000000000000000 : ℝ) ≤ (965577884869 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (82590211276235951 / 10000000000000000 : ℝ) (129446102323
    / 100000000000 : ℝ) (965577884869 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell796_denomLower :
    (2387672266501 / 625000000 : ℝ) ≤ Real.exp (2577524328912247 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2577524328912247 / 312500000000000 : ℝ) (647009211283 /
    500000000000 : ℝ) (2387672266501 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell796_product_lower :
    (2655356360162247 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (199 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell796_leftExp
    (by norm_num : (0 : ℝ) ≤ (6761810853 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell796_product_upper :
    Real.pi * Real.exp (797 / 800 : ℝ) ≤ (85077711276235951 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell796_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell796_endpointLower :
    (307876167 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (199 / 400 : ℝ) (797 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2655356360162247 / 312500000000000 : ℝ) (Real.pi * Real.exp (199 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell796_product_lower
  have hD : Real.exp (Real.pi * Real.exp (797 / 800 : ℝ) - (199 / 800 : ℝ)) ≤
      (965577884869 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell796_denomUpper
    linarith [hpThetaJensenCell796_product_upper]
  have hi : (1 / (965577884869 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (797 / 800 : ℝ) - (199 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (965577884869 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (965577884869 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((199 / 800 : ℝ) - Real.pi * Real.exp (797 / 800 : ℝ)) := by
    rw [show (199 / 800 : ℝ) - Real.pi * Real.exp (797 / 800 : ℝ) =
      -(Real.pi * Real.exp (797 / 800 : ℝ) - (199 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (199 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (199 / 200 : ℝ)) := by
    have h := hpThetaJensenCell796_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (965577884869 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell796_endpointUpper :
    hpThetaJensenKernelEndpointUpper (199 / 400 : ℝ) (797 / 1600 : ℝ) ≤ (1251795023 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (797 / 800 : ℝ)) (85077711276235951 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (797 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell796_product_upper
  have hD : (2387672266501 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (199 / 200 : ℝ) - (797 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell796_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell796_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (199 / 200 : ℝ) - (797 / 3200 : ℝ)) ≤
      (1 / (2387672266501 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2387672266501 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((797 / 3200 : ℝ) - Real.pi * Real.exp (199 / 200 : ℝ)) ≤
      (2 / (2387672266501 / 625000000 : ℝ) : ℝ) := by
    rw [show (797 / 3200 : ℝ) - Real.pi * Real.exp (199 / 200 : ℝ) =
      -(Real.pi * Real.exp (199 / 200 : ℝ) - (797 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (85077711276235951 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (85077711276235951 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell796_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (199 / 400 : ℝ) (797 / 1600 : ℝ)) :
    (307876167 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1251795023 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell796_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell796_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell797_leftExp :
    (5416214721 / 2000000000 : ℝ) ≤ Real.exp (797 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (797 / 800 : ℝ) (64476406697 / 62500000000 : ℝ)
    (5416214721 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell797_rightExp :
    Real.exp (399 / 400 : ℝ) ≤ (5422989223 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (399 / 400 : ℝ) (515831402847 / 500000000000 : ℝ)
    (5422989223 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell797_denomUpper :
    Real.exp (16538699982052239 / 2000000000000000 : ℝ) ≤ (975602891269 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16538699982052239 / 2000000000000000 : ℝ) (129487891289
    / 100000000000 : ℝ) (975602891269 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell797_denomLower :
    (38598878933759 / 10000000000 : ℝ) ≤ Real.exp (2064598354721979 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2064598354721979 / 250000000000000 : ℝ) (647217815731 /
    500000000000 : ℝ) (38598878933759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell797_product_lower :
    (2126942104721979 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (797 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell797_leftExp
    (by norm_num : (0 : ℝ) ≤ (5416214721 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell797_product_upper :
    Real.pi * Real.exp (399 / 400 : ℝ) ≤ (17036824982052239 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell797_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell797_endpointLower :
    (305557063 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (797 / 1600 : ℝ) (399 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2126942104721979 / 250000000000000 : ℝ) (Real.pi * Real.exp (797 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell797_product_lower
  have hD : Real.exp (Real.pi * Real.exp (399 / 400 : ℝ) - (797 / 3200 : ℝ)) ≤
      (975602891269 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell797_denomUpper
    linarith [hpThetaJensenCell797_product_upper]
  have hi : (1 / (975602891269 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (399 / 400 : ℝ) - (797 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (975602891269 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (975602891269 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((797 / 3200 : ℝ) - Real.pi * Real.exp (399 / 400 : ℝ)) := by
    rw [show (797 / 3200 : ℝ) - Real.pi * Real.exp (399 / 400 : ℝ) =
      -(Real.pi * Real.exp (399 / 400 : ℝ) - (797 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (797 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (797 / 800 : ℝ)) := by
    have h := hpThetaJensenCell797_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (975602891269 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell797_endpointUpper :
    hpThetaJensenKernelEndpointUpper (797 / 1600 : ℝ) (399 / 800 : ℝ) ≤ (1242381783 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (399 / 400 : ℝ)) (17036824982052239 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (399 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell797_product_upper
  have hD : (38598878933759 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (797 / 800 : ℝ) - (399 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell797_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell797_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (797 / 800 : ℝ) - (399 / 1600 : ℝ)) ≤
      (1 / (38598878933759 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (38598878933759 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((399 / 1600 : ℝ) - Real.pi * Real.exp (797 / 800 : ℝ)) ≤
      (2 / (38598878933759 / 10000000000 : ℝ) : ℝ) := by
    rw [show (399 / 1600 : ℝ) - Real.pi * Real.exp (797 / 800 : ℝ) =
      -(Real.pi * Real.exp (797 / 800 : ℝ) - (399 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17036824982052239 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (17036824982052239 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell797_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (797 / 1600 : ℝ) (399 / 800 : ℝ)) :
    (305557063 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1242381783 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell797_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell797_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell798_leftExp :
    (27114946113 / 10000000000 : ℝ) ≤ Real.exp (399 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (399 / 400 : ℝ) (1031662805693 / 1000000000000 : ℝ)
    (27114946113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell798_rightExp :
    Real.exp (799 / 800 : ℝ) ≤ (2714886099 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (799 / 800 : ℝ) (103170310581 / 100000000000 : ℝ)
    (2714886099 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell798_denomUpper :
    Real.exp (8279692164415707 / 1000000000000000 : ℝ) ≤ (19714902027737 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8279692164415707 / 1000000000000000 : ℝ) (64764873811 /
    50000000000 : ℝ) (19714902027737 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell798_denomLower :
    (7799925485103 / 2000000000 : ℝ) ≤ Real.exp (10335902848628987 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10335902848628987 / 1250000000000000 : ℝ) (323713378197
    / 250000000000 : ℝ) (7799925485103 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell798_product_lower :
    (10648012223628987 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (399 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell798_leftExp
    (by norm_num : (0 : ℝ) ≤ (27114946113 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell798_product_upper :
    Real.pi * Real.exp (799 / 800 : ℝ) ≤ (8529067164415707 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell798_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell798_endpointLower :
    (606502537 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (399 / 800 : ℝ) (799 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10648012223628987 / 1250000000000000 : ℝ) (Real.pi * Real.exp (399 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell798_product_lower
  have hD : Real.exp (Real.pi * Real.exp (799 / 800 : ℝ) - (399 / 1600 : ℝ)) ≤
      (19714902027737 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell798_denomUpper
    linarith [hpThetaJensenCell798_product_upper]
  have hi : (1 / (19714902027737 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (799 / 800 : ℝ) - (399 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19714902027737 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19714902027737 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((399 / 1600 : ℝ) - Real.pi * Real.exp (799 / 800 : ℝ)) := by
    rw [show (399 / 1600 : ℝ) - Real.pi * Real.exp (799 / 800 : ℝ) =
      -(Real.pi * Real.exp (799 / 800 : ℝ) - (399 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (399 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (399 / 400 : ℝ)) := by
    have h := hpThetaJensenCell798_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19714902027737 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell798_endpointUpper :
    hpThetaJensenKernelEndpointUpper (399 / 800 : ℝ) (799 / 1600 : ℝ) ≤ (616511219 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (799 / 800 : ℝ)) (8529067164415707 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (799 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell798_product_upper
  have hD : (7799925485103 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (399 / 400 : ℝ) - (799 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell798_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell798_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (399 / 400 : ℝ) - (799 / 3200 : ℝ)) ≤
      (1 / (7799925485103 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7799925485103 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((799 / 3200 : ℝ) - Real.pi * Real.exp (399 / 400 : ℝ)) ≤
      (2 / (7799925485103 / 2000000000 : ℝ) : ℝ) := by
    rw [show (799 / 3200 : ℝ) - Real.pi * Real.exp (399 / 400 : ℝ) =
      -(Real.pi * Real.exp (399 / 400 : ℝ) - (799 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8529067164415707 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (8529067164415707 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell798_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (399 / 800 : ℝ) (799 / 1600 : ℝ)) :
    (606502537 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (616511219 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell798_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell798_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell799_leftExp :
    (27148860989 / 10000000000 : ℝ) ≤ Real.exp (799 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (799 / 800 : ℝ) (1031703105809 / 1000000000000 : ℝ)
    (27148860989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell799_rightExp :
    Real.exp (1 / 1 : ℝ) ≤ (13591409143 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1 / 1 : ℝ) (412697363 / 400000000 : ℝ)
    (13591409143 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell799_denomUpper :
    Real.exp (41450238323784799 / 5000000000000000 : ℝ) ≤ (19920120437879 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41450238323784799 / 5000000000000000 : ℝ) (1295716714471
    / 1000000000000 : ℝ) (19920120437879 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell799_denomLower :
    (4925632641669 / 1250000000 : ℝ) ≤ Real.exp (10348830561519311 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10348830561519311 / 1250000000000000 : ℝ) (1295272067783
    / 1000000000000 : ℝ) (4925632641669 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell799_product_lower :
    (10661330561519311 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (799 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell799_leftExp
    (by norm_num : (0 : ℝ) ≤ (27148860989 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell799_product_upper :
    Real.pi * Real.exp (1 / 1 : ℝ) ≤ (42698675823784799 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell799_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell799_endpointLower :
    (300958741 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (799 / 1600 : ℝ) (1 / 2 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (10661330561519311 / 1250000000000000 : ℝ) (Real.pi * Real.exp (799 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell799_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1 / 1 : ℝ) - (799 / 3200 : ℝ)) ≤
      (19920120437879 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell799_denomUpper
    linarith [hpThetaJensenCell799_product_upper]
  have hi : (1 / (19920120437879 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1 / 1 : ℝ) - (799 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (19920120437879 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (19920120437879 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((799 / 3200 : ℝ) - Real.pi * Real.exp (1 / 1 : ℝ)) := by
    rw [show (799 / 3200 : ℝ) - Real.pi * Real.exp (1 / 1 : ℝ) =
      -(Real.pi * Real.exp (1 / 1 : ℝ) - (799 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (799 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (799 / 800 : ℝ)) := by
    have h := hpThetaJensenCell799_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (19920120437879 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell799_endpointUpper :
    hpThetaJensenKernelEndpointUpper (799 / 1600 : ℝ) (1 / 2 : ℝ) ≤ (611858409 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1 / 1 : ℝ)) (42698675823784799 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1 / 2 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell799_product_upper
  have hD : (4925632641669 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (799 / 800 : ℝ) - (1 / 4 : ℝ)) := by
    apply le_trans hpThetaJensenCell799_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell799_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (799 / 800 : ℝ) - (1 / 4 : ℝ)) ≤
      (1 / (4925632641669 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4925632641669 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1 / 4 : ℝ) - Real.pi * Real.exp (799 / 800 : ℝ)) ≤
      (2 / (4925632641669 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1 / 4 : ℝ) - Real.pi * Real.exp (799 / 800 : ℝ) =
      -(Real.pi * Real.exp (799 / 800 : ℝ) - (1 / 4 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42698675823784799 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (42698675823784799 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell799_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (799 / 1600 : ℝ) (1 / 2 : ℝ)) :
    (300958741 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (611858409 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell799_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell799_endpointUpper

def hpThetaJensenCellsBatch039Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (277460677 / 2000000000 : ℝ)
  | 1 => (688576319 / 5000000000 : ℝ)
  | 2 => (341764439 / 2500000000 : ℝ)
  | 3 => (67850929 / 500000000 : ℝ)
  | 4 => (336758737 / 2500000000 : ℝ)
  | 5 => (1337106701 / 10000000000 : ℝ)
  | 6 => (53089347 / 400000000 : ℝ)
  | 7 => (1317415711 / 10000000000 : ℝ)
  | 8 => (1307652643 / 10000000000 : ℝ)
  | 9 => (1297944309 / 10000000000 : ℝ)
  | 10 => (257658109 / 2000000000 : ℝ)
  | 11 => (639345593 / 5000000000 : ℝ)
  | 12 => (1269146067 / 10000000000 : ℝ)
  | 13 => (629827511 / 5000000000 : ℝ)
  | 14 => (250043577 / 2000000000 : ℝ)
  | 15 => (1240834489 / 10000000000 : ℝ)
  | 16 => (307876167 / 2500000000 : ℝ)
  | 17 => (305557063 / 2500000000 : ℝ)
  | 18 => (606502537 / 5000000000 : ℝ)
  | 19 => (300958741 / 2500000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch039Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1409873181 / 10000000000 : ℝ)
  | 1 => (1399574949 / 10000000000 : ℝ)
  | 2 => (173666657 / 1250000000 : ℝ)
  | 3 => (689573971 / 5000000000 : ℝ)
  | 4 => (684509423 / 5000000000 : ℝ)
  | 5 => (339736451 / 2500000000 : ℝ)
  | 6 => (674464327 / 5000000000 : ℝ)
  | 7 => (1338967233 / 10000000000 : ℝ)
  | 8 => (664530689 / 5000000000 : ℝ)
  | 9 => (329802731 / 2500000000 : ℝ)
  | 10 => (261883141 / 2000000000 : ℝ)
  | 11 => (324918889 / 2500000000 : ℝ)
  | 12 => (1289990311 / 10000000000 : ℝ)
  | 13 => (640179901 / 5000000000 : ℝ)
  | 14 => (158847983 / 1250000000 : ℝ)
  | 15 => (1261262327 / 10000000000 : ℝ)
  | 16 => (1251795023 / 10000000000 : ℝ)
  | 17 => (1242381783 / 10000000000 : ℝ)
  | 18 => (616511219 / 5000000000 : ℝ)
  | 19 => (611858409 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch039_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch039Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch039Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell780_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell781_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell782_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell783_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell784_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell785_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell786_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell787_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell788_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell789_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell790_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell791_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell792_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell793_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell794_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell795_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell796_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell797_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell798_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell799_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper] at h ⊢
    exact h

end HodgeProofHP
