import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1400_leftExp :
    (28773013379 / 5000000000 : ℝ) ≤ Real.exp (7 / 4 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 4 : ℝ) (264052624329 / 250000000000 : ℝ)
    (28773013379 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1400_rightExp :
    Real.exp (1401 / 800 : ℝ) ≤ (3601125267 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1401 / 800 : ℝ) (528125878173 / 500000000000 : ℝ)
    (3601125267 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1400_denomUpper :
    Real.exp (11039832430930331 / 625000000000000 : ℝ) ≤ (29318470276815603 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11039832430930331 / 625000000000000 : ℝ) (173670844173 /
    100000000000 : ℝ) (29318470276815603 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1400_denomLower :
    (458461245901315877 / 10000000000 : ℝ) ≤ Real.exp (11025500768419921 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11025500768419921 / 625000000000000 : ℝ) (34709287831 /
    20000000000 : ℝ) (458461245901315877 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1400_product_lower :
    (11299133580919921 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 4 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1400_leftExp
    (by norm_num : (0 : ℝ) ≤ (28773013379 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1400_product_upper :
    Real.pi * Real.exp (1401 / 800 : ℝ) ≤ (11313269930930331 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1400_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1400_endpointLower :
    (255571 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 8 : ℝ) (1401 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11299133580919921 / 625000000000000 : ℝ) (Real.pi * Real.exp (7 / 4 : ℝ))
    (by norm_num) hpThetaJensenCell1400_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1401 / 800 : ℝ) - (7 / 16 : ℝ)) ≤
      (29318470276815603 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1400_denomUpper
    linarith [hpThetaJensenCell1400_product_upper]
  have hi : (1 / (29318470276815603 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1401 / 800 : ℝ) - (7 / 16 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29318470276815603 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29318470276815603 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 16 : ℝ) - Real.pi * Real.exp (1401 / 800 : ℝ)) := by
    rw [show (7 / 16 : ℝ) - Real.pi * Real.exp (1401 / 800 : ℝ) =
      -(Real.pi * Real.exp (1401 / 800 : ℝ) - (7 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 4 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 4 : ℝ)) := by
    have h := hpThetaJensenCell1400_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29318470276815603 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1400_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 8 : ℝ) (1401 / 1600 : ℝ) ≤ (525749 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1401 / 800 : ℝ)) (11313269930930331 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1401 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1400_product_upper
  have hD : (458461245901315877 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 4 : ℝ) - (1401 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1400_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1400_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 4 : ℝ) - (1401 / 3200 : ℝ)) ≤
      (1 / (458461245901315877 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (458461245901315877 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1401 / 3200 : ℝ) - Real.pi * Real.exp (7 / 4 : ℝ)) ≤
      (2 / (458461245901315877 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1401 / 3200 : ℝ) - Real.pi * Real.exp (7 / 4 : ℝ) =
      -(Real.pi * Real.exp (7 / 4 : ℝ) - (1401 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11313269930930331 / 625000000000000 : ℝ) ^ 2 - 6 *
      (11313269930930331 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1400_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 8 : ℝ) (1401 / 1600 : ℝ)) :
    (255571 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (525749 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1400_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1400_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1401_leftExp :
    (57618004269 / 10000000000 : ℝ) ≤ Real.exp (1401 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1401 / 800 : ℝ) (211250351269 / 200000000000 : ℝ)
    (57618004269 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1401_rightExp :
    Real.exp (701 / 400 : ℝ) ≤ (5769007181 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (701 / 400 : ℝ) (528146508493 / 500000000000 : ℝ)
    (5769007181 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1401_denomUpper :
    Real.exp (17686060076779333 / 1000000000000000 : ℝ) ≤ (479687385644226639 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (17686060076779333 / 1000000000000000 : ℝ) (868960331539
    / 500000000000 : ℝ) (479687385644226639 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1401_denomLower :
    (468799729719242441 / 10000000000 : ℝ) ≤ Real.exp (22078876408432031 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (22078876408432031 / 1250000000000000 : ℝ) (1736674209221
    / 1000000000000 : ℝ) (468799729719242441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1401_product_lower :
    (22626532658432031 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1401 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1401_leftExp
    (by norm_num : (0 : ℝ) ≤ (57618004269 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1401_product_upper :
    Real.pi * Real.exp (701 / 400 : ℝ) ≤ (18123872576779333 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1401_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1401_endpointLower :
    (501163 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1401 / 1600 : ℝ) (701 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22626532658432031 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1401 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1401_product_lower
  have hD : Real.exp (Real.pi * Real.exp (701 / 400 : ℝ) - (1401 / 3200 : ℝ)) ≤
      (479687385644226639 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1401_denomUpper
    linarith [hpThetaJensenCell1401_product_upper]
  have hi : (1 / (479687385644226639 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (701 / 400 : ℝ) - (1401 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (479687385644226639 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (479687385644226639 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1401 / 3200 : ℝ) - Real.pi * Real.exp (701 / 400 : ℝ)) := by
    rw [show (1401 / 3200 : ℝ) - Real.pi * Real.exp (701 / 400 : ℝ) =
      -(Real.pi * Real.exp (701 / 400 : ℝ) - (1401 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1401 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1401 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1401_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (479687385644226639 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1401_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1401 / 1600 : ℝ) (701 / 800 : ℝ) ≤ (1031 / 20000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (701 / 400 : ℝ)) (18123872576779333 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (701 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1401_product_upper
  have hD : (468799729719242441 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1401 / 800 : ℝ) - (701 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1401_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1401_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1401 / 800 : ℝ) - (701 / 1600 : ℝ)) ≤
      (1 / (468799729719242441 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (468799729719242441 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((701 / 1600 : ℝ) - Real.pi * Real.exp (1401 / 800 : ℝ)) ≤
      (2 / (468799729719242441 / 10000000000 : ℝ) : ℝ) := by
    rw [show (701 / 1600 : ℝ) - Real.pi * Real.exp (1401 / 800 : ℝ) =
      -(Real.pi * Real.exp (1401 / 800 : ℝ) - (701 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18123872576779333 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (18123872576779333 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1401_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1401 / 1600 : ℝ) (701 / 800 : ℝ)) :
    (501163 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1031 / 20000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1401_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1401_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1402_leftExp :
    (57690071807 / 10000000000 : ℝ) ≤ Real.exp (701 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (701 / 400 : ℝ) (211258603397 / 200000000000 : ℝ)
    (57690071807 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1402_rightExp :
    Real.exp (1403 / 800 : ℝ) ≤ (57762229489 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1403 / 800 : ℝ) (528167139619 / 500000000000 : ℝ)
    (57762229489 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1402_denomUpper :
    Real.exp (177084165827035977 / 10000000000000000 : ℝ) ≤ (490532294960118497 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (177084165827035977 / 10000000000000000 : ℝ)
    (347827053923 / 200000000000 : ℝ) (490532294960118497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1402_denomLower :
    (14980778394999191 / 312500000 : ℝ) ≤ Real.exp (22106786633537093 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22106786633537093 / 1250000000000000 : ℝ) (434471601571
    / 250000000000 : ℝ) (14980778394999191 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1402_product_lower :
    (22654833508537093 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (701 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1402_leftExp
    (by norm_num : (0 : ℝ) ≤ (57690071807 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1402_product_upper :
    Real.pi * Real.exp (1403 / 800 : ℝ) ≤ (181465415827035977 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1402_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1402_endpointLower :
    (245683 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (701 / 800 : ℝ) (1403 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22654833508537093 / 1250000000000000 : ℝ) (Real.pi * Real.exp (701 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1402_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1403 / 800 : ℝ) - (701 / 1600 : ℝ)) ≤
      (490532294960118497 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1402_denomUpper
    linarith [hpThetaJensenCell1402_product_upper]
  have hi : (1 / (490532294960118497 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1403 / 800 : ℝ) - (701 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (490532294960118497 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (490532294960118497 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((701 / 1600 : ℝ) - Real.pi * Real.exp (1403 / 800 : ℝ)) := by
    rw [show (701 / 1600 : ℝ) - Real.pi * Real.exp (1403 / 800 : ℝ) =
      -(Real.pi * Real.exp (1403 / 800 : ℝ) - (701 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (701 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (701 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1402_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (490532294960118497 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1402_endpointUpper :
    hpThetaJensenKernelEndpointUpper (701 / 800 : ℝ) (1403 / 1600 : ℝ) ≤ (126359 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1403 / 800 : ℝ)) (181465415827035977 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1403 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1402_product_upper
  have hD : (14980778394999191 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (701 / 400 : ℝ) - (1403 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1402_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1402_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (701 / 400 : ℝ) - (1403 / 3200 : ℝ)) ≤
      (1 / (14980778394999191 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (14980778394999191 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1403 / 3200 : ℝ) - Real.pi * Real.exp (701 / 400 : ℝ)) ≤
      (2 / (14980778394999191 / 312500000 : ℝ) : ℝ) := by
    rw [show (1403 / 3200 : ℝ) - Real.pi * Real.exp (701 / 400 : ℝ) =
      -(Real.pi * Real.exp (701 / 400 : ℝ) - (1403 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (181465415827035977 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (181465415827035977 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1402_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (701 / 800 : ℝ) (1403 / 1600 : ℝ)) :
    (245683 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (126359 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1402_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1402_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1403_leftExp :
    (28881114743 / 5000000000 : ℝ) ≤ Real.exp (1403 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1403 / 800 : ℝ) (1056334279237 / 1000000000000 : ℝ)
    (28881114743 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1403_rightExp :
    Real.exp (351 / 200 : ℝ) ≤ (28917238711 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (351 / 200 : ℝ) (528187771551 / 500000000000 : ℝ)
    (28917238711 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1403_denomUpper :
    Real.exp (88654007213806623 / 5000000000000000 : ℝ) ≤ (501636612363246611 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (88654007213806623 / 5000000000000000 : ℝ) (1740352267091
    / 1000000000000 : ℝ) (501636612363246611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1403_denomLower :
    (245111487964744077 / 5000000000 : ℝ) ≤ Real.exp (11067366128461357 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11067366128461357 / 625000000000000 : ℝ) (1739100988487
    / 1000000000000 : ℝ) (245111487964744077 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1403_product_lower :
    (11341584878461357 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1403 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1403_leftExp
    (by norm_num : (0 : ℝ) ≤ (28881114743 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1403_product_upper :
    Real.pi * Real.exp (351 / 200 : ℝ) ≤ (90846194713806623 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1403_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1403_endpointLower :
    (240873 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1403 / 1600 : ℝ) (351 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11341584878461357 / 625000000000000 : ℝ) (Real.pi * Real.exp (1403 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1403_product_lower
  have hD : Real.exp (Real.pi * Real.exp (351 / 200 : ℝ) - (1403 / 3200 : ℝ)) ≤
      (501636612363246611 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1403_denomUpper
    linarith [hpThetaJensenCell1403_product_upper]
  have hi : (1 / (501636612363246611 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (351 / 200 : ℝ) - (1403 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (501636612363246611 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (501636612363246611 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1403 / 3200 : ℝ) - Real.pi * Real.exp (351 / 200 : ℝ)) := by
    rw [show (1403 / 3200 : ℝ) - Real.pi * Real.exp (351 / 200 : ℝ) =
      -(Real.pi * Real.exp (351 / 200 : ℝ) - (1403 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1403 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1403 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1403_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (501636612363246611 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1403_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1403 / 1600 : ℝ) (351 / 400 : ℝ) ≤ (99111 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (351 / 200 : ℝ)) (90846194713806623 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (351 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1403_product_upper
  have hD : (245111487964744077 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1403 / 800 : ℝ) - (351 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1403_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1403_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1403 / 800 : ℝ) - (351 / 800 : ℝ)) ≤
      (1 / (245111487964744077 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (245111487964744077 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((351 / 800 : ℝ) - Real.pi * Real.exp (1403 / 800 : ℝ)) ≤
      (2 / (245111487964744077 / 5000000000 : ℝ) : ℝ) := by
    rw [show (351 / 800 : ℝ) - Real.pi * Real.exp (1403 / 800 : ℝ) =
      -(Real.pi * Real.exp (1403 / 800 : ℝ) - (351 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (90846194713806623 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (90846194713806623 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1403_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1403 / 1600 : ℝ) (351 / 400 : ℝ)) :
    (240873 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (99111 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1403_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1403_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1404_leftExp :
    (57834477419 / 10000000000 : ℝ) ≤ Real.exp (351 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (351 / 200 : ℝ) (1056375543101 / 1000000000000 : ℝ)
    (57834477419 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1404_rightExp :
    Real.exp (281 / 160 : ℝ) ≤ (1447670393 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (281 / 160 : ℝ) (1056416808577 / 1000000000000 : ℝ)
    (1447670393 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1404_denomUpper :
    Real.exp (4438303672956049 / 250000000000000 : ℝ) ≤ (513006864857670059 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (4438303672956049 / 250000000000000 : ℝ) (108848228827 /
    62500000000 : ℝ) (513006864857670059 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1404_denomLower :
    (501320287567756421 / 10000000000 : ℝ) ≤ Real.exp (22162713322963881 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (22162713322963881 / 1250000000000000 : ℝ) (1740317961581
    / 1000000000000 : ℝ) (501320287567756421 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1404_product_lower :
    (22711541447963881 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (351 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1404_leftExp
    (by norm_num : (0 : ℝ) ≤ (57834477419 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1404_product_upper :
    Real.pi * Real.exp (281 / 160 : ℝ) ≤ (4547991172956049 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1404_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1404_endpointLower :
    (472301 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (351 / 400 : ℝ) (281 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22711541447963881 / 1250000000000000 : ℝ) (Real.pi * Real.exp (351 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1404_product_lower
  have hD : Real.exp (Real.pi * Real.exp (281 / 160 : ℝ) - (351 / 800 : ℝ)) ≤
      (513006864857670059 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1404_denomUpper
    linarith [hpThetaJensenCell1404_product_upper]
  have hi : (1 / (513006864857670059 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (281 / 160 : ℝ) - (351 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (513006864857670059 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (513006864857670059 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((351 / 800 : ℝ) - Real.pi * Real.exp (281 / 160 : ℝ)) := by
    rw [show (351 / 800 : ℝ) - Real.pi * Real.exp (281 / 160 : ℝ) =
      -(Real.pi * Real.exp (281 / 160 : ℝ) - (351 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (351 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (351 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1404_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (513006864857670059 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1404_endpointUpper :
    hpThetaJensenKernelEndpointUpper (351 / 400 : ℝ) (281 / 320 : ℝ) ≤ (121463 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (281 / 160 : ℝ)) (4547991172956049 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (281 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1404_product_upper
  have hD : (501320287567756421 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (351 / 200 : ℝ) - (281 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1404_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1404_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (351 / 200 : ℝ) - (281 / 640 : ℝ)) ≤
      (1 / (501320287567756421 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (501320287567756421 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((281 / 640 : ℝ) - Real.pi * Real.exp (351 / 200 : ℝ)) ≤
      (2 / (501320287567756421 / 10000000000 : ℝ) : ℝ) := by
    rw [show (281 / 640 : ℝ) - Real.pi * Real.exp (351 / 200 : ℝ) =
      -(Real.pi * Real.exp (351 / 200 : ℝ) - (281 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4547991172956049 / 250000000000000 : ℝ) ^ 2 - 6 *
      (4547991172956049 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1404_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (351 / 400 : ℝ) (281 / 320 : ℝ)) :
    (472301 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (121463 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1404_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1404_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1405_leftExp :
    (57906815717 / 10000000000 : ℝ) ≤ Real.exp (281 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (281 / 160 : ℝ) (8253256317 / 7812500000 : ℝ)
    (57906815717 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1405_rightExp :
    Real.exp (703 / 400 : ℝ) ≤ (28989622249 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (703 / 400 : ℝ) (211291615133 / 200000000000 : ℝ)
    (28989622249 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1405_denomUpper :
    Real.exp (88878281830102657 / 5000000000000000 : ℝ) ≤ (65581219009904311 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (88878281830102657 / 5000000000000000 : ℝ) (34855869157 /
    20000000000 : ℝ) (65581219009904311 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1405_denomLower :
    (12817084160955587 / 250000000 : ℝ) ≤ Real.exp (22190729875250183 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22190729875250183 / 1250000000000000 : ℝ) (435384332823
    / 250000000000 : ℝ) (12817084160955587 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1405_product_lower :
    (22739948625250183 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (281 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1405_leftExp
    (by norm_num : (0 : ℝ) ≤ (57906815717 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1405_product_upper :
    Real.pi * Real.exp (703 / 400 : ℝ) ≤ (91073594330102657 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1405_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1405_endpointLower :
    (115757 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (281 / 320 : ℝ) (703 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22739948625250183 / 1250000000000000 : ℝ) (Real.pi * Real.exp (281 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1405_product_lower
  have hD : Real.exp (Real.pi * Real.exp (703 / 400 : ℝ) - (281 / 640 : ℝ)) ≤
      (65581219009904311 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1405_denomUpper
    linarith [hpThetaJensenCell1405_product_upper]
  have hi : (1 / (65581219009904311 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (703 / 400 : ℝ) - (281 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65581219009904311 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65581219009904311 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((281 / 640 : ℝ) - Real.pi * Real.exp (703 / 400 : ℝ)) := by
    rw [show (281 / 640 : ℝ) - Real.pi * Real.exp (703 / 400 : ℝ) =
      -(Real.pi * Real.exp (703 / 400 : ℝ) - (281 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (281 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (281 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1405_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65581219009904311 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1405_endpointUpper :
    hpThetaJensenKernelEndpointUpper (281 / 320 : ℝ) (703 / 800 : ℝ) ≤ (476327 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (703 / 400 : ℝ)) (91073594330102657 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (703 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1405_product_upper
  have hD : (12817084160955587 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (281 / 160 : ℝ) - (703 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1405_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1405_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (281 / 160 : ℝ) - (703 / 1600 : ℝ)) ≤
      (1 / (12817084160955587 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12817084160955587 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((703 / 1600 : ℝ) - Real.pi * Real.exp (281 / 160 : ℝ)) ≤
      (2 / (12817084160955587 / 250000000 : ℝ) : ℝ) := by
    rw [show (703 / 1600 : ℝ) - Real.pi * Real.exp (281 / 160 : ℝ) =
      -(Real.pi * Real.exp (281 / 160 : ℝ) - (703 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (91073594330102657 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (91073594330102657 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1405_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (281 / 320 : ℝ) (703 / 800 : ℝ)) :
    (115757 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (476327 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1405_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1405_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1406_leftExp :
    (3623702781 / 625000000 : ℝ) ≤ Real.exp (703 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (703 / 400 : ℝ) (66028629729 / 62500000000 : ℝ)
    (3623702781 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1406_rightExp :
    Real.exp (1407 / 800 : ℝ) ≤ (14512940967 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1407 / 800 : ℝ) (264124836091 / 250000000000 : ℝ)
    (14512940967 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1406_denomUpper :
    Real.exp (44495316251340431 / 2500000000000000 : ℝ) ≤ (536572149884097347 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (44495316251340431 / 2500000000000000 : ℝ) (1362513799 /
    781250000 : ℝ) (536572149884097347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1406_denomLower :
    (26215945405541901 / 500000000 : ℝ) ≤ Real.exp (1388673872458419 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1388673872458419 / 78125000000000 : ℝ) (1742759103449 /
    1000000000000 : ℝ) (26215945405541901 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1406_product_lower :
    (1423024458395919 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (703 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1406_leftExp
    (by norm_num : (0 : ℝ) ≤ (3623702781 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1406_product_upper :
    Real.pi * Real.exp (1407 / 800 : ℝ) ≤ (45593753751340431 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1406_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1406_endpointLower :
    (453923 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (703 / 800 : ℝ) (1407 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1423024458395919 / 78125000000000 : ℝ) (Real.pi * Real.exp (703 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1406_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1407 / 800 : ℝ) - (703 / 1600 : ℝ)) ≤
      (536572149884097347 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1406_denomUpper
    linarith [hpThetaJensenCell1406_product_upper]
  have hi : (1 / (536572149884097347 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1407 / 800 : ℝ) - (703 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (536572149884097347 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (536572149884097347 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((703 / 1600 : ℝ) - Real.pi * Real.exp (1407 / 800 : ℝ)) := by
    rw [show (703 / 1600 : ℝ) - Real.pi * Real.exp (1407 / 800 : ℝ) =
      -(Real.pi * Real.exp (1407 / 800 : ℝ) - (703 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (703 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (703 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1406_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (536572149884097347 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1406_endpointUpper :
    hpThetaJensenKernelEndpointUpper (703 / 800 : ℝ) (1407 / 1600 : ℝ) ≤ (233487 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1407 / 800 : ℝ)) (45593753751340431 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1407 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1406_product_upper
  have hD : (26215945405541901 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (703 / 400 : ℝ) - (1407 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1406_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1406_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (703 / 400 : ℝ) - (1407 / 3200 : ℝ)) ≤
      (1 / (26215945405541901 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26215945405541901 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1407 / 3200 : ℝ) - Real.pi * Real.exp (703 / 400 : ℝ)) ≤
      (2 / (26215945405541901 / 500000000 : ℝ) : ℝ) := by
    rw [show (1407 / 3200 : ℝ) - Real.pi * Real.exp (703 / 400 : ℝ) =
      -(Real.pi * Real.exp (703 / 400 : ℝ) - (1407 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45593753751340431 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (45593753751340431 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1406_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (703 / 800 : ℝ) (1407 / 1600 : ℝ)) :
    (453923 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (233487 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1406_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1406_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1407_leftExp :
    (11610352773 / 2000000000 : ℝ) ≤ Real.exp (1407 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1407 / 800 : ℝ) (1056499344363 / 1000000000000 : ℝ)
    (11610352773 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1407_rightExp :
    Real.exp (44 / 25 : ℝ) ≤ (11624874789 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44 / 25 : ℝ) (264135153669 / 250000000000 : ℝ)
    (11624874789 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1407_denomUpper :
    Real.exp (35641250262998877 / 2000000000000000 : ℝ) ≤ (2143676235122609 / 39062500 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35641250262998877 / 2000000000000000 : ℝ) (1745244281683
    / 1000000000000 : ℝ) (2143676235122609 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1407_denomLower :
    (268116891795143083 / 5000000000 : ℝ) ≤ Real.exp (4449373923604327 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4449373923604327 / 250000000000000 : ℝ) (871991641887 /
    500000000000 : ℝ) (268116891795143083 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1407_product_lower :
    (4559373923604327 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1407 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1407_leftExp
    (by norm_num : (0 : ℝ) ≤ (11610352773 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1407_product_upper :
    Real.pi * Real.exp (44 / 25 : ℝ) ≤ (36520625262998877 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1407_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1407_endpointLower :
    (222493 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1407 / 1600 : ℝ) (22 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4559373923604327 / 250000000000000 : ℝ) (Real.pi * Real.exp (1407 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1407_product_lower
  have hD : Real.exp (Real.pi * Real.exp (44 / 25 : ℝ) - (1407 / 3200 : ℝ)) ≤
      (2143676235122609 / 39062500 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1407_denomUpper
    linarith [hpThetaJensenCell1407_product_upper]
  have hi : (1 / (2143676235122609 / 39062500 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (44 / 25 : ℝ) - (1407 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2143676235122609 / 39062500 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2143676235122609 / 39062500 : ℝ) : ℝ) ≤
      2 * Real.exp ((1407 / 3200 : ℝ) - Real.pi * Real.exp (44 / 25 : ℝ)) := by
    rw [show (1407 / 3200 : ℝ) - Real.pi * Real.exp (44 / 25 : ℝ) =
      -(Real.pi * Real.exp (44 / 25 : ℝ) - (1407 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1407 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1407 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1407_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2143676235122609 / 39062500 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1407_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1407 / 1600 : ℝ) (22 / 25 : ℝ) ≤ (457793 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (44 / 25 : ℝ)) (36520625262998877 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (22 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1407_product_upper
  have hD : (268116891795143083 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1407 / 800 : ℝ) - (11 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell1407_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1407_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1407 / 800 : ℝ) - (11 / 25 : ℝ)) ≤
      (1 / (268116891795143083 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (268116891795143083 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 25 : ℝ) - Real.pi * Real.exp (1407 / 800 : ℝ)) ≤
      (2 / (268116891795143083 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 25 : ℝ) - Real.pi * Real.exp (1407 / 800 : ℝ) =
      -(Real.pi * Real.exp (1407 / 800 : ℝ) - (11 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36520625262998877 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (36520625262998877 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1407_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1407 / 1600 : ℝ) (22 / 25 : ℝ)) :
    (222493 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (457793 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1407_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1407_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1408_leftExp :
    (58124373943 / 10000000000 : ℝ) ≤ Real.exp (44 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (44 / 25 : ℝ) (42261624587 / 40000000000 : ℝ)
    (58124373943 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1408_rightExp :
    Real.exp (1409 / 800 : ℝ) ≤ (29098537421 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1409 / 800 : ℝ) (5282909433 / 5000000000 : ℝ)
    (29098537421 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1408_denomUpper :
    Real.exp (89215761472051653 / 5000000000000000 : ℝ) ≤ (280641947566955743 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (89215761472051653 / 5000000000000000 : ℝ) (873236660279
    / 500000000000 : ℝ) (280641947566955743 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1408_denomLower :
    (274217523510380811 / 5000000000 : ℝ) ≤ Real.exp (22274992898042157 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22274992898042157 / 1250000000000000 : ℝ) (872604939089
    / 500000000000 : ℝ) (274217523510380811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1408_product_lower :
    (22825383523042157 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (44 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1408_leftExp
    (by norm_num : (0 : ℝ) ≤ (58124373943 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1408_product_upper :
    Real.pi * Real.exp (1409 / 800 : ℝ) ≤ (91415761472051653 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1408_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1408_endpointLower :
    (436211 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (22 / 25 : ℝ) (1409 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22825383523042157 / 1250000000000000 : ℝ) (Real.pi * Real.exp (44 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1408_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1409 / 800 : ℝ) - (11 / 25 : ℝ)) ≤
      (280641947566955743 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1408_denomUpper
    linarith [hpThetaJensenCell1408_product_upper]
  have hi : (1 / (280641947566955743 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1409 / 800 : ℝ) - (11 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (280641947566955743 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (280641947566955743 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 25 : ℝ) - Real.pi * Real.exp (1409 / 800 : ℝ)) := by
    rw [show (11 / 25 : ℝ) - Real.pi * Real.exp (1409 / 800 : ℝ) =
      -(Real.pi * Real.exp (1409 / 800 : ℝ) - (11 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (44 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (44 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1408_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (280641947566955743 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1408_endpointUpper :
    hpThetaJensenKernelEndpointUpper (22 / 25 : ℝ) (1409 / 1600 : ℝ) ≤ (448779 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1409 / 800 : ℝ)) (91415761472051653 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1409 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1408_product_upper
  have hD : (274217523510380811 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (44 / 25 : ℝ) - (1409 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1408_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1408_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (44 / 25 : ℝ) - (1409 / 3200 : ℝ)) ≤
      (1 / (274217523510380811 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (274217523510380811 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1409 / 3200 : ℝ) - Real.pi * Real.exp (44 / 25 : ℝ)) ≤
      (2 / (274217523510380811 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1409 / 3200 : ℝ) - Real.pi * Real.exp (44 / 25 : ℝ) =
      -(Real.pi * Real.exp (44 / 25 : ℝ) - (1409 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (91415761472051653 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (91415761472051653 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1408_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (22 / 25 : ℝ) (1409 / 1600 : ℝ)) :
    (436211 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (448779 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1408_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1408_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1409_leftExp :
    (58197074839 / 10000000000 : ℝ) ≤ Real.exp (1409 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1409 / 800 : ℝ) (1056581886599 / 1000000000000 : ℝ)
    (58197074839 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1409_rightExp :
    Real.exp (141 / 80 : ℝ) ≤ (58269866671 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (141 / 80 : ℝ) (132077895017 / 125000000000 : ℝ)
    (58269866671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1409_denomUpper :
    Real.exp (178657080244546903 / 10000000000000000 : ℝ) ≤ (143521980598048027 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (178657080244546903 / 10000000000000000 : ℝ)
    (436926196291 / 250000000000 : ℝ) (143521980598048027 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1409_denomLower :
    (280464968642642321 / 5000000000 : ℝ) ≤ Real.exp (22303151842200461 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22303151842200461 / 1250000000000000 : ℝ) (436609723103
    / 250000000000 : ℝ) (280464968642642321 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1409_product_lower :
    (22853933092200461 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1409 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1409_leftExp
    (by norm_num : (0 : ℝ) ≤ (58197074839 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1409_product_upper :
    Real.pi * Real.exp (141 / 80 : ℝ) ≤ (183060205244546903 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1409_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1409_endpointLower :
    (213799 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1409 / 1600 : ℝ) (141 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22853933092200461 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1409 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1409_product_lower
  have hD : Real.exp (Real.pi * Real.exp (141 / 80 : ℝ) - (1409 / 3200 : ℝ)) ≤
      (143521980598048027 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1409_denomUpper
    linarith [hpThetaJensenCell1409_product_upper]
  have hi : (1 / (143521980598048027 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (141 / 80 : ℝ) - (1409 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (143521980598048027 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (143521980598048027 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1409 / 3200 : ℝ) - Real.pi * Real.exp (141 / 80 : ℝ)) := by
    rw [show (1409 / 3200 : ℝ) - Real.pi * Real.exp (141 / 80 : ℝ) =
      -(Real.pi * Real.exp (141 / 80 : ℝ) - (1409 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1409 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1409 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1409_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (143521980598048027 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1409_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1409 / 1600 : ℝ) (141 / 160 : ℝ) ≤ (439929 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (141 / 80 : ℝ)) (183060205244546903 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (141 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1409_product_upper
  have hD : (280464968642642321 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1409 / 800 : ℝ) - (141 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1409_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1409_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1409 / 800 : ℝ) - (141 / 320 : ℝ)) ≤
      (1 / (280464968642642321 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (280464968642642321 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((141 / 320 : ℝ) - Real.pi * Real.exp (1409 / 800 : ℝ)) ≤
      (2 / (280464968642642321 / 5000000000 : ℝ) : ℝ) := by
    rw [show (141 / 320 : ℝ) - Real.pi * Real.exp (1409 / 800 : ℝ) =
      -(Real.pi * Real.exp (1409 / 800 : ℝ) - (141 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (183060205244546903 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (183060205244546903 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1409_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1409 / 1600 : ℝ) (141 / 160 : ℝ)) :
    (213799 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (439929 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1409_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1409_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1410_leftExp :
    (14567466667 / 2500000000 : ℝ) ≤ Real.exp (141 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (141 / 80 : ℝ) (211324632027 / 200000000000 : ℝ)
    (14567466667 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1410_rightExp :
    Real.exp (1411 / 800 : ℝ) ≤ (29171374773 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1411 / 800 : ℝ) (264166108821 / 250000000000 : ℝ)
    (29171374773 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1410_denomUpper :
    Real.exp (89441461787233389 / 5000000000000000 : ℝ) ≤ (36700051937111711 / 625000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (89441461787233389 / 5000000000000000 : ℝ) (1748938681369
    / 1000000000000 : ℝ) (36700051937111711 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1410_denomLower :
    (573725885872576167 / 10000000000 : ℝ) ≤ Real.exp (5582836623914233 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5582836623914233 / 312500000000000 : ℝ) (349534066469 /
    200000000000 : ℝ) (573725885872576167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1410_product_lower :
    (5720629592664233 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (141 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1410_leftExp
    (by norm_num : (0 : ℝ) ≤ (14567466667 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1410_product_upper :
    Real.pi * Real.exp (1411 / 800 : ℝ) ≤ (91644586787233389 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1410_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1410_endpointLower :
    (209571 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (141 / 160 : ℝ) (1411 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5720629592664233 / 312500000000000 : ℝ) (Real.pi * Real.exp (141 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1410_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1411 / 800 : ℝ) - (141 / 320 : ℝ)) ≤
      (36700051937111711 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1410_denomUpper
    linarith [hpThetaJensenCell1410_product_upper]
  have hi : (1 / (36700051937111711 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1411 / 800 : ℝ) - (141 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (36700051937111711 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (36700051937111711 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((141 / 320 : ℝ) - Real.pi * Real.exp (1411 / 800 : ℝ)) := by
    rw [show (141 / 320 : ℝ) - Real.pi * Real.exp (1411 / 800 : ℝ) =
      -(Real.pi * Real.exp (1411 / 800 : ℝ) - (141 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (141 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (141 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1410_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (36700051937111711 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1410_endpointUpper :
    hpThetaJensenKernelEndpointUpper (141 / 160 : ℝ) (1411 / 1600 : ℝ) ≤ (215621 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1411 / 800 : ℝ)) (91644586787233389 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1411 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1410_product_upper
  have hD : (573725885872576167 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (141 / 80 : ℝ) - (1411 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1410_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1410_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (141 / 80 : ℝ) - (1411 / 3200 : ℝ)) ≤
      (1 / (573725885872576167 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (573725885872576167 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1411 / 3200 : ℝ) - Real.pi * Real.exp (141 / 80 : ℝ)) ≤
      (2 / (573725885872576167 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1411 / 3200 : ℝ) - Real.pi * Real.exp (141 / 80 : ℝ) =
      -(Real.pi * Real.exp (141 / 80 : ℝ) - (1411 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (91644586787233389 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (91644586787233389 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1410_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (141 / 160 : ℝ) (1411 / 1600 : ℝ)) :
    (209571 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (215621 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1410_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1410_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1411_leftExp :
    (58342749543 / 10000000000 : ℝ) ≤ Real.exp (1411 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1411 / 800 : ℝ) (1056664435283 / 1000000000000 : ℝ)
    (58342749543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1411_rightExp :
    Real.exp (353 / 200 : ℝ) ≤ (29207861791 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (353 / 200 : ℝ) (211341142409 / 200000000000 : ℝ)
    (29207861791 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1411_denomUpper :
    Real.exp (89554526647573063 / 5000000000000000 : ℝ) ≤ (300315228298640637 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (89554526647573063 / 5000000000000000 : ℝ) (54692969221 /
    31250000000 : ℝ) (300315228298640637 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1411_denomLower :
    (586830520819843759 / 10000000000 : ℝ) ≤ Real.exp (22359576902786557 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (22359576902786557 / 1250000000000000 : ℝ) (437226050957
    / 250000000000 : ℝ) (586830520819843759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1411_product_lower :
    (22911139402786557 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1411 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1411_leftExp
    (by norm_num : (0 : ℝ) ≤ (58342749543 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1411_product_upper :
    Real.pi * Real.exp (353 / 200 : ℝ) ≤ (91759214147573063 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1411_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1411_endpointLower :
    (205421 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1411 / 1600 : ℝ) (353 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22911139402786557 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1411 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1411_product_lower
  have hD : Real.exp (Real.pi * Real.exp (353 / 200 : ℝ) - (1411 / 3200 : ℝ)) ≤
      (300315228298640637 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1411_denomUpper
    linarith [hpThetaJensenCell1411_product_upper]
  have hi : (1 / (300315228298640637 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (353 / 200 : ℝ) - (1411 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (300315228298640637 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (300315228298640637 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1411 / 3200 : ℝ) - Real.pi * Real.exp (353 / 200 : ℝ)) := by
    rw [show (1411 / 3200 : ℝ) - Real.pi * Real.exp (353 / 200 : ℝ) =
      -(Real.pi * Real.exp (353 / 200 : ℝ) - (1411 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1411 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1411 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1411_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (300315228298640637 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1411_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1411 / 1600 : ℝ) (353 / 400 : ℝ) ≤ (211357 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (353 / 200 : ℝ)) (91759214147573063 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (353 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1411_product_upper
  have hD : (586830520819843759 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1411 / 800 : ℝ) - (353 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1411_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1411_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1411 / 800 : ℝ) - (353 / 800 : ℝ)) ≤
      (1 / (586830520819843759 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (586830520819843759 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((353 / 800 : ℝ) - Real.pi * Real.exp (1411 / 800 : ℝ)) ≤
      (2 / (586830520819843759 / 10000000000 : ℝ) : ℝ) := by
    rw [show (353 / 800 : ℝ) - Real.pi * Real.exp (1411 / 800 : ℝ) =
      -(Real.pi * Real.exp (1411 / 800 : ℝ) - (353 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (91759214147573063 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (91759214147573063 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1411_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1411 / 1600 : ℝ) (353 / 400 : ℝ)) :
    (205421 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (211357 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1411_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1411_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1412_leftExp :
    (2920786179 / 500000000 : ℝ) ≤ Real.exp (353 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (353 / 200 : ℝ) (264176428011 / 250000000000 : ℝ)
    (2920786179 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1412_rightExp :
    Real.exp (1413 / 800 : ℝ) ≤ (58488788893 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1413 / 800 : ℝ) (528373495209 / 500000000000 : ℝ)
    (58488788893 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1412_denomUpper :
    Real.exp (179335469764726549 / 10000000000000000 : ℝ) ≤ (307192421370319491 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (179335469764726549 / 10000000000000000 : ℝ)
    (175141379217 / 100000000000 : ℝ) (307192421370319491 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1412_denomLower :
    (300125836506982571 / 5000000000 : ℝ) ≤ Real.exp (1119392155457121 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1119392155457121 / 62500000000000 : ℝ) (218767564097 /
    125000000000 : ℝ) (300125836506982571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1412_product_lower :
    (1146989811707121 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (353 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1412_leftExp
    (by norm_num : (0 : ℝ) ≤ (2920786179 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1412_product_upper :
    Real.pi * Real.exp (1413 / 800 : ℝ) ≤ (183747969764726549 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1412_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1412_endpointLower :
    (80539 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (353 / 400 : ℝ) (1413 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1146989811707121 / 62500000000000 : ℝ) (Real.pi * Real.exp (353 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1412_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1413 / 800 : ℝ) - (353 / 800 : ℝ)) ≤
      (307192421370319491 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1412_denomUpper
    linarith [hpThetaJensenCell1412_product_upper]
  have hi : (1 / (307192421370319491 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1413 / 800 : ℝ) - (353 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (307192421370319491 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (307192421370319491 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((353 / 800 : ℝ) - Real.pi * Real.exp (1413 / 800 : ℝ)) := by
    rw [show (353 / 800 : ℝ) - Real.pi * Real.exp (1413 / 800 : ℝ) =
      -(Real.pi * Real.exp (1413 / 800 : ℝ) - (353 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (353 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (353 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1412_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (307192421370319491 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1412_endpointUpper :
    hpThetaJensenKernelEndpointUpper (353 / 400 : ℝ) (1413 / 1600 : ℝ) ≤ (414343 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1413 / 800 : ℝ)) (183747969764726549 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1413 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1412_product_upper
  have hD : (300125836506982571 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (353 / 200 : ℝ) - (1413 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1412_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1412_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (353 / 200 : ℝ) - (1413 / 3200 : ℝ)) ≤
      (1 / (300125836506982571 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (300125836506982571 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1413 / 3200 : ℝ) - Real.pi * Real.exp (353 / 200 : ℝ)) ≤
      (2 / (300125836506982571 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1413 / 3200 : ℝ) - Real.pi * Real.exp (353 / 200 : ℝ) =
      -(Real.pi * Real.exp (353 / 200 : ℝ) - (1413 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (183747969764726549 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (183747969764726549 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1412_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (353 / 400 : ℝ) (1413 / 1600 : ℝ)) :
    (80539 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (414343 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1412_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1412_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1413_leftExp :
    (5848878889 / 1000000000 : ℝ) ≤ Real.exp (1413 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1413 / 800 : ℝ) (1056746990417 / 1000000000000 : ℝ)
    (5848878889 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1413_rightExp :
    Real.exp (707 / 400 : ℝ) ≤ (58561945593 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (707 / 400 : ℝ) (264197067601 / 250000000000 : ℝ)
    (58561945593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1413_denomUpper :
    Real.exp (179562173341349649 / 10000000000000000 : ℝ) ≤ (78559030847031543 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (179562173341349649 / 10000000000000000 : ℝ) (70106200743
    / 40000000000 : ℝ) (78559030847031543 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1413_denomLower :
    (30699869018256151 / 500000000 : ℝ) ≤ Real.exp (2241614515831411 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2241614515831411 / 125000000000000 : ℝ) (437844816259 /
    250000000000 : ℝ) (30699869018256151 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1413_product_lower :
    (2296848890831411 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1413 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1413_leftExp
    (by norm_num : (0 : ℝ) ≤ (5848878889 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1413_product_upper :
    Real.pi * Real.exp (707 / 400 : ℝ) ≤ (183977798341349649 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1413_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1413_endpointLower :
    (394697 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1413 / 1600 : ℝ) (707 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2296848890831411 / 125000000000000 : ℝ) (Real.pi * Real.exp (1413 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1413_product_lower
  have hD : Real.exp (Real.pi * Real.exp (707 / 400 : ℝ) - (1413 / 3200 : ℝ)) ≤
      (78559030847031543 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1413_denomUpper
    linarith [hpThetaJensenCell1413_product_upper]
  have hi : (1 / (78559030847031543 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (707 / 400 : ℝ) - (1413 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (78559030847031543 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (78559030847031543 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1413 / 3200 : ℝ) - Real.pi * Real.exp (707 / 400 : ℝ)) := by
    rw [show (1413 / 3200 : ℝ) - Real.pi * Real.exp (707 / 400 : ℝ) =
      -(Real.pi * Real.exp (707 / 400 : ℝ) - (1413 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1413 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1413 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1413_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (78559030847031543 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1413_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1413 / 1600 : ℝ) (707 / 800 : ℝ) ≤ (203063 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (707 / 400 : ℝ)) (183977798341349649 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (707 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1413_product_upper
  have hD : (30699869018256151 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1413 / 800 : ℝ) - (707 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1413_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1413_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1413 / 800 : ℝ) - (707 / 1600 : ℝ)) ≤
      (1 / (30699869018256151 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (30699869018256151 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((707 / 1600 : ℝ) - Real.pi * Real.exp (1413 / 800 : ℝ)) ≤
      (2 / (30699869018256151 / 500000000 : ℝ) : ℝ) := by
    rw [show (707 / 1600 : ℝ) - Real.pi * Real.exp (1413 / 800 : ℝ) =
      -(Real.pi * Real.exp (1413 / 800 : ℝ) - (707 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (183977798341349649 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (183977798341349649 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1413_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1413 / 1600 : ℝ) (707 / 800 : ℝ)) :
    (394697 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (203063 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1413_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1413_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1414_leftExp :
    (58561945591 / 10000000000 : ℝ) ≤ Real.exp (707 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (707 / 400 : ℝ) (1056788270403 / 1000000000000 : ℝ)
    (58561945591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1414_rightExp :
    Real.exp (283 / 160 : ℝ) ≤ (14658798449 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (283 / 160 : ℝ) (528414776001 / 500000000000 : ℝ)
    (14658798449 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1414_denomUpper :
    Real.exp (44947291095789257 / 2500000000000000 : ℝ) ≤ (40181321611572111 / 625000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (44947291095789257 / 2500000000000000 : ℝ) (1753898700213
    / 1000000000000 : ℝ) (40181321611572111 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1414_denomLower :
    (314037947883433089 / 5000000000 : ℝ) ≤ Real.exp (22444483096640109 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22444483096640109 / 1250000000000000 : ℝ) (438155116647
    / 250000000000 : ℝ) (314037947883433089 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1414_product_lower :
    (22997217471640109 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (707 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1414_leftExp
    (by norm_num : (0 : ℝ) ≤ (58561945591 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1414_product_upper :
    Real.pi * Real.exp (283 / 160 : ℝ) ≤ (46051978595789257 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1414_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1414_endpointLower :
    (12089 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (707 / 800 : ℝ) (283 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (22997217471640109 / 1250000000000000 : ℝ) (Real.pi * Real.exp (707 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1414_product_lower
  have hD : Real.exp (Real.pi * Real.exp (283 / 160 : ℝ) - (707 / 1600 : ℝ)) ≤
      (40181321611572111 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1414_denomUpper
    linarith [hpThetaJensenCell1414_product_upper]
  have hi : (1 / (40181321611572111 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (283 / 160 : ℝ) - (707 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (40181321611572111 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (40181321611572111 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((707 / 1600 : ℝ) - Real.pi * Real.exp (283 / 160 : ℝ)) := by
    rw [show (707 / 1600 : ℝ) - Real.pi * Real.exp (283 / 160 : ℝ) =
      -(Real.pi * Real.exp (283 / 160 : ℝ) - (707 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (707 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (707 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1414_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (40181321611572111 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1414_endpointUpper :
    hpThetaJensenKernelEndpointUpper (707 / 800 : ℝ) (283 / 320 : ℝ) ≤ (398061 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (283 / 160 : ℝ)) (46051978595789257 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (283 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1414_product_upper
  have hD : (314037947883433089 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (707 / 400 : ℝ) - (283 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1414_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1414_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (707 / 400 : ℝ) - (283 / 640 : ℝ)) ≤
      (1 / (314037947883433089 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (314037947883433089 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((283 / 640 : ℝ) - Real.pi * Real.exp (707 / 400 : ℝ)) ≤
      (2 / (314037947883433089 / 5000000000 : ℝ) : ℝ) := by
    rw [show (283 / 640 : ℝ) - Real.pi * Real.exp (707 / 400 : ℝ) =
      -(Real.pi * Real.exp (707 / 400 : ℝ) - (283 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46051978595789257 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (46051978595789257 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1414_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (707 / 800 : ℝ) (283 / 320 : ℝ)) :
    (12089 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (398061 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1414_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1414_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1415_leftExp :
    (58635193793 / 10000000000 : ℝ) ≤ Real.exp (283 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (283 / 160 : ℝ) (1056829552001 / 1000000000000 : ℝ)
    (58635193793 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1415_rightExp :
    Real.exp (177 / 100 : ℝ) ≤ (11741706723 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (177 / 100 : ℝ) (264217708803 / 250000000000 : ℝ)
    (11741706723 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1415_denomUpper :
    Real.exp (36003288649029739 / 2000000000000000 : ℝ) ≤ (328840121246230617 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (36003288649029739 / 2000000000000000 : ℝ) (1755144843009
    / 1000000000000 : ℝ) (328840121246230617 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1415_denomLower :
    (321247845082424691 / 5000000000 : ℝ) ≤ Real.exp (22472856967317307 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22472856967317307 / 1250000000000000 : ℝ) (1753864123289
    / 1000000000000 : ℝ) (321247845082424691 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1415_product_lower :
    (23025981967317307 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (283 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1415_leftExp
    (by norm_num : (0 : ℝ) ≤ (58635193793 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1415_product_upper :
    Real.pi * Real.exp (177 / 100 : ℝ) ≤ (36887663649029739 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1415_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1415_endpointLower :
    (379143 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (283 / 320 : ℝ) (177 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23025981967317307 / 1250000000000000 : ℝ) (Real.pi * Real.exp (283 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1415_product_lower
  have hD : Real.exp (Real.pi * Real.exp (177 / 100 : ℝ) - (283 / 640 : ℝ)) ≤
      (328840121246230617 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1415_denomUpper
    linarith [hpThetaJensenCell1415_product_upper]
  have hi : (1 / (328840121246230617 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (177 / 100 : ℝ) - (283 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (328840121246230617 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (328840121246230617 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((283 / 640 : ℝ) - Real.pi * Real.exp (177 / 100 : ℝ)) := by
    rw [show (283 / 640 : ℝ) - Real.pi * Real.exp (177 / 100 : ℝ) =
      -(Real.pi * Real.exp (177 / 100 : ℝ) - (283 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (283 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (283 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1415_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (328840121246230617 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1415_endpointUpper :
    hpThetaJensenKernelEndpointUpper (283 / 320 : ℝ) (177 / 200 : ℝ) ≤ (381 / 9765625 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (177 / 100 : ℝ)) (36887663649029739 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (177 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1415_product_upper
  have hD : (321247845082424691 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (283 / 160 : ℝ) - (177 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1415_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1415_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (283 / 160 : ℝ) - (177 / 400 : ℝ)) ≤
      (1 / (321247845082424691 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (321247845082424691 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((177 / 400 : ℝ) - Real.pi * Real.exp (283 / 160 : ℝ)) ≤
      (2 / (321247845082424691 / 5000000000 : ℝ) : ℝ) := by
    rw [show (177 / 400 : ℝ) - Real.pi * Real.exp (283 / 160 : ℝ) =
      -(Real.pi * Real.exp (283 / 160 : ℝ) - (177 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36887663649029739 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (36887663649029739 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1415_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (283 / 320 : ℝ) (177 / 200 : ℝ)) :
    (379143 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (381 / 9765625 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1415_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1415_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1416_leftExp :
    (14677133403 / 2500000000 : ℝ) ≤ Real.exp (177 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (177 / 100 : ℝ) (1056870835211 / 1000000000000 : ℝ)
    (14677133403 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1416_rightExp :
    Real.exp (1417 / 800 : ℝ) ≤ (3673872823 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1417 / 800 : ℝ) (264228030009 / 250000000000 : ℝ)
    (3673872823 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1416_denomUpper :
    Real.exp (11265250643627039 / 625000000000000 : ℝ) ≤ (672818472780904513 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (11265250643627039 / 625000000000000 : ℝ) (175639345299 /
    100000000000 : ℝ) (672818472780904513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1416_denomLower :
    (328632730692788167 / 5000000000 : ℝ) ≤ Real.exp (5625316703974697 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (5625316703974697 / 312500000000000 : ℝ) (438777560279 /
    250000000000 : ℝ) (328632730692788167 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1416_product_lower :
    (5763695610224697 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (177 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1416_leftExp
    (by norm_num : (0 : ℝ) ≤ (14677133403 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1416_product_upper :
    Real.pi * Real.exp (1417 / 800 : ℝ) ≤ (11541813143627039 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1416_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1416_endpointLower :
    (371581 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (177 / 200 : ℝ) (1417 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5763695610224697 / 312500000000000 : ℝ) (Real.pi * Real.exp (177 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1416_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1417 / 800 : ℝ) - (177 / 400 : ℝ)) ≤
      (672818472780904513 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1416_denomUpper
    linarith [hpThetaJensenCell1416_product_upper]
  have hi : (1 / (672818472780904513 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1417 / 800 : ℝ) - (177 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (672818472780904513 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (672818472780904513 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((177 / 400 : ℝ) - Real.pi * Real.exp (1417 / 800 : ℝ)) := by
    rw [show (177 / 400 : ℝ) - Real.pi * Real.exp (1417 / 800 : ℝ) =
      -(Real.pi * Real.exp (1417 / 800 : ℝ) - (177 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (177 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (177 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1416_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (672818472780904513 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1416_endpointUpper :
    hpThetaJensenKernelEndpointUpper (177 / 200 : ℝ) (1417 / 1600 : ℝ) ≤ (191187 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1417 / 800 : ℝ)) (11541813143627039 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1417 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1416_product_upper
  have hD : (328632730692788167 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (177 / 100 : ℝ) - (1417 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1416_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1416_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (177 / 100 : ℝ) - (1417 / 3200 : ℝ)) ≤
      (1 / (328632730692788167 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (328632730692788167 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1417 / 3200 : ℝ) - Real.pi * Real.exp (177 / 100 : ℝ)) ≤
      (2 / (328632730692788167 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1417 / 3200 : ℝ) - Real.pi * Real.exp (177 / 100 : ℝ) =
      -(Real.pi * Real.exp (177 / 100 : ℝ) - (1417 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11541813143627039 / 625000000000000 : ℝ) ^ 2 - 6 *
      (11541813143627039 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1416_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (177 / 200 : ℝ) (1417 / 1600 : ℝ)) :
    (371581 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (191187 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1416_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1416_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1417_leftExp :
    (11756393033 / 2000000000 : ℝ) ≤ Real.exp (1417 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1417 / 800 : ℝ) (211382424007 / 200000000000 : ℝ)
    (11756393033 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1417_rightExp :
    Real.exp (709 / 400 : ℝ) ≤ (58855488567 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (709 / 400 : ℝ) (132119175809 / 125000000000 : ℝ)
    (58855488567 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1417_denomUpper :
    Real.exp (180471865893667231 / 10000000000000000 : ℝ) ≤ (344162504915495107 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (180471865893667231 / 10000000000000000 : ℝ)
    (1757644536091 / 1000000000000 : ℝ) (344162504915495107 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1417_denomLower :
    (336197069731370389 / 5000000000 : ℝ) ≤ Real.exp (4505942537666067 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4505942537666067 / 250000000000000 : ℝ) (878179413039 /
    500000000000 : ℝ) (336197069731370389 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1417_product_lower :
    (4616723787666067 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1417 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1417_leftExp
    (by norm_num : (0 : ℝ) ≤ (11756393033 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1417_product_upper :
    Real.pi * Real.exp (709 / 400 : ℝ) ≤ (184899990893667231 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1417_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1417_endpointLower :
    (569 / 15625000 : ℝ) ≤ hpThetaTraceEndpointLower (1417 / 1600 : ℝ) (709 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4616723787666067 / 250000000000000 : ℝ) (Real.pi * Real.exp (1417 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1417_product_lower
  have hD : Real.exp (Real.pi * Real.exp (709 / 400 : ℝ) - (1417 / 3200 : ℝ)) ≤
      (344162504915495107 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1417_denomUpper
    linarith [hpThetaJensenCell1417_product_upper]
  have hi : (1 / (344162504915495107 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (709 / 400 : ℝ) - (1417 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (344162504915495107 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (344162504915495107 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1417 / 3200 : ℝ) - Real.pi * Real.exp (709 / 400 : ℝ)) := by
    rw [show (1417 / 3200 : ℝ) - Real.pi * Real.exp (709 / 400 : ℝ) =
      -(Real.pi * Real.exp (709 / 400 : ℝ) - (1417 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1417 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1417 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1417_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (344162504915495107 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1417_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1417 / 1600 : ℝ) (709 / 800 : ℝ) ≤ (93687 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (709 / 400 : ℝ)) (184899990893667231 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (709 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1417_product_upper
  have hD : (336197069731370389 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1417 / 800 : ℝ) - (709 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1417_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1417_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1417 / 800 : ℝ) - (709 / 1600 : ℝ)) ≤
      (1 / (336197069731370389 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (336197069731370389 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((709 / 1600 : ℝ) - Real.pi * Real.exp (1417 / 800 : ℝ)) ≤
      (2 / (336197069731370389 / 5000000000 : ℝ) : ℝ) := by
    rw [show (709 / 1600 : ℝ) - Real.pi * Real.exp (1417 / 800 : ℝ) =
      -(Real.pi * Real.exp (1417 / 800 : ℝ) - (709 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (184899990893667231 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (184899990893667231 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1417_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1417 / 1600 : ℝ) (709 / 800 : ℝ)) :
    (569 / 15625000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (93687 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1417_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1417_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1418_leftExp :
    (14713872141 / 2500000000 : ℝ) ≤ Real.exp (709 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (709 / 400 : ℝ) (1056953406471 / 1000000000000 : ℝ)
    (14713872141 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1418_rightExp :
    Real.exp (1419 / 800 : ℝ) ≤ (7366137991 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1419 / 800 : ℝ) (1056994694521 / 1000000000000 : ℝ)
    (7366137991 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1418_denomUpper :
    Real.exp (22587501299559663 / 1250000000000000 : ℝ) ≤ (22006539779601221 / 312500000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (22587501299559663 / 1250000000000000 : ℝ) (1758898098337
    / 1000000000000 : ℝ) (22006539779601221 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1418_denomLower :
    (42993180737306727 / 625000000 : ℝ) ≤ Real.exp (5639548657148559 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5639548657148559 / 312500000000000 : ℝ) (1757609884111 /
    1000000000000 : ℝ) (42993180737306727 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1418_product_lower :
    (5778122875898559 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (709 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1418_leftExp
    (by norm_num : (0 : ℝ) ≤ (14713872141 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1418_product_upper :
    Real.pi * Real.exp (1419 / 800 : ℝ) ≤ (23141407549559663 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1418_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1418_endpointLower :
    (89219 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (709 / 800 : ℝ) (1419 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5778122875898559 / 312500000000000 : ℝ) (Real.pi * Real.exp (709 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1418_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1419 / 800 : ℝ) - (709 / 1600 : ℝ)) ≤
      (22006539779601221 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1418_denomUpper
    linarith [hpThetaJensenCell1418_product_upper]
  have hi : (1 / (22006539779601221 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1419 / 800 : ℝ) - (709 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22006539779601221 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22006539779601221 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((709 / 1600 : ℝ) - Real.pi * Real.exp (1419 / 800 : ℝ)) := by
    rw [show (709 / 1600 : ℝ) - Real.pi * Real.exp (1419 / 800 : ℝ) =
      -(Real.pi * Real.exp (1419 / 800 : ℝ) - (709 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (709 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (709 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1418_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22006539779601221 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1418_endpointUpper :
    hpThetaJensenKernelEndpointUpper (709 / 800 : ℝ) (1419 / 1600 : ℝ) ≤ (367263 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1419 / 800 : ℝ)) (23141407549559663 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1419 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1418_product_upper
  have hD : (42993180737306727 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (709 / 400 : ℝ) - (1419 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1418_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1418_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (709 / 400 : ℝ) - (1419 / 3200 : ℝ)) ≤
      (1 / (42993180737306727 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (42993180737306727 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1419 / 3200 : ℝ) - Real.pi * Real.exp (709 / 400 : ℝ)) ≤
      (2 / (42993180737306727 / 625000000 : ℝ) : ℝ) := by
    rw [show (1419 / 3200 : ℝ) - Real.pi * Real.exp (709 / 400 : ℝ) =
      -(Real.pi * Real.exp (709 / 400 : ℝ) - (1419 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23141407549559663 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (23141407549559663 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1418_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (709 / 800 : ℝ) (1419 / 1600 : ℝ)) :
    (89219 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (367263 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1418_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1418_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1419_leftExp :
    (2357164157 / 400000000 : ℝ) ≤ Real.exp (1419 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1419 / 800 : ℝ) (26424867363 / 25000000000 : ℝ)
    (2357164157 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1419_rightExp :
    Real.exp (71 / 40 : ℝ) ≤ (14750702841 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 40 : ℝ) (528517992091 / 500000000000 : ℝ)
    (14750702841 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1419_denomUpper :
    Real.exp (45232111040365713 / 2500000000000000 : ℝ) ≤ (144096186550608683 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (45232111040365713 / 2500000000000000 : ℝ) (176015414571
    / 100000000000 : ℝ) (144096186550608683 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1419_denomLower :
    (175941282929997641 / 2500000000 : ℝ) ≤ Real.exp (903468507289743 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (903468507289743 / 50000000000000 : ℝ) (879431710619 /
    500000000000 : ℝ) (175941282929997641 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1419_product_lower :
    (925656007289743 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (1419 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1419_leftExp
    (by norm_num : (0 : ℝ) ≤ (2357164157 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1419_product_upper :
    Real.pi * Real.exp (71 / 40 : ℝ) ≤ (46340704790365713 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1419_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1419_endpointLower :
    (10929 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (1419 / 1600 : ℝ) (71 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (925656007289743 / 50000000000000 : ℝ) (Real.pi * Real.exp (1419 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1419_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 40 : ℝ) - (1419 / 3200 : ℝ)) ≤
      (144096186550608683 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1419_denomUpper
    linarith [hpThetaJensenCell1419_product_upper]
  have hi : (1 / (144096186550608683 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 40 : ℝ) - (1419 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (144096186550608683 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (144096186550608683 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1419 / 3200 : ℝ) - Real.pi * Real.exp (71 / 40 : ℝ)) := by
    rw [show (1419 / 3200 : ℝ) - Real.pi * Real.exp (71 / 40 : ℝ) =
      -(Real.pi * Real.exp (71 / 40 : ℝ) - (1419 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1419 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1419 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1419_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (144096186550608683 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1419_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1419 / 1600 : ℝ) (71 / 80 : ℝ) ≤ (359917 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 40 : ℝ)) (46340704790365713 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1419_product_upper
  have hD : (175941282929997641 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1419 / 800 : ℝ) - (71 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1419_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1419_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1419 / 800 : ℝ) - (71 / 160 : ℝ)) ≤
      (1 / (175941282929997641 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (175941282929997641 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 160 : ℝ) - Real.pi * Real.exp (1419 / 800 : ℝ)) ≤
      (2 / (175941282929997641 / 2500000000 : ℝ) : ℝ) := by
    rw [show (71 / 160 : ℝ) - Real.pi * Real.exp (1419 / 800 : ℝ) =
      -(Real.pi * Real.exp (1419 / 800 : ℝ) - (71 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46340704790365713 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (46340704790365713 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1419_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1419 / 1600 : ℝ) (71 / 80 : ℝ)) :
    (10929 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (359917 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1419_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1419_endpointUpper

def hpThetaJensenCellsBatch070Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (255571 / 5000000000 : ℝ)
  | 1 => (501163 / 10000000000 : ℝ)
  | 2 => (245683 / 5000000000 : ℝ)
  | 3 => (240873 / 5000000000 : ℝ)
  | 4 => (472301 / 10000000000 : ℝ)
  | 5 => (115757 / 2500000000 : ℝ)
  | 6 => (453923 / 10000000000 : ℝ)
  | 7 => (222493 / 5000000000 : ℝ)
  | 8 => (436211 / 10000000000 : ℝ)
  | 9 => (213799 / 5000000000 : ℝ)
  | 10 => (209571 / 5000000000 : ℝ)
  | 11 => (205421 / 5000000000 : ℝ)
  | 12 => (80539 / 2000000000 : ℝ)
  | 13 => (394697 / 10000000000 : ℝ)
  | 14 => (12089 / 312500000 : ℝ)
  | 15 => (379143 / 10000000000 : ℝ)
  | 16 => (371581 / 10000000000 : ℝ)
  | 17 => (569 / 15625000 : ℝ)
  | 18 => (89219 / 2500000000 : ℝ)
  | 19 => (10929 / 312500000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch070Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (525749 / 10000000000 : ℝ)
  | 1 => (1031 / 20000000 : ℝ)
  | 2 => (126359 / 2500000000 : ℝ)
  | 3 => (99111 / 2000000000 : ℝ)
  | 4 => (121463 / 2500000000 : ℝ)
  | 5 => (476327 / 10000000000 : ℝ)
  | 6 => (233487 / 5000000000 : ℝ)
  | 7 => (457793 / 10000000000 : ℝ)
  | 8 => (448779 / 10000000000 : ℝ)
  | 9 => (439929 / 10000000000 : ℝ)
  | 10 => (215621 / 5000000000 : ℝ)
  | 11 => (211357 / 5000000000 : ℝ)
  | 12 => (414343 / 10000000000 : ℝ)
  | 13 => (203063 / 5000000000 : ℝ)
  | 14 => (398061 / 10000000000 : ℝ)
  | 15 => (381 / 9765625 : ℝ)
  | 16 => (191187 / 5000000000 : ℝ)
  | 17 => (93687 / 2500000000 : ℝ)
  | 18 => (367263 / 10000000000 : ℝ)
  | 19 => (359917 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch070_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch070Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch070Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1400_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1401_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1402_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1403_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1404_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1405_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1406_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1407_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1408_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1409_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1410_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1411_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1412_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1413_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1414_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1415_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1416_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1417_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1418_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1419_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper] at h ⊢
    exact h

end HodgeProofHP
