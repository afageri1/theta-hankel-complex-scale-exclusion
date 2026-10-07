import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell280_leftExp :
    (2838135097 / 2000000000 : ℝ) ≤ Real.exp (7 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 20 : ℝ) (252749383281 / 250000000000 : ℝ)
    (2838135097 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell280_rightExp :
    Real.exp (281 / 800 : ℝ) ≤ (7104212461 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (281 / 800 : ℝ) (1011037025987 / 1000000000000 : ℝ)
    (7104212461 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell280_denomUpper :
    Real.exp (21881044137990373 / 5000000000000000 : ℝ) ≤ (49709954181 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21881044137990373 / 5000000000000000 : ℝ) (286637239879
    / 250000000000 : ℝ) (49709954181 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell280_denomLower :
    (790688314907 / 10000000000 : ℝ) ≤ Real.exp (1092579689456803 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1092579689456803 / 250000000000000 : ℝ) (143292242471 /
    125000000000 : ℝ) (790688314907 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell280_product_lower :
    (1114532814456803 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell280_leftExp
    (by norm_num : (0 : ℝ) ≤ (2838135097 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell280_product_upper :
    Real.pi * Real.exp (281 / 800 : ℝ) ≤ (22318544137990373 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell280_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell280_endpointLower :
    (829042797 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 40 : ℝ) (281 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1114532814456803 / 250000000000000 : ℝ) (Real.pi * Real.exp (7 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell280_product_lower
  have hD : Real.exp (Real.pi * Real.exp (281 / 800 : ℝ) - (7 / 80 : ℝ)) ≤
      (49709954181 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell280_denomUpper
    linarith [hpThetaJensenCell280_product_upper]
  have hi : (1 / (49709954181 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (281 / 800 : ℝ) - (7 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (49709954181 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (49709954181 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 80 : ℝ) - Real.pi * Real.exp (281 / 800 : ℝ)) := by
    rw [show (7 / 80 : ℝ) - Real.pi * Real.exp (281 / 800 : ℝ) =
      -(Real.pi * Real.exp (281 / 800 : ℝ) - (7 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 20 : ℝ)) := by
    have h := hpThetaJensenCell280_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (49709954181 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell280_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 40 : ℝ) (281 / 1600 : ℝ) ≤ (6710089071 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (281 / 800 : ℝ)) (22318544137990373 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (281 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell280_product_upper
  have hD : (790688314907 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 20 : ℝ) - (281 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell280_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell280_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 20 : ℝ) - (281 / 3200 : ℝ)) ≤
      (1 / (790688314907 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (790688314907 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((281 / 3200 : ℝ) - Real.pi * Real.exp (7 / 20 : ℝ)) ≤
      (2 / (790688314907 / 10000000000 : ℝ) : ℝ) := by
    rw [show (281 / 3200 : ℝ) - Real.pi * Real.exp (7 / 20 : ℝ) =
      -(Real.pi * Real.exp (7 / 20 : ℝ) - (281 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22318544137990373 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22318544137990373 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell280_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 40 : ℝ) (281 / 1600 : ℝ)) :
    (829042797 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6710089071 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell280_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell280_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell281_leftExp :
    (14208424921 / 10000000000 : ℝ) ≤ Real.exp (281 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (281 / 800 : ℝ) (505518512993 / 500000000000 : ℝ)
    (14208424921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell281_rightExp :
    Real.exp (141 / 400 : ℝ) ≤ (7113098279 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (141 / 400 : ℝ) (126384565049 / 125000000000 : ℝ)
    (7113098279 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell281_denomUpper :
    Real.exp (21907397261618447 / 5000000000000000 : ℝ) ≤ (199890593469 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21907397261618447 / 5000000000000000 : ℝ) (573368909867
    / 500000000000 : ℝ) (199890593469 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell281_denomLower :
    (397430596501 / 5000000000 : ℝ) ≤ Real.exp (5469478008051779 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5469478008051779 / 1250000000000000 : ℝ) (14331581441 /
    12500000000 : ℝ) (397430596501 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell281_product_lower :
    (5579634258051779 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (281 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell281_leftExp
    (by norm_num : (0 : ℝ) ≤ (14208424921 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell281_product_upper :
    Real.pi * Real.exp (141 / 400 : ℝ) ≤ (22346459761618447 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell281_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell281_endpointLower :
    (13236363423 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (281 / 1600 : ℝ) (141 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5579634258051779 / 1250000000000000 : ℝ) (Real.pi * Real.exp (281 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell281_product_lower
  have hD : Real.exp (Real.pi * Real.exp (141 / 400 : ℝ) - (281 / 3200 : ℝ)) ≤
      (199890593469 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell281_denomUpper
    linarith [hpThetaJensenCell281_product_upper]
  have hi : (1 / (199890593469 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (141 / 400 : ℝ) - (281 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (199890593469 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (199890593469 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((281 / 3200 : ℝ) - Real.pi * Real.exp (141 / 400 : ℝ)) := by
    rw [show (281 / 3200 : ℝ) - Real.pi * Real.exp (141 / 400 : ℝ) =
      -(Real.pi * Real.exp (141 / 400 : ℝ) - (281 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (281 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (281 / 800 : ℝ)) := by
    have h := hpThetaJensenCell281_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (199890593469 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell281_endpointUpper :
    hpThetaJensenKernelEndpointUpper (281 / 1600 : ℝ) (141 / 800 : ℝ) ≤ (6695801143 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (141 / 400 : ℝ)) (22346459761618447 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (141 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell281_product_upper
  have hD : (397430596501 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (281 / 800 : ℝ) - (141 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell281_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell281_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (281 / 800 : ℝ) - (141 / 1600 : ℝ)) ≤
      (1 / (397430596501 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (397430596501 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((141 / 1600 : ℝ) - Real.pi * Real.exp (281 / 800 : ℝ)) ≤
      (2 / (397430596501 / 5000000000 : ℝ) : ℝ) := by
    rw [show (141 / 1600 : ℝ) - Real.pi * Real.exp (281 / 800 : ℝ) =
      -(Real.pi * Real.exp (281 / 800 : ℝ) - (141 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22346459761618447 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22346459761618447 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell281_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (281 / 1600 : ℝ) (141 / 800 : ℝ)) :
    (13236363423 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6695801143 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell281_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell281_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell282_leftExp :
    (14226196557 / 10000000000 : ℝ) ≤ Real.exp (141 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (141 / 400 : ℝ) (1011076520391 / 1000000000000 : ℝ)
    (14226196557 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell282_rightExp :
    Real.exp (283 / 800 : ℝ) ≤ (14243990423 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (283 / 800 : ℝ) (50555800817 / 50000000000 : ℝ)
    (14243990423 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell282_denomUpper :
    Real.exp (43867570604963839 / 10000000000000000 : ℝ) ≤ (803793305563 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43867570604963839 / 10000000000000000 : ℝ) (573463480679
    / 500000000000 : ℝ) (803793305563 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell282_denomLower :
    (799061666487 / 10000000000 : ℝ) ≤ Real.exp (5476066286737343 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5476066286737343 / 1250000000000000 : ℝ) (573357685869 /
    500000000000 : ℝ) (799061666487 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell282_product_lower :
    (5586613161737343 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (141 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell282_leftExp
    (by norm_num : (0 : ℝ) ≤ (14226196557 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell282_product_upper :
    Real.pi * Real.exp (283 / 800 : ℝ) ≤ (44748820604963839 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell282_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell282_endpointLower :
    (412749831 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (141 / 800 : ℝ) (283 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5586613161737343 / 1250000000000000 : ℝ) (Real.pi * Real.exp (141 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell282_product_lower
  have hD : Real.exp (Real.pi * Real.exp (283 / 800 : ℝ) - (141 / 1600 : ℝ)) ≤
      (803793305563 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell282_denomUpper
    linarith [hpThetaJensenCell282_product_upper]
  have hi : (1 / (803793305563 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (283 / 800 : ℝ) - (141 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (803793305563 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (803793305563 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((141 / 1600 : ℝ) - Real.pi * Real.exp (283 / 800 : ℝ)) := by
    rw [show (141 / 1600 : ℝ) - Real.pi * Real.exp (283 / 800 : ℝ) =
      -(Real.pi * Real.exp (283 / 800 : ℝ) - (141 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (141 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (141 / 400 : ℝ)) := by
    have h := hpThetaJensenCell282_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (803793305563 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell282_endpointUpper :
    hpThetaJensenKernelEndpointUpper (141 / 800 : ℝ) (283 / 1600 : ℝ) ≤ (13362978203 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (283 / 800 : ℝ)) (44748820604963839 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (283 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell282_product_upper
  have hD : (799061666487 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (141 / 400 : ℝ) - (283 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell282_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell282_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (141 / 400 : ℝ) - (283 / 3200 : ℝ)) ≤
      (1 / (799061666487 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (799061666487 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((283 / 3200 : ℝ) - Real.pi * Real.exp (141 / 400 : ℝ)) ≤
      (2 / (799061666487 / 10000000000 : ℝ) : ℝ) := by
    rw [show (283 / 3200 : ℝ) - Real.pi * Real.exp (141 / 400 : ℝ) =
      -(Real.pi * Real.exp (141 / 400 : ℝ) - (283 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44748820604963839 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44748820604963839 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell282_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (141 / 800 : ℝ) (283 / 1600 : ℝ)) :
    (412749831 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13362978203 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell282_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell282_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell283_leftExp :
    (14243990421 / 10000000000 : ℝ) ≤ Real.exp (283 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (283 / 800 : ℝ) (1011116016339 / 1000000000000 : ℝ)
    (14243990421 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell283_rightExp :
    Real.exp (71 / 200 : ℝ) ≤ (14261806543 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (71 / 200 : ℝ) (1011155513831 / 1000000000000 : ℝ)
    (14261806543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell283_denomUpper :
    Real.exp (43920416602842999 / 10000000000000000 : ℝ) ≤ (6312908399 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43920416602842999 / 10000000000000000 : ℝ)
    (1147116384811 / 1000000000000 : ℝ) (6312908399 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell283_denomLower :
    (803289946983 / 10000000000 : ℝ) ≤ Real.exp (5482663294336279 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5482663294336279 / 1250000000000000 : ℝ) (229380901917 /
    200000000000 : ℝ) (803289946983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell283_product_lower :
    (5593600794336279 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (283 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell283_leftExp
    (by norm_num : (0 : ℝ) ≤ (14243990421 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell283_product_upper :
    Real.pi * Real.exp (71 / 200 : ℝ) ≤ (44804791602842999 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell283_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell283_endpointLower :
    (3294894689 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (283 / 1600 : ℝ) (71 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5593600794336279 / 1250000000000000 : ℝ) (Real.pi * Real.exp (283 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell283_product_lower
  have hD : Real.exp (Real.pi * Real.exp (71 / 200 : ℝ) - (283 / 3200 : ℝ)) ≤
      (6312908399 / 78125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell283_denomUpper
    linarith [hpThetaJensenCell283_product_upper]
  have hi : (1 / (6312908399 / 78125000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (71 / 200 : ℝ) - (283 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6312908399 / 78125000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6312908399 / 78125000 : ℝ) : ℝ) ≤
      2 * Real.exp ((283 / 3200 : ℝ) - Real.pi * Real.exp (71 / 200 : ℝ)) := by
    rw [show (283 / 3200 : ℝ) - Real.pi * Real.exp (71 / 200 : ℝ) =
      -(Real.pi * Real.exp (71 / 200 : ℝ) - (283 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (283 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (283 / 800 : ℝ)) := by
    have h := hpThetaJensenCell283_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6312908399 / 78125000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell283_endpointUpper :
    hpThetaJensenKernelEndpointUpper (283 / 1600 : ℝ) (71 / 400 : ℝ) ≤ (6667153191 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (71 / 200 : ℝ)) (44804791602842999 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (71 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell283_product_upper
  have hD : (803289946983 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (283 / 800 : ℝ) - (71 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell283_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell283_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (283 / 800 : ℝ) - (71 / 800 : ℝ)) ≤
      (1 / (803289946983 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (803289946983 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((71 / 800 : ℝ) - Real.pi * Real.exp (283 / 800 : ℝ)) ≤
      (2 / (803289946983 / 10000000000 : ℝ) : ℝ) := by
    rw [show (71 / 800 : ℝ) - Real.pi * Real.exp (283 / 800 : ℝ) =
      -(Real.pi * Real.exp (283 / 800 : ℝ) - (71 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (44804791602842999 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (44804791602842999 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell283_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (283 / 1600 : ℝ) (71 / 400 : ℝ)) :
    (3294894689 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6667153191 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell283_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell283_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell284_leftExp :
    (7130903271 / 5000000000 : ℝ) ≤ Real.exp (71 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 200 : ℝ) (101115551383 / 100000000000 : ℝ)
    (7130903271 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell284_rightExp :
    Real.exp (57 / 160 : ℝ) ≤ (3569911237 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 160 : ℝ) (202239002573 / 200000000000 : ℝ)
    (3569911237 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell284_denomUpper :
    Real.exp (10993333152780541 / 2500000000000000 : ℝ) ≤ (812339498281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10993333152780541 / 2500000000000000 : ℝ) (573653045279
    / 500000000000 : ℝ) (812339498281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell284_denomLower :
    (80754624821 / 1000000000 : ℝ) ≤ Real.exp (2744634521118429 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2744634521118429 / 625000000000000 : ℝ) (1147093929277 /
    1000000000000 : ℝ) (80754624821 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell284_product_lower :
    (2800298583618429 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell284_leftExp
    (by norm_num : (0 : ℝ) ≤ (7130903271 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell284_product_upper :
    Real.pi * Real.exp (57 / 160 : ℝ) ≤ (11215208152780541 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell284_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell284_endpointLower :
    (13151116399 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 400 : ℝ) (57 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2800298583618429 / 625000000000000 : ℝ) (Real.pi * Real.exp (71 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell284_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 160 : ℝ) - (71 / 800 : ℝ)) ≤
      (812339498281 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell284_denomUpper
    linarith [hpThetaJensenCell284_product_upper]
  have hi : (1 / (812339498281 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 160 : ℝ) - (71 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (812339498281 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (812339498281 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 800 : ℝ) - Real.pi * Real.exp (57 / 160 : ℝ)) := by
    rw [show (71 / 800 : ℝ) - Real.pi * Real.exp (57 / 160 : ℝ) =
      -(Real.pi * Real.exp (57 / 160 : ℝ) - (71 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 200 : ℝ)) := by
    have h := hpThetaJensenCell284_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (812339498281 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell284_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 400 : ℝ) (57 / 320 : ℝ) ≤ (13305587317 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 160 : ℝ)) (11215208152780541 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell284_product_upper
  have hD : (80754624821 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 200 : ℝ) - (57 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell284_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell284_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 200 : ℝ) - (57 / 640 : ℝ)) ≤
      (1 / (80754624821 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (80754624821 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 640 : ℝ) - Real.pi * Real.exp (71 / 200 : ℝ)) ≤
      (2 / (80754624821 / 1000000000 : ℝ) : ℝ) := by
    rw [show (57 / 640 : ℝ) - Real.pi * Real.exp (71 / 200 : ℝ) =
      -(Real.pi * Real.exp (71 / 200 : ℝ) - (57 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11215208152780541 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (11215208152780541 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell284_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 400 : ℝ) (57 / 320 : ℝ)) :
    (13151116399 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13305587317 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell284_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell284_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell285_leftExp :
    (14279644947 / 10000000000 : ℝ) ≤ Real.exp (57 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 160 : ℝ) (3949980519 / 3906250000 : ℝ) (14279644947
    / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell285_rightExp :
    Real.exp (143 / 400 : ℝ) ≤ (2859501133 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (143 / 400 : ℝ) (505617256721 / 500000000000 : ℝ)
    (2859501133 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell285_denomUpper :
    Real.exp (8805263742924869 / 2000000000000000 : ℝ) ≤ (408327596129 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8805263742924869 / 2000000000000000 : ℝ) (229499215807 /
    200000000000 : ℝ) (408327596129 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell285_denomLower :
    (405915392597 / 5000000000 : ℝ) ≤ Real.exp (5495883541041953 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5495883541041953 / 1250000000000000 : ℝ) (1147283631247
    / 1000000000000 : ℝ) (405915392597 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell285_product_lower :
    (5607602291041953 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell285_leftExp
    (by norm_num : (0 : ℝ) ≤ (14279644947 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell285_product_upper :
    Real.pi * Real.exp (143 / 400 : ℝ) ≤ (8983388742924869 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell285_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell285_endpointLower :
    (3280652003 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 320 : ℝ) (143 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5607602291041953 / 1250000000000000 : ℝ) (Real.pi * Real.exp (57 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell285_product_lower
  have hD : Real.exp (Real.pi * Real.exp (143 / 400 : ℝ) - (57 / 640 : ℝ)) ≤
      (408327596129 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell285_denomUpper
    linarith [hpThetaJensenCell285_product_upper]
  have hi : (1 / (408327596129 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (143 / 400 : ℝ) - (57 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (408327596129 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (408327596129 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 640 : ℝ) - Real.pi * Real.exp (143 / 400 : ℝ)) := by
    rw [show (57 / 640 : ℝ) - Real.pi * Real.exp (143 / 400 : ℝ) =
      -(Real.pi * Real.exp (143 / 400 : ℝ) - (57 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 160 : ℝ)) := by
    have h := hpThetaJensenCell285_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (408327596129 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell285_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 320 : ℝ) (143 / 800 : ℝ) ≤ (12965646 / 9765625 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (143 / 400 : ℝ)) (8983388742924869 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (143 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell285_product_upper
  have hD : (405915392597 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 160 : ℝ) - (143 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell285_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell285_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 160 : ℝ) - (143 / 1600 : ℝ)) ≤
      (1 / (405915392597 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (405915392597 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((143 / 1600 : ℝ) - Real.pi * Real.exp (57 / 160 : ℝ)) ≤
      (2 / (405915392597 / 5000000000 : ℝ) : ℝ) := by
    rw [show (143 / 1600 : ℝ) - Real.pi * Real.exp (57 / 160 : ℝ) =
      -(Real.pi * Real.exp (57 / 160 : ℝ) - (143 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8983388742924869 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (8983388742924869 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell285_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 320 : ℝ) (143 / 800 : ℝ)) :
    (3280652003 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12965646 / 9765625 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell285_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell285_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell286_leftExp :
    (111699263 / 78125000 : ℝ) ≤ Real.exp (143 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (143 / 400 : ℝ) (1011234513441 / 1000000000000 : ℝ)
    (111699263 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell286_rightExp :
    Real.exp (287 / 800 : ℝ) ≤ (7157694361 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (287 / 800 : ℝ) (1011274015561 / 1000000000000 : ℝ)
    (7157694361 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell286_denomUpper :
    Real.exp (22039687500657073 / 5000000000000000 : ℝ) ≤ (205249894027 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22039687500657073 / 5000000000000000 : ℝ) (573843175343
    / 500000000000 : ℝ) (205249894027 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell286_denomLower :
    (816143775069 / 10000000000 : ℝ) ≤ Real.exp (85976668777299 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (85976668777299 / 19531250000000 : ℝ) (57373680797 /
    50000000000 : ℝ) (816143775069 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell286_product_lower :
    (43864188880837 / 9765625000000 : ℝ) ≤ Real.pi * Real.exp (143 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell286_leftExp
    (by norm_num : (0 : ℝ) ≤ (111699263 / 78125000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell286_product_upper :
    Real.pi * Real.exp (287 / 800 : ℝ) ≤ (22486562500657073 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell286_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell286_endpointLower :
    (6547027043 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (143 / 800 : ℝ) (287 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (43864188880837 / 9765625000000 : ℝ) (Real.pi * Real.exp (143 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell286_product_lower
  have hD : Real.exp (Real.pi * Real.exp (287 / 800 : ℝ) - (143 / 1600 : ℝ)) ≤
      (205249894027 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell286_denomUpper
    linarith [hpThetaJensenCell286_product_upper]
  have hi : (1 / (205249894027 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (287 / 800 : ℝ) - (143 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (205249894027 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (205249894027 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((143 / 1600 : ℝ) - Real.pi * Real.exp (287 / 800 : ℝ)) := by
    rw [show (143 / 1600 : ℝ) - Real.pi * Real.exp (287 / 800 : ℝ) =
      -(Real.pi * Real.exp (287 / 800 : ℝ) - (143 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (143 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (143 / 400 : ℝ)) := by
    have h := hpThetaJensenCell286_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (205249894027 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell286_endpointUpper :
    hpThetaJensenKernelEndpointUpper (143 / 800 : ℝ) (287 / 1600 : ℝ) ≤ (2649601887 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (287 / 800 : ℝ)) (22486562500657073 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (287 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell286_product_upper
  have hD : (816143775069 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (143 / 400 : ℝ) - (287 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell286_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell286_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (143 / 400 : ℝ) - (287 / 3200 : ℝ)) ≤
      (1 / (816143775069 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (816143775069 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((287 / 3200 : ℝ) - Real.pi * Real.exp (143 / 400 : ℝ)) ≤
      (2 / (816143775069 / 10000000000 : ℝ) : ℝ) := by
    rw [show (287 / 3200 : ℝ) - Real.pi * Real.exp (143 / 400 : ℝ) =
      -(Real.pi * Real.exp (143 / 400 : ℝ) - (287 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22486562500657073 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22486562500657073 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell286_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (143 / 800 : ℝ) (287 / 1600 : ℝ)) :
    (6547027043 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2649601887 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell286_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell286_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell287_leftExp :
    (178942359 / 125000000 : ℝ) ≤ Real.exp (287 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (287 / 800 : ℝ) (25281850389 / 25000000000 : ℝ)
    (178942359 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell287_rightExp :
    Real.exp (9 / 25 : ℝ) ≤ (7166647073 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 25 : ℝ) (126414189903 / 125000000000 : ℝ)
    (7166647073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell287_denomUpper :
    Real.exp (22066250778007289 / 5000000000000000 : ℝ) ≤ (412686435303 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22066250778007289 / 5000000000000000 : ℝ) (573938452973
    / 500000000000 : ℝ) (412686435303 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell287_denomLower :
    (205121359149 / 2500000000 : ℝ) ≤ Real.exp (68864235436941 / 15625000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (68864235436941 / 15625000000000 : ℝ) (1147663883791 /
    1000000000000 : ℝ) (205121359149 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell287_product_lower :
    (70270485436941 / 15625000000000 : ℝ) ≤ Real.pi * Real.exp (287 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell287_leftExp
    (by norm_num : (0 : ℝ) ≤ (178942359 / 125000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell287_product_upper :
    Real.pi * Real.exp (9 / 25 : ℝ) ≤ (22514688278007289 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell287_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell287_endpointLower :
    (1633181889 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (287 / 1600 : ℝ) (9 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (70270485436941 / 15625000000000 : ℝ) (Real.pi * Real.exp (287 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell287_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 25 : ℝ) - (287 / 3200 : ℝ)) ≤
      (412686435303 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell287_denomUpper
    linarith [hpThetaJensenCell287_product_upper]
  have hi : (1 / (412686435303 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 25 : ℝ) - (287 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (412686435303 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (412686435303 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((287 / 3200 : ℝ) - Real.pi * Real.exp (9 / 25 : ℝ)) := by
    rw [show (287 / 3200 : ℝ) - Real.pi * Real.exp (9 / 25 : ℝ) =
      -(Real.pi * Real.exp (9 / 25 : ℝ) - (287 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (287 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (287 / 800 : ℝ)) := by
    have h := hpThetaJensenCell287_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (412686435303 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell287_endpointUpper :
    hpThetaJensenKernelEndpointUpper (287 / 1600 : ℝ) (9 / 50 : ℝ) ≤ (13219151607 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 25 : ℝ)) (22514688278007289 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell287_product_upper
  have hD : (205121359149 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (287 / 800 : ℝ) - (9 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell287_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell287_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (287 / 800 : ℝ) - (9 / 100 : ℝ)) ≤
      (1 / (205121359149 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (205121359149 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 100 : ℝ) - Real.pi * Real.exp (287 / 800 : ℝ)) ≤
      (2 / (205121359149 / 2500000000 : ℝ) : ℝ) := by
    rw [show (9 / 100 : ℝ) - Real.pi * Real.exp (287 / 800 : ℝ) =
      -(Real.pi * Real.exp (287 / 800 : ℝ) - (9 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22514688278007289 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22514688278007289 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell287_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (287 / 1600 : ℝ) (9 / 50 : ℝ)) :
    (1633181889 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13219151607 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell287_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell287_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell288_leftExp :
    (2866658829 / 2000000000 : ℝ) ≤ Real.exp (9 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 25 : ℝ) (1011313519223 / 1000000000000 : ℝ)
    (2866658829 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell288_rightExp :
    Real.exp (289 / 800 : ℝ) ≤ (14351221967 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (289 / 800 : ℝ) (101135302443 / 100000000000 : ℝ)
    (14351221967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell288_denomUpper :
    Real.exp (44185698472973431 / 10000000000000000 : ℝ) ≤ (829775299221 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44185698472973431 / 10000000000000000 : ℝ) (229613549057
    / 200000000000 : ℝ) (829775299221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell288_denomLower :
    (824855991167 / 10000000000 : ℝ) ≤ Real.exp (1103155930489471 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1103155930489471 / 250000000000000 : ℝ) (286963608817 /
    250000000000 : ℝ) (824855991167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell288_product_lower :
    (1125734055489471 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell288_leftExp
    (by norm_num : (0 : ℝ) ≤ (2866658829 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell288_product_upper :
    Real.pi * Real.exp (289 / 800 : ℝ) ≤ (45085698472973431 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell288_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell288_endpointLower :
    (13036811579 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 50 : ℝ) (289 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1125734055489471 / 250000000000000 : ℝ) (Real.pi * Real.exp (9 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell288_product_lower
  have hD : Real.exp (Real.pi * Real.exp (289 / 800 : ℝ) - (9 / 100 : ℝ)) ≤
      (829775299221 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell288_denomUpper
    linarith [hpThetaJensenCell288_product_upper]
  have hi : (1 / (829775299221 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (289 / 800 : ℝ) - (9 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (829775299221 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (829775299221 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 100 : ℝ) - Real.pi * Real.exp (289 / 800 : ℝ)) := by
    rw [show (9 / 100 : ℝ) - Real.pi * Real.exp (289 / 800 : ℝ) =
      -(Real.pi * Real.exp (289 / 800 : ℝ) - (9 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 25 : ℝ)) := by
    have h := hpThetaJensenCell288_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (829775299221 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell288_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 50 : ℝ) (289 / 1600 : ℝ) ≤ (206097633 / 156250000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (289 / 800 : ℝ)) (45085698472973431 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (289 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell288_product_upper
  have hD : (824855991167 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 25 : ℝ) - (289 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell288_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell288_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 25 : ℝ) - (289 / 3200 : ℝ)) ≤
      (1 / (824855991167 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (824855991167 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((289 / 3200 : ℝ) - Real.pi * Real.exp (9 / 25 : ℝ)) ≤
      (2 / (824855991167 / 10000000000 : ℝ) : ℝ) := by
    rw [show (289 / 3200 : ℝ) - Real.pi * Real.exp (9 / 25 : ℝ) =
      -(Real.pi * Real.exp (9 / 25 : ℝ) - (289 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45085698472973431 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (45085698472973431 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell288_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 50 : ℝ) (289 / 1600 : ℝ)) :
    (13036811579 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (206097633 / 156250000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell288_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell288_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell289_leftExp :
    (2870244393 / 2000000000 : ℝ) ≤ Real.exp (289 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (289 / 800 : ℝ) (1011353024429 / 1000000000000 : ℝ)
    (2870244393 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell289_rightExp :
    Real.exp (29 / 80 : ℝ) ≤ (14369172211 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 80 : ℝ) (1011392531179 / 1000000000000 : ℝ)
    (14369172211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell289_denomUpper :
    Real.exp (44238965833872123 / 10000000000000000 : ℝ) ≤ (52137942891 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44238965833872123 / 10000000000000000 : ℝ) (574129434563
    / 500000000000 : ℝ) (52137942891 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell289_denomLower :
    (1619639963 / 19531250 : ℝ) ≤ Real.exp (1104485852886707 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1104485852886707 / 250000000000000 : ℝ) (229609054159 /
    200000000000 : ℝ) (1619639963 / 19531250 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell289_product_lower :
    (1127142102886707 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (289 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell289_leftExp
    (by norm_num : (0 : ℝ) ≤ (2870244393 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell289_product_upper :
    Real.pi * Real.exp (29 / 80 : ℝ) ≤ (45142090833872123 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell289_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell289_endpointLower :
    (650406199 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (289 / 1600 : ℝ) (29 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1127142102886707 / 250000000000000 : ℝ) (Real.pi * Real.exp (289 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell289_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 80 : ℝ) - (289 / 3200 : ℝ)) ≤
      (52137942891 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell289_denomUpper
    linarith [hpThetaJensenCell289_product_upper]
  have hi : (1 / (52137942891 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 80 : ℝ) - (289 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (52137942891 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (52137942891 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((289 / 3200 : ℝ) - Real.pi * Real.exp (29 / 80 : ℝ)) := by
    rw [show (289 / 3200 : ℝ) - Real.pi * Real.exp (29 / 80 : ℝ) =
      -(Real.pi * Real.exp (29 / 80 : ℝ) - (289 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (289 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (289 / 800 : ℝ)) := by
    have h := hpThetaJensenCell289_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (52137942891 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell289_endpointUpper :
    hpThetaJensenKernelEndpointUpper (289 / 1600 : ℝ) (29 / 160 : ℝ) ≤ (13161300647 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 80 : ℝ)) (45142090833872123 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell289_product_upper
  have hD : (1619639963 / 19531250 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (289 / 800 : ℝ) - (29 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell289_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell289_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (289 / 800 : ℝ) - (29 / 320 : ℝ)) ≤
      (1 / (1619639963 / 19531250 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1619639963 / 19531250 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 320 : ℝ) - Real.pi * Real.exp (289 / 800 : ℝ)) ≤
      (2 / (1619639963 / 19531250 : ℝ) : ℝ) := by
    rw [show (29 / 320 : ℝ) - Real.pi * Real.exp (289 / 800 : ℝ) =
      -(Real.pi * Real.exp (289 / 800 : ℝ) - (29 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45142090833872123 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (45142090833872123 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell289_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (289 / 1600 : ℝ) (29 / 160 : ℝ)) :
    (650406199 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13161300647 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell289_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell289_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell290_leftExp :
    (14369172209 / 10000000000 : ℝ) ≤ Real.exp (29 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 80 : ℝ) (505696265589 / 500000000000 : ℝ)
    (14369172209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell290_rightExp :
    Real.exp (291 / 800 : ℝ) ≤ (14387144907 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (291 / 800 : ℝ) (63214502467 / 62500000000 : ℝ)
    (14387144907 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell290_denomUpper :
    Real.exp (44292303729816851 / 10000000000000000 : ℝ) ≤ (52416778673 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44292303729816851 / 10000000000000000 : ℝ) (143556284741
    / 125000000000 : ℝ) (52416778673 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell290_denomLower :
    (83368467123 / 1000000000 : ℝ) ≤ Real.exp (5529087682302091 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5529087682302091 / 1250000000000000 : ℝ) (114823639083 /
    100000000000 : ℝ) (83368467123 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell290_product_lower :
    (5642759557302091 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell290_leftExp
    (by norm_num : (0 : ℝ) ≤ (14369172209 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell290_product_upper :
    Real.pi * Real.exp (291 / 800 : ℝ) ≤ (45198553729816851 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell290_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell290_endpointLower :
    (6489696403 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 160 : ℝ) (291 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5642759557302091 / 1250000000000000 : ℝ) (Real.pi * Real.exp (29 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell290_product_lower
  have hD : Real.exp (Real.pi * Real.exp (291 / 800 : ℝ) - (29 / 320 : ℝ)) ≤
      (52416778673 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell290_denomUpper
    linarith [hpThetaJensenCell290_product_upper]
  have hi : (1 / (52416778673 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (291 / 800 : ℝ) - (29 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (52416778673 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (52416778673 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 320 : ℝ) - Real.pi * Real.exp (291 / 800 : ℝ)) := by
    rw [show (29 / 320 : ℝ) - Real.pi * Real.exp (291 / 800 : ℝ) =
      -(Real.pi * Real.exp (291 / 800 : ℝ) - (29 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 80 : ℝ)) := by
    have h := hpThetaJensenCell290_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (52416778673 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell290_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 160 : ℝ) (291 / 1600 : ℝ) ≤ (6566154253 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (291 / 800 : ℝ)) (45198553729816851 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (291 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell290_product_upper
  have hD : (83368467123 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 80 : ℝ) - (291 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell290_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell290_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 80 : ℝ) - (291 / 3200 : ℝ)) ≤
      (1 / (83368467123 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (83368467123 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((291 / 3200 : ℝ) - Real.pi * Real.exp (29 / 80 : ℝ)) ≤
      (2 / (83368467123 / 1000000000 : ℝ) : ℝ) := by
    rw [show (291 / 3200 : ℝ) - Real.pi * Real.exp (29 / 80 : ℝ) =
      -(Real.pi * Real.exp (29 / 80 : ℝ) - (291 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45198553729816851 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (45198553729816851 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell290_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 160 : ℝ) (291 / 1600 : ℝ)) :
    (6489696403 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6566154253 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell290_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell290_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell291_leftExp :
    (2877428981 / 2000000000 : ℝ) ≤ Real.exp (291 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (291 / 800 : ℝ) (1011432039471 / 1000000000000 : ℝ)
    (2877428981 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell291_rightExp :
    Real.exp (73 / 200 : ℝ) ≤ (7202570041 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 200 : ℝ) (1011471549307 / 1000000000000 : ℝ)
    (7202570041 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell291_denomUpper :
    Real.exp (22172856122815313 / 5000000000000000 : ℝ) ≤ (843159645233 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22172856122815313 / 5000000000000000 : ℝ) (1148641972127
    / 1000000000000 : ℝ) (843159645233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell291_denomLower :
    (26191976511 / 312500000 : ℝ) ≤ Real.exp (1107150983409719 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1107150983409719 / 250000000000000 : ℝ) (1148427795821 /
    1000000000000 : ℝ) (26191976511 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell291_product_lower :
    (1129963483409719 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (291 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell291_leftExp
    (by norm_num : (0 : ℝ) ≤ (2877428981 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell291_product_upper :
    Real.pi * Real.exp (73 / 200 : ℝ) ≤ (22627543622815313 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell291_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell291_endpointLower :
    (12950618553 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (291 / 1600 : ℝ) (73 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1129963483409719 / 250000000000000 : ℝ) (Real.pi * Real.exp (291 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell291_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 200 : ℝ) - (291 / 3200 : ℝ)) ≤
      (843159645233 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell291_denomUpper
    linarith [hpThetaJensenCell291_product_upper]
  have hi : (1 / (843159645233 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 200 : ℝ) - (291 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (843159645233 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (843159645233 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((291 / 3200 : ℝ) - Real.pi * Real.exp (73 / 200 : ℝ)) := by
    rw [show (291 / 3200 : ℝ) - Real.pi * Real.exp (73 / 200 : ℝ) =
      -(Real.pi * Real.exp (73 / 200 : ℝ) - (291 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (291 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (291 / 800 : ℝ)) := by
    have h := hpThetaJensenCell291_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (843159645233 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell291_endpointUpper :
    hpThetaJensenKernelEndpointUpper (291 / 1600 : ℝ) (73 / 400 : ℝ) ≤ (6551636291 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 200 : ℝ)) (22627543622815313 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell291_product_upper
  have hD : (26191976511 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (291 / 800 : ℝ) - (73 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell291_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell291_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (291 / 800 : ℝ) - (73 / 800 : ℝ)) ≤
      (1 / (26191976511 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26191976511 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 800 : ℝ) - Real.pi * Real.exp (291 / 800 : ℝ)) ≤
      (2 / (26191976511 / 312500000 : ℝ) : ℝ) := by
    rw [show (73 / 800 : ℝ) - Real.pi * Real.exp (291 / 800 : ℝ) =
      -(Real.pi * Real.exp (291 / 800 : ℝ) - (73 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22627543622815313 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22627543622815313 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell291_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (291 / 1600 : ℝ) (73 / 400 : ℝ)) :
    (12950618553 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6551636291 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell291_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell291_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell292_leftExp :
    (14405140081 / 10000000000 : ℝ) ≤ Real.exp (73 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 200 : ℝ) (505735774653 / 500000000000 : ℝ)
    (14405140081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell292_rightExp :
    Real.exp (293 / 800 : ℝ) ≤ (7211578883 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (293 / 800 : ℝ) (505755530343 / 500000000000 : ℝ)
    (7211578883 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell292_denomUpper :
    Real.exp (22199595737780619 / 5000000000000000 : ℝ) ≤ (211920219227 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22199595737780619 / 5000000000000000 : ℝ) (574416976097
    / 500000000000 : ℝ) (211920219227 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell292_denomLower :
    (210657905247 / 2500000000 : ℝ) ≤ Real.exp (5542430979668619 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5542430979668619 / 1250000000000000 : ℝ) (574309743107 /
    500000000000 : ℝ) (210657905247 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell292_product_lower :
    (5656884104668619 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell292_leftExp
    (by norm_num : (0 : ℝ) ≤ (14405140081 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell292_product_upper :
    Real.pi * Real.exp (293 / 800 : ℝ) ≤ (22655845737780619 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell292_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell292_endpointLower :
    (12921801703 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 400 : ℝ) (293 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5656884104668619 / 1250000000000000 : ℝ) (Real.pi * Real.exp (73 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell292_product_lower
  have hD : Real.exp (Real.pi * Real.exp (293 / 800 : ℝ) - (73 / 800 : ℝ)) ≤
      (211920219227 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell292_denomUpper
    linarith [hpThetaJensenCell292_product_upper]
  have hi : (1 / (211920219227 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (293 / 800 : ℝ) - (73 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (211920219227 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (211920219227 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 800 : ℝ) - Real.pi * Real.exp (293 / 800 : ℝ)) := by
    rw [show (73 / 800 : ℝ) - Real.pi * Real.exp (293 / 800 : ℝ) =
      -(Real.pi * Real.exp (293 / 800 : ℝ) - (73 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 200 : ℝ)) := by
    have h := hpThetaJensenCell292_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (211920219227 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell292_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 400 : ℝ) (293 / 1600 : ℝ) ≤ (408568543 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (293 / 800 : ℝ)) (22655845737780619 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (293 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell292_product_upper
  have hD : (210657905247 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 200 : ℝ) - (293 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell292_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell292_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 200 : ℝ) - (293 / 3200 : ℝ)) ≤
      (1 / (210657905247 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (210657905247 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((293 / 3200 : ℝ) - Real.pi * Real.exp (73 / 200 : ℝ)) ≤
      (2 / (210657905247 / 2500000000 : ℝ) : ℝ) := by
    rw [show (293 / 3200 : ℝ) - Real.pi * Real.exp (73 / 200 : ℝ) =
      -(Real.pi * Real.exp (73 / 200 : ℝ) - (293 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22655845737780619 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22655845737780619 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell292_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 400 : ℝ) (293 / 1600 : ℝ)) :
    (12921801703 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (408568543 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell292_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell292_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell293_leftExp :
    (3605789441 / 2500000000 : ℝ) ≤ Real.exp (293 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (293 / 800 : ℝ) (202302212137 / 200000000000 : ℝ)
    (3605789441 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell293_rightExp :
    Real.exp (147 / 400 : ℝ) ≤ (7220598993 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (147 / 400 : ℝ) (1011550573609 / 1000000000000 : ℝ)
    (7220598993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell293_denomUpper :
    Real.exp (22226370752215849 / 5000000000000000 : ℝ) ≤ (852232386243 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22226370752215849 / 5000000000000000 : ℝ) (574513109283
    / 500000000000 : ℝ) (852232386243 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell293_denomLower :
    (423575009739 / 5000000000 : ℝ) ≤ Real.exp (1387278970191259 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1387278970191259 / 312500000000000 : ℝ) (1148811462447 /
    1000000000000 : ℝ) (423575009739 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell293_product_lower :
    (1415989907691259 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (293 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell293_leftExp
    (by norm_num : (0 : ℝ) ≤ (3605789441 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell293_product_upper :
    Real.pi * Real.exp (147 / 400 : ℝ) ≤ (22684183252215849 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell293_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell293_endpointLower :
    (12892942753 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (293 / 1600 : ℝ) (147 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1415989907691259 / 312500000000000 : ℝ) (Real.pi * Real.exp (293 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell293_product_lower
  have hD : Real.exp (Real.pi * Real.exp (147 / 400 : ℝ) - (293 / 3200 : ℝ)) ≤
      (852232386243 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell293_denomUpper
    linarith [hpThetaJensenCell293_product_upper]
  have hi : (1 / (852232386243 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (147 / 400 : ℝ) - (293 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (852232386243 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (852232386243 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((293 / 3200 : ℝ) - Real.pi * Real.exp (147 / 400 : ℝ)) := by
    rw [show (293 / 3200 : ℝ) - Real.pi * Real.exp (147 / 400 : ℝ) =
      -(Real.pi * Real.exp (147 / 400 : ℝ) - (293 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (293 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (293 / 800 : ℝ)) := by
    have h := hpThetaJensenCell293_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (852232386243 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell293_endpointUpper :
    hpThetaJensenKernelEndpointUpper (293 / 1600 : ℝ) (147 / 800 : ℝ) ≤ (6522535693 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (147 / 400 : ℝ)) (22684183252215849 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (147 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell293_product_upper
  have hD : (423575009739 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (293 / 800 : ℝ) - (147 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell293_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell293_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (293 / 800 : ℝ) - (147 / 1600 : ℝ)) ≤
      (1 / (423575009739 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (423575009739 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((147 / 1600 : ℝ) - Real.pi * Real.exp (293 / 800 : ℝ)) ≤
      (2 / (423575009739 / 5000000000 : ℝ) : ℝ) := by
    rw [show (147 / 1600 : ℝ) - Real.pi * Real.exp (293 / 800 : ℝ) =
      -(Real.pi * Real.exp (293 / 800 : ℝ) - (147 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22684183252215849 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (22684183252215849 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell293_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (293 / 1600 : ℝ) (147 / 800 : ℝ)) :
    (12892942753 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6522535693 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell293_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell293_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell294_leftExp :
    (2888239597 / 2000000000 : ℝ) ≤ Real.exp (147 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (147 / 400 : ℝ) (126443821701 / 125000000000 : ℝ)
    (2888239597 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell294_rightExp :
    Real.exp (59 / 160 : ℝ) ≤ (1445926077 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 160 : ℝ) (40463603523 / 40000000000 : ℝ)
    (1445926077 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell294_denomUpper :
    Real.exp (4450636242020661 / 1000000000000000 : ℝ) ≤ (85681440797 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4450636242020661 / 1000000000000000 : ℝ) (287304692923 /
    250000000000 : ℝ) (85681440797 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell294_denomLower :
    (13307791831 / 156250000 : ℝ) ≤ Real.exp (1111161926502303 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1111161926502303 / 250000000000000 : ℝ) (574501862501 /
    500000000000 : ℝ) (13307791831 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell294_product_lower :
    (1134208801502303 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (147 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell294_leftExp
    (by norm_num : (0 : ℝ) ≤ (2888239597 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell294_product_upper :
    Real.pi * Real.exp (59 / 160 : ℝ) ≤ (4542511242020661 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell294_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell294_endpointLower :
    (64320211 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (147 / 800 : ℝ) (59 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1134208801502303 / 250000000000000 : ℝ) (Real.pi * Real.exp (147 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell294_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 160 : ℝ) - (147 / 1600 : ℝ)) ≤
      (85681440797 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell294_denomUpper
    linarith [hpThetaJensenCell294_product_upper]
  have hi : (1 / (85681440797 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 160 : ℝ) - (147 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (85681440797 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (85681440797 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((147 / 1600 : ℝ) - Real.pi * Real.exp (59 / 160 : ℝ)) := by
    rw [show (147 / 1600 : ℝ) - Real.pi * Real.exp (59 / 160 : ℝ) =
      -(Real.pi * Real.exp (59 / 160 : ℝ) - (147 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (147 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (147 / 400 : ℝ)) := by
    have h := hpThetaJensenCell294_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (85681440797 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell294_endpointUpper :
    hpThetaJensenKernelEndpointUpper (147 / 800 : ℝ) (59 / 320 : ℝ) ≤ (2603181419 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 160 : ℝ)) (4542511242020661 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell294_product_upper
  have hD : (13307791831 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (147 / 400 : ℝ) - (59 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell294_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell294_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (147 / 400 : ℝ) - (59 / 640 : ℝ)) ≤
      (1 / (13307791831 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13307791831 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 640 : ℝ) - Real.pi * Real.exp (147 / 400 : ℝ)) ≤
      (2 / (13307791831 / 156250000 : ℝ) : ℝ) := by
    rw [show (59 / 640 : ℝ) - Real.pi * Real.exp (147 / 400 : ℝ) =
      -(Real.pi * Real.exp (147 / 400 : ℝ) - (59 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4542511242020661 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4542511242020661 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell294_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (147 / 800 : ℝ) (59 / 320 : ℝ)) :
    (64320211 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2603181419 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell294_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell294_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell295_leftExp :
    (14459260769 / 10000000000 : ℝ) ≤ Real.exp (59 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 160 : ℝ) (505795044037 / 500000000000 : ℝ)
    (14459260769 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell295_rightExp :
    Real.exp (37 / 100 : ℝ) ≤ (3619336537 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 100 : ℝ) (202325920817 / 200000000000 : ℝ)
    (3619336537 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell295_denomUpper :
    Real.exp (11140013579283441 / 2500000000000000 : ℝ) ≤ (43071358971 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11140013579283441 / 2500000000000000 : ℝ) (229882322409
    / 200000000000 : ℝ) (43071358971 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell295_denomLower :
    (856277827889 / 10000000000 : ℝ) ≤ Real.exp (5562512244725531 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5562512244725531 / 1250000000000000 : ℝ) (574598137147 /
    500000000000 : ℝ) (856277827889 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell295_product_lower :
    (5678137244725531 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell295_leftExp
    (by norm_num : (0 : ℝ) ≤ (14459260769 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell295_product_upper :
    Real.pi * Real.exp (37 / 100 : ℝ) ≤ (11370482329283441 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell295_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell295_endpointLower :
    (6417550261 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 320 : ℝ) (37 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5678137244725531 / 1250000000000000 : ℝ) (Real.pi * Real.exp (59 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell295_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 100 : ℝ) - (59 / 640 : ℝ)) ≤
      (43071358971 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell295_denomUpper
    linarith [hpThetaJensenCell295_product_upper]
  have hi : (1 / (43071358971 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 100 : ℝ) - (59 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (43071358971 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (43071358971 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 640 : ℝ) - Real.pi * Real.exp (37 / 100 : ℝ)) := by
    rw [show (59 / 640 : ℝ) - Real.pi * Real.exp (37 / 100 : ℝ) =
      -(Real.pi * Real.exp (37 / 100 : ℝ) - (59 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 160 : ℝ)) := by
    have h := hpThetaJensenCell295_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (43071358971 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell295_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 320 : ℝ) (37 / 200 : ℝ) ≤ (6493350509 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 100 : ℝ)) (11370482329283441 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell295_product_upper
  have hD : (856277827889 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 160 : ℝ) - (37 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell295_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell295_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 160 : ℝ) - (37 / 400 : ℝ)) ≤
      (1 / (856277827889 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (856277827889 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 400 : ℝ) - Real.pi * Real.exp (59 / 160 : ℝ)) ≤
      (2 / (856277827889 / 10000000000 : ℝ) : ℝ) := by
    rw [show (37 / 400 : ℝ) - Real.pi * Real.exp (59 / 160 : ℝ) =
      -(Real.pi * Real.exp (59 / 160 : ℝ) - (37 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11370482329283441 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (11370482329283441 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell295_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 320 : ℝ) (37 / 200 : ℝ)) :
    (6417550261 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6493350509 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell295_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell295_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell296_leftExp :
    (7238673073 / 5000000000 : ℝ) ≤ Real.exp (37 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 100 : ℝ) (252907401021 / 250000000000 : ℝ)
    (7238673073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell296_rightExp :
    Real.exp (297 / 800 : ℝ) ≤ (2899090829 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (297 / 800 : ℝ) (505834560819 / 500000000000 : ℝ)
    (2899090829 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell296_denomUpper :
    Real.exp (8922763454750597 / 2000000000000000 : ℝ) ≤ (866070938531 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8922763454750597 / 2000000000000000 : ℝ) (574802370019 /
    500000000000 : ℝ) (866070938531 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell296_denomLower :
    (860887708723 / 10000000000 : ℝ) ≤ Real.exp (2784611864594027 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2784611864594027 / 625000000000000 : ℝ) (574694555397 /
    500000000000 : ℝ) (860887708723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell296_product_lower :
    (2842619677094027 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell296_leftExp
    (by norm_num : (0 : ℝ) ≤ (7238673073 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell296_product_upper :
    Real.pi * Real.exp (297 / 800 : ℝ) ≤ (9107763454750597 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell296_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell296_endpointLower :
    (12806118231 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 200 : ℝ) (297 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2842619677094027 / 625000000000000 : ℝ) (Real.pi * Real.exp (37 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell296_product_lower
  have hD : Real.exp (Real.pi * Real.exp (297 / 800 : ℝ) - (37 / 400 : ℝ)) ≤
      (866070938531 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell296_denomUpper
    linarith [hpThetaJensenCell296_product_upper]
  have hi : (1 / (866070938531 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (297 / 800 : ℝ) - (37 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (866070938531 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (866070938531 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 400 : ℝ) - Real.pi * Real.exp (297 / 800 : ℝ)) := by
    rw [show (37 / 400 : ℝ) - Real.pi * Real.exp (297 / 800 : ℝ) =
      -(Real.pi * Real.exp (297 / 800 : ℝ) - (37 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 100 : ℝ)) := by
    have h := hpThetaJensenCell296_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (866070938531 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell296_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 200 : ℝ) (297 / 1600 : ℝ) ≤ (3239363409 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (297 / 800 : ℝ)) (9107763454750597 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (297 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell296_product_upper
  have hD : (860887708723 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 100 : ℝ) - (297 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell296_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell296_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 100 : ℝ) - (297 / 3200 : ℝ)) ≤
      (1 / (860887708723 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (860887708723 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((297 / 3200 : ℝ) - Real.pi * Real.exp (37 / 100 : ℝ)) ≤
      (2 / (860887708723 / 10000000000 : ℝ) : ℝ) := by
    rw [show (297 / 3200 : ℝ) - Real.pi * Real.exp (37 / 100 : ℝ) =
      -(Real.pi * Real.exp (37 / 100 : ℝ) - (297 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9107763454750597 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (9107763454750597 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell296_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 200 : ℝ) (297 / 1600 : ℝ)) :
    (12806118231 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3239363409 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell296_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell296_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell297_leftExp :
    (226491471 / 156250000 : ℝ) ≤ Real.exp (297 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (297 / 800 : ℝ) (1011669121637 / 1000000000000 : ℝ)
    (226491471 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell297_rightExp :
    Real.exp (149 / 400 : ℝ) ≤ (1814198099 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (149 / 400 : ℝ) (202341728147 / 200000000000 : ℝ)
    (1814198099 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell297_denomUpper :
    Real.exp (5583456423431707 / 1250000000000000 : ℝ) ≤ (870745927077 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5583456423431707 / 1250000000000000 : ℝ) (574899078079 /
    500000000000 : ℝ) (870745927077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell297_denomLower :
    (86552855841 / 1000000000 : ℝ) ≤ Real.exp (87124126513979 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87124126513979 / 19531250000000 : ℝ) (574791117477 /
    500000000000 : ℝ) (86552855841 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell297_product_lower :
    (88942974170229 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (297 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell297_leftExp
    (by norm_num : (0 : ℝ) ≤ (226491471 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell297_product_upper :
    Real.pi * Real.exp (149 / 400 : ℝ) ≤ (5699472048431707 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell297_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell297_endpointLower :
    (2555419161 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (297 / 1600 : ℝ) (149 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (88942974170229 / 19531250000000 : ℝ) (Real.pi * Real.exp (297 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell297_product_lower
  have hD : Real.exp (Real.pi * Real.exp (149 / 400 : ℝ) - (297 / 3200 : ℝ)) ≤
      (870745927077 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell297_denomUpper
    linarith [hpThetaJensenCell297_product_upper]
  have hi : (1 / (870745927077 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (149 / 400 : ℝ) - (297 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (870745927077 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (870745927077 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((297 / 3200 : ℝ) - Real.pi * Real.exp (149 / 400 : ℝ)) := by
    rw [show (297 / 3200 : ℝ) - Real.pi * Real.exp (149 / 400 : ℝ) =
      -(Real.pi * Real.exp (149 / 400 : ℝ) - (297 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (297 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (297 / 800 : ℝ)) := by
    have h := hpThetaJensenCell297_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (870745927077 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell297_endpointUpper :
    hpThetaJensenKernelEndpointUpper (297 / 1600 : ℝ) (149 / 800 : ℝ) ≤ (3232041363 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (149 / 400 : ℝ)) (5699472048431707 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (149 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell297_product_upper
  have hD : (86552855841 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (297 / 800 : ℝ) - (149 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell297_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell297_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (297 / 800 : ℝ) - (149 / 1600 : ℝ)) ≤
      (1 / (86552855841 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (86552855841 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((149 / 1600 : ℝ) - Real.pi * Real.exp (297 / 800 : ℝ)) ≤
      (2 / (86552855841 / 1000000000 : ℝ) : ℝ) := by
    rw [show (149 / 1600 : ℝ) - Real.pi * Real.exp (297 / 800 : ℝ) =
      -(Real.pi * Real.exp (297 / 800 : ℝ) - (149 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5699472048431707 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (5699472048431707 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell297_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (297 / 1600 : ℝ) (149 / 800 : ℝ)) :
    (2555419161 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3232041363 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell297_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell297_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell298_leftExp :
    (14513584791 / 10000000000 : ℝ) ≤ Real.exp (149 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (149 / 400 : ℝ) (505854320367 / 500000000000 : ℝ)
    (14513584791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell298_rightExp :
    Real.exp (299 / 800 : ℝ) ≤ (3632934529 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (299 / 800 : ℝ) (8093985291 / 8000000000 : ℝ)
    (3632934529 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell298_denomUpper :
    Real.exp (11180389185764697 / 2500000000000000 : ℝ) ≤ (875452387737 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11180389185764697 / 2500000000000000 : ℝ) (1149991860843
    / 1000000000000 : ℝ) (875452387737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell298_denomLower :
    (435100308819 / 5000000000 : ℝ) ≤ Real.exp (5582673358840909 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5582673358840909 / 1250000000000000 : ℝ) (574887823611 /
    500000000000 : ℝ) (435100308819 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell298_product_lower :
    (5699470233840909 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (149 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell298_leftExp
    (by norm_num : (0 : ℝ) ≤ (14513584791 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell298_product_upper :
    Real.pi * Real.exp (299 / 800 : ℝ) ≤ (11413201685764697 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell298_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell298_endpointLower :
    (12748033743 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (149 / 800 : ℝ) (299 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5699470233840909 / 1250000000000000 : ℝ) (Real.pi * Real.exp (149 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell298_product_lower
  have hD : Real.exp (Real.pi * Real.exp (299 / 800 : ℝ) - (149 / 1600 : ℝ)) ≤
      (875452387737 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell298_denomUpper
    linarith [hpThetaJensenCell298_product_upper]
  have hi : (1 / (875452387737 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (299 / 800 : ℝ) - (149 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (875452387737 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (875452387737 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((149 / 1600 : ℝ) - Real.pi * Real.exp (299 / 800 : ℝ)) := by
    rw [show (149 / 1600 : ℝ) - Real.pi * Real.exp (299 / 800 : ℝ) =
      -(Real.pi * Real.exp (299 / 800 : ℝ) - (149 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (149 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (149 / 400 : ℝ)) := by
    have h := hpThetaJensenCell298_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (875452387737 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell298_endpointUpper :
    hpThetaJensenKernelEndpointUpper (149 / 800 : ℝ) (299 / 1600 : ℝ) ≤ (12898836963 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (299 / 800 : ℝ)) (11413201685764697 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (299 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell298_product_upper
  have hD : (435100308819 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (149 / 400 : ℝ) - (299 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell298_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell298_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (149 / 400 : ℝ) - (299 / 3200 : ℝ)) ≤
      (1 / (435100308819 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (435100308819 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((299 / 3200 : ℝ) - Real.pi * Real.exp (149 / 400 : ℝ)) ≤
      (2 / (435100308819 / 5000000000 : ℝ) : ℝ) := by
    rw [show (299 / 3200 : ℝ) - Real.pi * Real.exp (149 / 400 : ℝ) =
      -(Real.pi * Real.exp (149 / 400 : ℝ) - (299 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11413201685764697 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (11413201685764697 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell298_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (149 / 800 : ℝ) (299 / 1600 : ℝ)) :
    (12748033743 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12898836963 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell298_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell298_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell299_leftExp :
    (2906347623 / 2000000000 : ℝ) ≤ Real.exp (299 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (299 / 800 : ℝ) (505874080687 / 500000000000 : ℝ)
    (2906347623 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell299_rightExp :
    Real.exp (3 / 8 : ℝ) ≤ (14549914147 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 8 : ℝ) (25294692089 / 25000000000 : ℝ)
    (14549914147 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell299_denomUpper :
    Real.exp (44775533434816171 / 10000000000000000 : ℝ) ≤ (176038113233 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44775533434816171 / 10000000000000000 : ℝ)
    (1150185854567 / 1000000000000 : ℝ) (176038113233 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell299_denomLower :
    (874904129269 / 10000000000 : ℝ) ≤ Real.exp (1117882305204477 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1117882305204477 / 250000000000000 : ℝ) (22999386961 /
    20000000000 : ℝ) (874904129269 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell299_product_lower :
    (1141319805204477 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (299 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell299_leftExp
    (by norm_num : (0 : ℝ) ≤ (2906347623 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell299_product_upper :
    Real.pi * Real.exp (3 / 8 : ℝ) ≤ (45709908434816171 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell299_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell299_endpointLower :
    (12718932531 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (299 / 1600 : ℝ) (3 / 16 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1141319805204477 / 250000000000000 : ℝ) (Real.pi * Real.exp (299 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell299_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 8 : ℝ) - (299 / 3200 : ℝ)) ≤
      (176038113233 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell299_denomUpper
    linarith [hpThetaJensenCell299_product_upper]
  have hi : (1 / (176038113233 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 8 : ℝ) - (299 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (176038113233 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (176038113233 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((299 / 3200 : ℝ) - Real.pi * Real.exp (3 / 8 : ℝ)) := by
    rw [show (299 / 3200 : ℝ) - Real.pi * Real.exp (3 / 8 : ℝ) =
      -(Real.pi * Real.exp (3 / 8 : ℝ) - (299 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (299 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (299 / 800 : ℝ)) := by
    have h := hpThetaJensenCell299_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (176038113233 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell299_endpointUpper :
    hpThetaJensenKernelEndpointUpper (299 / 1600 : ℝ) (3 / 16 : ℝ) ≤ (1286946867 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 8 : ℝ)) (45709908434816171 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 16 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell299_product_upper
  have hD : (874904129269 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (299 / 800 : ℝ) - (3 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell299_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell299_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (299 / 800 : ℝ) - (3 / 32 : ℝ)) ≤
      (1 / (874904129269 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (874904129269 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 32 : ℝ) - Real.pi * Real.exp (299 / 800 : ℝ)) ≤
      (2 / (874904129269 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 32 : ℝ) - Real.pi * Real.exp (299 / 800 : ℝ) =
      -(Real.pi * Real.exp (299 / 800 : ℝ) - (3 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45709908434816171 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (45709908434816171 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell299_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (299 / 1600 : ℝ) (3 / 16 : ℝ)) :
    (12718932531 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1286946867 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell299_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell299_endpointUpper

def hpThetaJensenCellsBatch014Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (829042797 / 625000000 : ℝ)
  | 1 => (13236363423 / 10000000000 : ℝ)
  | 2 => (412749831 / 312500000 : ℝ)
  | 3 => (3294894689 / 2500000000 : ℝ)
  | 4 => (13151116399 / 10000000000 : ℝ)
  | 5 => (3280652003 / 2500000000 : ℝ)
  | 6 => (6547027043 / 5000000000 : ℝ)
  | 7 => (1633181889 / 1250000000 : ℝ)
  | 8 => (13036811579 / 10000000000 : ℝ)
  | 9 => (650406199 / 500000000 : ℝ)
  | 10 => (6489696403 / 5000000000 : ℝ)
  | 11 => (12950618553 / 10000000000 : ℝ)
  | 12 => (12921801703 / 10000000000 : ℝ)
  | 13 => (12892942753 / 10000000000 : ℝ)
  | 14 => (64320211 / 50000000 : ℝ)
  | 15 => (6417550261 / 5000000000 : ℝ)
  | 16 => (12806118231 / 10000000000 : ℝ)
  | 17 => (2555419161 / 2000000000 : ℝ)
  | 18 => (12748033743 / 10000000000 : ℝ)
  | 19 => (12718932531 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch014Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6710089071 / 5000000000 : ℝ)
  | 1 => (6695801143 / 5000000000 : ℝ)
  | 2 => (13362978203 / 10000000000 : ℝ)
  | 3 => (6667153191 / 5000000000 : ℝ)
  | 4 => (13305587317 / 10000000000 : ℝ)
  | 5 => (12965646 / 9765625 : ℝ)
  | 6 => (2649601887 / 2000000000 : ℝ)
  | 7 => (13219151607 / 10000000000 : ℝ)
  | 8 => (206097633 / 156250000 : ℝ)
  | 9 => (13161300647 / 10000000000 : ℝ)
  | 10 => (6566154253 / 5000000000 : ℝ)
  | 11 => (6551636291 / 5000000000 : ℝ)
  | 12 => (408568543 / 312500000 : ℝ)
  | 13 => (6522535693 / 5000000000 : ℝ)
  | 14 => (2603181419 / 2000000000 : ℝ)
  | 15 => (6493350509 / 5000000000 : ℝ)
  | 16 => (3239363409 / 2500000000 : ℝ)
  | 17 => (3232041363 / 2500000000 : ℝ)
  | 18 => (12898836963 / 10000000000 : ℝ)
  | 19 => (1286946867 / 1000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch014_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch014Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch014Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell280_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell281_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell282_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell283_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell284_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell285_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell286_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell287_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell288_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell289_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell290_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell291_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell292_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell293_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell294_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell295_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell296_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell297_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell298_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell299_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper] at h ⊢
    exact h

end HodgeProofHP
