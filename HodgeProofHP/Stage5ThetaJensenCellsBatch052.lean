import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1040_leftExp :
    (1467718667 / 400000000 : ℝ) ≤ Real.exp (13 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 10 : ℝ) (1041461484251 / 1000000000000 : ℝ)
    (1467718667 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1040_rightExp :
    Real.exp (1041 / 800 : ℝ) ≤ (9184715391 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1041 / 800 : ℝ) (32546942723 / 31250000000 : ℝ)
    (9184715391 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1040_denomUpper :
    Real.exp (28042137579357863 / 2500000000000000 : ℝ) ≤ (2974940170103 / 40000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28042137579357863 / 2500000000000000 : ℝ) (141981519637
    / 100000000000 : ℝ) (2974940170103 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1040_denomLower :
    (366428417945689 / 5000000000 : ℝ) ≤ Real.exp (560106027812233 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (560106027812233 / 50000000000000 : ℝ) (1419161589601 /
    1000000000000 : ℝ) (366428417945689 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1040_product_lower :
    (576371652812233 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1040_leftExp
    (by norm_num : (0 : ℝ) ≤ (1467718667 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1040_product_upper :
    Real.pi * Real.exp (1041 / 800 : ℝ) ≤ (28854637579357863 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1040_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1040_endpointLower :
    (124335207 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 20 : ℝ) (1041 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (576371652812233 / 50000000000000 : ℝ) (Real.pi * Real.exp (13 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell1040_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1041 / 800 : ℝ) - (13 / 40 : ℝ)) ≤
      (2974940170103 / 40000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1040_denomUpper
    linarith [hpThetaJensenCell1040_product_upper]
  have hi : (1 / (2974940170103 / 40000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1041 / 800 : ℝ) - (13 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2974940170103 / 40000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2974940170103 / 40000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 40 : ℝ) - Real.pi * Real.exp (1041 / 800 : ℝ)) := by
    rw [show (13 / 40 : ℝ) - Real.pi * Real.exp (1041 / 800 : ℝ) =
      -(Real.pi * Real.exp (1041 / 800 : ℝ) - (13 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 10 : ℝ)) := by
    have h := hpThetaJensenCell1040_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2974940170103 / 40000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1040_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 20 : ℝ) (1041 / 1600 : ℝ) ≤ (7928347 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1041 / 800 : ℝ)) (28854637579357863 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1041 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1040_product_upper
  have hD : (366428417945689 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 10 : ℝ) - (1041 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1040_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1040_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 10 : ℝ) - (1041 / 3200 : ℝ)) ≤
      (1 / (366428417945689 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (366428417945689 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1041 / 3200 : ℝ) - Real.pi * Real.exp (13 / 10 : ℝ)) ≤
      (2 / (366428417945689 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1041 / 3200 : ℝ) - Real.pi * Real.exp (13 / 10 : ℝ) =
      -(Real.pi * Real.exp (13 / 10 : ℝ) - (1041 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28854637579357863 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (28854637579357863 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1040_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 20 : ℝ) (1041 / 1600 : ℝ)) :
    (124335207 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7928347 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1040_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1040_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1041_leftExp :
    (36738861561 / 10000000000 : ℝ) ≤ Real.exp (1041 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1041 / 800 : ℝ) (208300433427 / 200000000000 : ℝ)
    (36738861561 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1041_rightExp :
    Real.exp (521 / 400 : ℝ) ≤ (7356962771 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (521 / 400 : ℝ) (1041542851609 / 1000000000000 : ℝ)
    (7356962771 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1041_denomUpper :
    Real.exp (22461957742634203 / 2000000000000000 : ℝ) ≤ (15086279372421 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22461957742634203 / 2000000000000000 : ℝ) (2840883997 /
    2000000000 : ℝ) (15086279372421 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1041_denomLower :
    (74326762194927 / 1000000000 : ℝ) ≤ Real.exp (14020282946143139 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14020282946143139 / 1250000000000000 : ℝ) (354946825707
    / 250000000000 : ℝ) (74326762194927 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1041_product_lower :
    (14427314196143139 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1041 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1041_leftExp
    (by norm_num : (0 : ℝ) ≤ (36738861561 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1041_product_upper :
    Real.pi * Real.exp (521 / 400 : ℝ) ≤ (23112582742634203 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1041_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1041_endpointLower :
    (122921287 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1041 / 1600 : ℝ) (521 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14427314196143139 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1041 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1041_product_lower
  have hD : Real.exp (Real.pi * Real.exp (521 / 400 : ℝ) - (1041 / 3200 : ℝ)) ≤
      (15086279372421 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1041_denomUpper
    linarith [hpThetaJensenCell1041_product_upper]
  have hi : (1 / (15086279372421 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (521 / 400 : ℝ) - (1041 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15086279372421 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15086279372421 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1041 / 3200 : ℝ) - Real.pi * Real.exp (521 / 400 : ℝ)) := by
    rw [show (1041 / 3200 : ℝ) - Real.pi * Real.exp (521 / 400 : ℝ) =
      -(Real.pi * Real.exp (521 / 400 : ℝ) - (1041 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1041 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1041 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1041_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15086279372421 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1041_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1041 / 1600 : ℝ) (521 / 800 : ℝ) ≤ (125413223 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (521 / 400 : ℝ)) (23112582742634203 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (521 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1041_product_upper
  have hD : (74326762194927 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1041 / 800 : ℝ) - (521 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1041_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1041_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1041 / 800 : ℝ) - (521 / 1600 : ℝ)) ≤
      (1 / (74326762194927 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (74326762194927 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((521 / 1600 : ℝ) - Real.pi * Real.exp (1041 / 800 : ℝ)) ≤
      (2 / (74326762194927 / 1000000000 : ℝ) : ℝ) := by
    rw [show (521 / 1600 : ℝ) - Real.pi * Real.exp (1041 / 800 : ℝ) =
      -(Real.pi * Real.exp (1041 / 800 : ℝ) - (521 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23112582742634203 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (23112582742634203 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1041_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1041 / 1600 : ℝ) (521 / 800 : ℝ)) :
    (122921287 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (125413223 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1041_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1041_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1042_leftExp :
    (36784813853 / 10000000000 : ℝ) ≤ Real.exp (521 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (521 / 400 : ℝ) (130192856451 / 125000000000 : ℝ)
    (36784813853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1042_rightExp :
    Real.exp (1043 / 800 : ℝ) ≤ (36830823623 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1043 / 800 : ℝ) (130197942209 / 125000000000 : ℝ)
    (36830823623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1042_denomUpper :
    Real.exp (112451207678251439 / 10000000000000000 : ℝ) ≤ (382528592191149 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (112451207678251439 / 10000000000000000 : ℝ)
    (1421069879223 / 1000000000000 : ℝ) (382528592191149 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1042_denomLower :
    (753839896204627 / 10000000000 : ℝ) ≤ Real.exp (14037937740259247 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14037937740259247 / 1250000000000000 : ℝ) (710207046227
    / 500000000000 : ℝ) (753839896204627 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1042_product_lower :
    (14445359615259247 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (521 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1042_leftExp
    (by norm_num : (0 : ℝ) ≤ (36784813853 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1042_product_upper :
    Real.pi * Real.exp (1043 / 800 : ℝ) ≤ (115707457678251439 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1042_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1042_endpointLower :
    (6076061 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (521 / 800 : ℝ) (1043 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14445359615259247 / 1250000000000000 : ℝ) (Real.pi * Real.exp (521 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1042_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1043 / 800 : ℝ) - (521 / 1600 : ℝ)) ≤
      (382528592191149 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1042_denomUpper
    linarith [hpThetaJensenCell1042_product_upper]
  have hi : (1 / (382528592191149 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1043 / 800 : ℝ) - (521 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (382528592191149 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (382528592191149 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((521 / 1600 : ℝ) - Real.pi * Real.exp (1043 / 800 : ℝ)) := by
    rw [show (521 / 1600 : ℝ) - Real.pi * Real.exp (1043 / 800 : ℝ) =
      -(Real.pi * Real.exp (1043 / 800 : ℝ) - (521 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (521 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (521 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1042_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (382528592191149 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1042_endpointUpper :
    hpThetaJensenKernelEndpointUpper (521 / 800 : ℝ) (1043 / 1600 : ℝ) ≤ (123986979 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1043 / 800 : ℝ)) (115707457678251439 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1043 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1042_product_upper
  have hD : (753839896204627 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (521 / 400 : ℝ) - (1043 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1042_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1042_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (521 / 400 : ℝ) - (1043 / 3200 : ℝ)) ≤
      (1 / (753839896204627 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (753839896204627 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1043 / 3200 : ℝ) - Real.pi * Real.exp (521 / 400 : ℝ)) ≤
      (2 / (753839896204627 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1043 / 3200 : ℝ) - Real.pi * Real.exp (521 / 400 : ℝ) =
      -(Real.pi * Real.exp (521 / 400 : ℝ) - (1043 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (115707457678251439 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (115707457678251439 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1042_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (521 / 800 : ℝ) (1043 / 1600 : ℝ)) :
    (6076061 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (123986979 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1042_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1042_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1043_leftExp :
    (36830823621 / 10000000000 : ℝ) ≤ Real.exp (1043 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1043 / 800 : ℝ) (1041583537671 / 1000000000000 : ℝ)
    (36830823621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1043_rightExp :
    Real.exp (261 / 200 : ℝ) ≤ (18438445469 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (261 / 200 : ℝ) (1041624225323 / 1000000000000 : ℝ)
    (18438445469 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1043_denomUpper :
    Real.exp (56296403716292117 / 5000000000000000 : ℝ) ≤ (387983718732997 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56296403716292117 / 5000000000000000 : ℝ) (14216988407 /
    10000000000 : ℝ) (387983718732997 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1043_denomLower :
    (382288178264821 / 5000000000 : ℝ) ≤ Real.exp (14055615105143079 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14055615105143079 / 1250000000000000 : ℝ) (1421041960637
    / 1000000000000 : ℝ) (382288178264821 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1043_product_lower :
    (14463427605143079 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1043 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1043_leftExp
    (by norm_num : (0 : ℝ) ≤ (36830823621 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1043_product_upper :
    Real.pi * Real.exp (261 / 200 : ℝ) ≤ (57926091216292117 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1043_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1043_endpointLower :
    (7508431 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1043 / 1600 : ℝ) (261 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14463427605143079 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1043 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1043_product_lower
  have hD : Real.exp (Real.pi * Real.exp (261 / 200 : ℝ) - (1043 / 3200 : ℝ)) ≤
      (387983718732997 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1043_denomUpper
    linarith [hpThetaJensenCell1043_product_upper]
  have hi : (1 / (387983718732997 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (261 / 200 : ℝ) - (1043 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (387983718732997 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (387983718732997 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1043 / 3200 : ℝ) - Real.pi * Real.exp (261 / 200 : ℝ)) := by
    rw [show (1043 / 3200 : ℝ) - Real.pi * Real.exp (261 / 200 : ℝ) =
      -(Real.pi * Real.exp (261 / 200 : ℝ) - (1043 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1043 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1043 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1043_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (387983718732997 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1043_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1043 / 1600 : ℝ) (261 / 400 : ℝ) ≤ (30643677 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (261 / 200 : ℝ)) (57926091216292117 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (261 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1043_product_upper
  have hD : (382288178264821 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1043 / 800 : ℝ) - (261 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1043_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1043_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1043 / 800 : ℝ) - (261 / 800 : ℝ)) ≤
      (1 / (382288178264821 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (382288178264821 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((261 / 800 : ℝ) - Real.pi * Real.exp (1043 / 800 : ℝ)) ≤
      (2 / (382288178264821 / 5000000000 : ℝ) : ℝ) := by
    rw [show (261 / 800 : ℝ) - Real.pi * Real.exp (1043 / 800 : ℝ) =
      -(Real.pi * Real.exp (1043 / 800 : ℝ) - (261 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57926091216292117 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (57926091216292117 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1043_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1043 / 1600 : ℝ) (261 / 400 : ℝ)) :
    (7508431 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (30643677 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1043_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1043_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1044_leftExp :
    (4609611367 / 1250000000 : ℝ) ≤ Real.exp (261 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (261 / 200 : ℝ) (520812112661 / 500000000000 : ℝ)
    (4609611367 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1044_rightExp :
    Real.exp (209 / 160 : ℝ) ≤ (18461507937 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (209 / 160 : ℝ) (260416228641 / 250000000000 : ℝ)
    (18461507937 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1044_denomUpper :
    Real.exp (56367294104323641 / 5000000000000000 : ℝ) ≤ (31481901023617 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56367294104323641 / 5000000000000000 : ℝ) (355582221289
    / 250000000000 : ℝ) (31481901023617 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1044_denomLower :
    (775479749103959 / 10000000000 : ℝ) ≤ Real.exp (1759164383584533 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1759164383584533 / 156250000000000 : ℝ) (1421670909553 /
    1000000000000 : ℝ) (775479749103959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1044_product_lower :
    (1810189774209533 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (261 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1044_leftExp
    (by norm_num : (0 : ℝ) ≤ (4609611367 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1044_product_upper :
    Real.pi * Real.exp (209 / 160 : ℝ) ≤ (57998544104323641 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1044_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1044_endpointLower :
    (29690551 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (261 / 400 : ℝ) (209 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1810189774209533 / 156250000000000 : ℝ) (Real.pi * Real.exp (261 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1044_product_lower
  have hD : Real.exp (Real.pi * Real.exp (209 / 160 : ℝ) - (261 / 800 : ℝ)) ≤
      (31481901023617 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1044_denomUpper
    linarith [hpThetaJensenCell1044_product_upper]
  have hi : (1 / (31481901023617 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (209 / 160 : ℝ) - (261 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31481901023617 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31481901023617 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((261 / 800 : ℝ) - Real.pi * Real.exp (209 / 160 : ℝ)) := by
    rw [show (261 / 800 : ℝ) - Real.pi * Real.exp (209 / 160 : ℝ) =
      -(Real.pi * Real.exp (209 / 160 : ℝ) - (261 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (261 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (261 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1044_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31481901023617 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1044_endpointUpper :
    hpThetaJensenKernelEndpointUpper (261 / 400 : ℝ) (209 / 320 : ℝ) ≤ (121176301 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (209 / 160 : ℝ)) (57998544104323641 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (209 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1044_product_upper
  have hD : (775479749103959 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (261 / 200 : ℝ) - (209 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1044_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1044_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (261 / 200 : ℝ) - (209 / 640 : ℝ)) ≤
      (1 / (775479749103959 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (775479749103959 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((209 / 640 : ℝ) - Real.pi * Real.exp (261 / 200 : ℝ)) ≤
      (2 / (775479749103959 / 10000000000 : ℝ) : ℝ) := by
    rw [show (209 / 640 : ℝ) - Real.pi * Real.exp (261 / 200 : ℝ) =
      -(Real.pi * Real.exp (261 / 200 : ℝ) - (209 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57998544104323641 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (57998544104323641 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1044_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (261 / 400 : ℝ) (209 / 320 : ℝ)) :
    (29690551 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (121176301 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1044_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1044_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1045_leftExp :
    (36923015871 / 10000000000 : ℝ) ≤ Real.exp (209 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (209 / 160 : ℝ) (1041664914563 / 1000000000000 : ℝ)
    (36923015871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1045_rightExp :
    Real.exp (523 / 400 : ℝ) ≤ (18484599251 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (523 / 400 : ℝ) (208341121079 / 200000000000 : ℝ)
    (18484599251 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1045_denomUpper :
    Real.exp (56438275114746843 / 5000000000000000 : ℝ) ≤ (399150147815459 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56438275114746843 / 5000000000000000 : ℝ) (711480007387
    / 500000000000 : ℝ) (399150147815459 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1045_denomLower :
    (786552869620841 / 10000000000 : ℝ) ≤ Real.exp (14091037659525829 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14091037659525829 / 1250000000000000 : ℝ) (355575235353
    / 250000000000 : ℝ) (786552869620841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1045_product_lower :
    (14499631409525829 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (209 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1045_leftExp
    (by norm_num : (0 : ℝ) ≤ (36923015871 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1045_product_upper :
    Real.pi * Real.exp (523 / 400 : ℝ) ≤ (58071087614746843 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1045_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1045_endpointLower :
    (117403039 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (209 / 320 : ℝ) (523 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14499631409525829 / 1250000000000000 : ℝ) (Real.pi * Real.exp (209 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1045_product_lower
  have hD : Real.exp (Real.pi * Real.exp (523 / 400 : ℝ) - (209 / 640 : ℝ)) ≤
      (399150147815459 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1045_denomUpper
    linarith [hpThetaJensenCell1045_product_upper]
  have hi : (1 / (399150147815459 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (523 / 400 : ℝ) - (209 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (399150147815459 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (399150147815459 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((209 / 640 : ℝ) - Real.pi * Real.exp (523 / 400 : ℝ)) := by
    rw [show (209 / 640 : ℝ) - Real.pi * Real.exp (523 / 400 : ℝ) =
      -(Real.pi * Real.exp (523 / 400 : ℝ) - (209 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (209 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (209 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1045_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (399150147815459 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1045_endpointUpper :
    hpThetaJensenKernelEndpointUpper (209 / 320 : ℝ) (523 / 800 : ℝ) ≤ (119791647 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (523 / 400 : ℝ)) (58071087614746843 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (523 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1045_product_upper
  have hD : (786552869620841 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (209 / 160 : ℝ) - (523 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1045_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1045_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (209 / 160 : ℝ) - (523 / 1600 : ℝ)) ≤
      (1 / (786552869620841 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (786552869620841 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((523 / 1600 : ℝ) - Real.pi * Real.exp (209 / 160 : ℝ)) ≤
      (2 / (786552869620841 / 10000000000 : ℝ) : ℝ) := by
    rw [show (523 / 1600 : ℝ) - Real.pi * Real.exp (209 / 160 : ℝ) =
      -(Real.pi * Real.exp (209 / 160 : ℝ) - (523 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58071087614746843 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (58071087614746843 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1045_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (209 / 320 : ℝ) (523 / 800 : ℝ)) :
    (117403039 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (119791647 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1045_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1045_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1046_leftExp :
    (73938397 / 20000000 : ℝ) ≤ Real.exp (523 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (523 / 400 : ℝ) (520852802697 / 500000000000 : ℝ)
    (73938397 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1046_rightExp :
    Real.exp (1047 / 800 : ℝ) ≤ (7403087779 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1047 / 800 : ℝ) (208349259563 / 200000000000 : ℝ)
    (7403087779 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1046_denomUpper :
    Real.exp (22603738744891947 / 2000000000000000 : ℝ) ≤ (404864322945557 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22603738744891947 / 2000000000000000 : ℝ) (1423592231771
    / 1000000000000 : ℝ) (404864322945557 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1046_denomLower :
    (398899281953821 / 5000000000 : ℝ) ≤ Real.exp (28217565813503 / 2500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (28217565813503 / 2500000000000 : ℝ) (1422932058439 /
    1000000000000 : ℝ) (398899281953821 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1046_product_lower :
    (29035534563503 / 2500000000000 : ℝ) ≤ Real.pi * Real.exp (523 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1046_leftExp
    (by norm_num : (0 : ℝ) ≤ (73938397 / 20000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1046_product_upper :
    Real.pi * Real.exp (1047 / 800 : ℝ) ≤ (23257488744891947 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1046_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1046_endpointLower :
    (116057291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (523 / 800 : ℝ) (1047 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (29035534563503 / 2500000000000 : ℝ) (Real.pi * Real.exp (523 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1046_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1047 / 800 : ℝ) - (523 / 1600 : ℝ)) ≤
      (404864322945557 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1046_denomUpper
    linarith [hpThetaJensenCell1046_product_upper]
  have hi : (1 / (404864322945557 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1047 / 800 : ℝ) - (523 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (404864322945557 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (404864322945557 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((523 / 1600 : ℝ) - Real.pi * Real.exp (1047 / 800 : ℝ)) := by
    rw [show (523 / 1600 : ℝ) - Real.pi * Real.exp (1047 / 800 : ℝ) =
      -(Real.pi * Real.exp (1047 / 800 : ℝ) - (523 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (523 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (523 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1046_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (404864322945557 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1046_endpointUpper :
    hpThetaJensenKernelEndpointUpper (523 / 800 : ℝ) (1047 / 1600 : ℝ) ≤ (59210319 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1047 / 800 : ℝ)) (23257488744891947 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1047 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1046_product_upper
  have hD : (398899281953821 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (523 / 400 : ℝ) - (1047 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1046_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1046_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (523 / 400 : ℝ) - (1047 / 3200 : ℝ)) ≤
      (1 / (398899281953821 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (398899281953821 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1047 / 3200 : ℝ) - Real.pi * Real.exp (523 / 400 : ℝ)) ≤
      (2 / (398899281953821 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1047 / 3200 : ℝ) - Real.pi * Real.exp (523 / 400 : ℝ) =
      -(Real.pi * Real.exp (523 / 400 : ℝ) - (1047 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23257488744891947 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (23257488744891947 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1046_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (523 / 800 : ℝ) (1047 / 1600 : ℝ)) :
    (116057291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (59210319 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1046_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1046_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1047_leftExp :
    (9253859723 / 2500000000 : ℝ) ≤ Real.exp (1047 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1047 / 800 : ℝ) (520873148907 / 500000000000 : ℝ)
    (9253859723 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1047_rightExp :
    Real.exp (131 / 100 : ℝ) ≤ (37061737123 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (131 / 100 : ℝ) (65111686989 / 62500000000 : ℝ)
    (37061737123 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1047_denomUpper :
    Real.exp (113161018913456939 / 10000000000000000 : ℝ) ≤ (410667762896467 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (113161018913456939 / 10000000000000000 : ℝ)
    (1424225538327 / 1000000000000 : ℝ) (410667762896467 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1047_denomLower :
    (809219727464723 / 10000000000 : ℝ) ≤ Real.exp (3531637709362377 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3531637709362377 / 312500000000000 : ℝ) (355891065699 /
    250000000000 : ℝ) (809219727464723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1047_product_lower :
    (3633981459362377 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1047 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1047_leftExp
    (by norm_num : (0 : ℝ) ≤ (9253859723 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1047_product_upper :
    Real.pi * Real.exp (131 / 100 : ℝ) ≤ (116432893913456939 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1047_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1047_endpointLower :
    (57362427 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1047 / 1600 : ℝ) (131 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3633981459362377 / 312500000000000 : ℝ) (Real.pi * Real.exp (1047 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1047_product_lower
  have hD : Real.exp (Real.pi * Real.exp (131 / 100 : ℝ) - (1047 / 3200 : ℝ)) ≤
      (410667762896467 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1047_denomUpper
    linarith [hpThetaJensenCell1047_product_upper]
  have hi : (1 / (410667762896467 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (131 / 100 : ℝ) - (1047 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (410667762896467 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (410667762896467 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1047 / 3200 : ℝ) - Real.pi * Real.exp (131 / 100 : ℝ)) := by
    rw [show (1047 / 3200 : ℝ) - Real.pi * Real.exp (131 / 100 : ℝ) =
      -(Real.pi * Real.exp (131 / 100 : ℝ) - (1047 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1047 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1047 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1047_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (410667762896467 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1047_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1047 / 1600 : ℝ) (131 / 200 : ℝ) ≤ (29265791 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (131 / 100 : ℝ)) (116432893913456939 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (131 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1047_product_upper
  have hD : (809219727464723 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1047 / 800 : ℝ) - (131 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1047_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1047_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1047 / 800 : ℝ) - (131 / 400 : ℝ)) ≤
      (1 / (809219727464723 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (809219727464723 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((131 / 400 : ℝ) - Real.pi * Real.exp (1047 / 800 : ℝ)) ≤
      (2 / (809219727464723 / 10000000000 : ℝ) : ℝ) := by
    rw [show (131 / 400 : ℝ) - Real.pi * Real.exp (1047 / 800 : ℝ) =
      -(Real.pi * Real.exp (1047 / 800 : ℝ) - (131 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (116432893913456939 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (116432893913456939 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1047_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1047 / 1600 : ℝ) (131 / 200 : ℝ)) :
    (57362427 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (29265791 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1047_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1047_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1048_leftExp :
    (37061737121 / 10000000000 : ℝ) ≤ Real.exp (131 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (131 / 100 : ℝ) (1041786991823 / 1000000000000 : ℝ)
    (37061737121 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1048_rightExp :
    Real.exp (1049 / 800 : ℝ) ≤ (37108093261 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1049 / 800 : ℝ) (1041827687423 / 1000000000000 : ℝ)
    (37108093261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1048_denomUpper :
    Real.exp (113303526032104773 / 10000000000000000 : ℝ) ≤ (208280984711507 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (113303526032104773 / 10000000000000000 : ℝ)
    (712429968347 / 500000000000 : ℝ) (208280984711507 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1048_denomLower :
    (820819308833901 / 10000000000 : ℝ) ≤ Real.exp (14144341480679579 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14144341480679579 / 1250000000000000 : ℝ) (1424197556717
    / 1000000000000 : ℝ) (820819308833901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1048_product_lower :
    (14554107105679579 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (131 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1048_leftExp
    (by norm_num : (0 : ℝ) ≤ (37061737121 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1048_product_upper :
    Real.pi * Real.exp (1049 / 800 : ℝ) ≤ (116578526032104773 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1048_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1048_endpointLower :
    (113405621 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (131 / 200 : ℝ) (1049 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14554107105679579 / 1250000000000000 : ℝ) (Real.pi * Real.exp (131 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1048_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1049 / 800 : ℝ) - (131 / 400 : ℝ)) ≤
      (208280984711507 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1048_denomUpper
    linarith [hpThetaJensenCell1048_product_upper]
  have hi : (1 / (208280984711507 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1049 / 800 : ℝ) - (131 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (208280984711507 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (208280984711507 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((131 / 400 : ℝ) - Real.pi * Real.exp (1049 / 800 : ℝ)) := by
    rw [show (131 / 400 : ℝ) - Real.pi * Real.exp (1049 / 800 : ℝ) =
      -(Real.pi * Real.exp (1049 / 800 : ℝ) - (131 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (131 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (131 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1048_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (208280984711507 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1048_endpointUpper :
    hpThetaJensenKernelEndpointUpper (131 / 200 : ℝ) (1049 / 1600 : ℝ) ≤ (57859559 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1049 / 800 : ℝ)) (116578526032104773 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1049 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1048_product_upper
  have hD : (820819308833901 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (131 / 100 : ℝ) - (1049 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1048_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1048_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (131 / 100 : ℝ) - (1049 / 3200 : ℝ)) ≤
      (1 / (820819308833901 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (820819308833901 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1049 / 3200 : ℝ) - Real.pi * Real.exp (131 / 100 : ℝ)) ≤
      (2 / (820819308833901 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1049 / 3200 : ℝ) - Real.pi * Real.exp (131 / 100 : ℝ) =
      -(Real.pi * Real.exp (131 / 100 : ℝ) - (1049 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (116578526032104773 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (116578526032104773 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1048_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (131 / 200 : ℝ) (1049 / 1600 : ℝ)) :
    (113405621 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (57859559 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1048_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1048_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1049_leftExp :
    (37108093259 / 10000000000 : ℝ) ≤ Real.exp (1049 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1049 / 800 : ℝ) (520913843711 / 500000000000 : ℝ)
    (37108093259 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1049_rightExp :
    Real.exp (21 / 16 : ℝ) ≤ (1857725369 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 16 : ℝ) (260467096153 / 250000000000 : ℝ)
    (1857725369 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1049_denomUpper :
    Real.exp (5672310765172817 / 500000000000000 : ℝ) ≤ (845096941441393 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5672310765172817 / 500000000000000 : ℝ) (57019817163 /
    40000000000 : ℝ) (845096941441393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1049_denomLower :
    (832600308907767 / 10000000000 : ℝ) ≤ Real.exp (14162154864716041 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14162154864716041 / 1250000000000000 : ℝ) (712415971207
    / 500000000000 : ℝ) (832600308907767 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1049_product_lower :
    (14572311114716041 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1049 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1049_leftExp
    (by norm_num : (0 : ℝ) ≤ (37108093259 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1049_product_upper :
    Real.pi * Real.exp (21 / 16 : ℝ) ≤ (5836217015172817 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1049_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1049_endpointLower :
    (112099487 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1049 / 1600 : ℝ) (21 / 32 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14572311114716041 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1049 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1049_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 16 : ℝ) - (1049 / 3200 : ℝ)) ≤
      (845096941441393 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1049_denomUpper
    linarith [hpThetaJensenCell1049_product_upper]
  have hi : (1 / (845096941441393 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 16 : ℝ) - (1049 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (845096941441393 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (845096941441393 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1049 / 3200 : ℝ) - Real.pi * Real.exp (21 / 16 : ℝ)) := by
    rw [show (1049 / 3200 : ℝ) - Real.pi * Real.exp (21 / 16 : ℝ) =
      -(Real.pi * Real.exp (21 / 16 : ℝ) - (1049 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1049 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1049 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1049_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (845096941441393 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1049_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1049 / 1600 : ℝ) (21 / 32 : ℝ) ≤ (14298549 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 16 : ℝ)) (5836217015172817 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1049_product_upper
  have hD : (832600308907767 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1049 / 800 : ℝ) - (21 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell1049_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1049_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1049 / 800 : ℝ) - (21 / 64 : ℝ)) ≤
      (1 / (832600308907767 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (832600308907767 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 64 : ℝ) - Real.pi * Real.exp (1049 / 800 : ℝ)) ≤
      (2 / (832600308907767 / 10000000000 : ℝ) : ℝ) := by
    rw [show (21 / 64 : ℝ) - Real.pi * Real.exp (1049 / 800 : ℝ) =
      -(Real.pi * Real.exp (1049 / 800 : ℝ) - (21 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5836217015172817 / 500000000000000 : ℝ) ^ 2 - 6 *
      (5836217015172817 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1049_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1049 / 1600 : ℝ) (21 / 32 : ℝ)) :
    (112099487 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14298549 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1049_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1049_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1050_leftExp :
    (18577253689 / 5000000000 : ℝ) ≤ Real.exp (21 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 16 : ℝ) (1041868384611 / 1000000000000 : ℝ)
    (18577253689 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1050_rightExp :
    Real.exp (1051 / 800 : ℝ) ≤ (18600489777 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1051 / 800 : ℝ) (1041909083391 / 1000000000000 : ℝ)
    (18600489777 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1050_denomUpper :
    Real.exp (56794543479994761 / 5000000000000000 : ℝ) ≤ (214314411393541 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56794543479994761 / 5000000000000000 : ℝ) (356533004429
    / 250000000000 : ℝ) (214314411393541 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1050_denomLower :
    (422282891185933 / 5000000000 : ℝ) ≤ Real.exp (7089995508916611 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7089995508916611 / 625000000000000 : ℝ) (712733711051 /
    500000000000 : ℝ) (422282891185933 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1050_product_lower :
    (7295268946416611 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1050_leftExp
    (by norm_num : (0 : ℝ) ≤ (18577253689 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1050_product_upper :
    Real.pi * Real.exp (1051 / 800 : ℝ) ≤ (58435168479994761 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1050_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1050_endpointLower :
    (22161269 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 32 : ℝ) (1051 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7295268946416611 / 625000000000000 : ℝ) (Real.pi * Real.exp (21 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell1050_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1051 / 800 : ℝ) - (21 / 64 : ℝ)) ≤
      (214314411393541 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1050_denomUpper
    linarith [hpThetaJensenCell1050_product_upper]
  have hi : (1 / (214314411393541 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1051 / 800 : ℝ) - (21 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (214314411393541 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (214314411393541 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 64 : ℝ) - Real.pi * Real.exp (1051 / 800 : ℝ)) := by
    rw [show (21 / 64 : ℝ) - Real.pi * Real.exp (1051 / 800 : ℝ) =
      -(Real.pi * Real.exp (1051 / 800 : ℝ) - (21 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 16 : ℝ)) := by
    have h := hpThetaJensenCell1050_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (214314411393541 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1050_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 32 : ℝ) (1051 / 1600 : ℝ) ≤ (113070879 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1051 / 800 : ℝ)) (58435168479994761 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1051 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1050_product_upper
  have hD : (422282891185933 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 16 : ℝ) - (1051 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1050_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1050_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 16 : ℝ) - (1051 / 3200 : ℝ)) ≤
      (1 / (422282891185933 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (422282891185933 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1051 / 3200 : ℝ) - Real.pi * Real.exp (21 / 16 : ℝ)) ≤
      (2 / (422282891185933 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1051 / 3200 : ℝ) - Real.pi * Real.exp (21 / 16 : ℝ) =
      -(Real.pi * Real.exp (21 / 16 : ℝ) - (1051 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58435168479994761 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (58435168479994761 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1050_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 32 : ℝ) (1051 / 1600 : ℝ)) :
    (22161269 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (113070879 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1050_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1050_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1051_leftExp :
    (1162530611 / 312500000 : ℝ) ≤ Real.exp (1051 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1051 / 800 : ℝ) (104190908339 / 100000000000 : ℝ)
    (1162530611 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1051_rightExp :
    Real.exp (263 / 200 : ℝ) ≤ (37247509853 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (263 / 200 : ℝ) (1041949783759 / 1000000000000 : ℝ)
    (37247509853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1051_denomUpper :
    Real.exp (113732141221615829 / 10000000000000000 : ℝ) ≤ (434804609071547 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (113732141221615829 / 10000000000000000 : ℝ)
    (713384852407 / 500000000000 : ℝ) (434804609071547 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1051_denomLower :
    (428359419650533 / 5000000000 : ℝ) ≤ Real.exp (443682811534089 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (443682811534089 / 39062500000000 : ℝ) (1426103998029 /
    1000000000000 : ℝ) (428359419650533 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1051_product_lower :
    (456524608409089 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (1051 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1051_leftExp
    (by norm_num : (0 : ℝ) ≤ (1162530611 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1051_product_upper :
    Real.pi * Real.exp (263 / 200 : ℝ) ≤ (117016516221615829 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1051_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1051_endpointLower :
    (27381523 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1051 / 1600 : ℝ) (263 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (456524608409089 / 39062500000000 : ℝ) (Real.pi * Real.exp (1051 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1051_product_lower
  have hD : Real.exp (Real.pi * Real.exp (263 / 200 : ℝ) - (1051 / 3200 : ℝ)) ≤
      (434804609071547 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1051_denomUpper
    linarith [hpThetaJensenCell1051_product_upper]
  have hi : (1 / (434804609071547 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (263 / 200 : ℝ) - (1051 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (434804609071547 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (434804609071547 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1051 / 3200 : ℝ) - Real.pi * Real.exp (263 / 200 : ℝ)) := by
    rw [show (1051 / 3200 : ℝ) - Real.pi * Real.exp (263 / 200 : ℝ) =
      -(Real.pi * Real.exp (263 / 200 : ℝ) - (1051 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1051 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1051 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1051_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (434804609071547 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1051_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1051 / 1600 : ℝ) (263 / 400 : ℝ) ≤ (111766473 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (263 / 200 : ℝ)) (117016516221615829 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (263 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1051_product_upper
  have hD : (428359419650533 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1051 / 800 : ℝ) - (263 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1051_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1051_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1051 / 800 : ℝ) - (263 / 800 : ℝ)) ≤
      (1 / (428359419650533 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (428359419650533 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((263 / 800 : ℝ) - Real.pi * Real.exp (1051 / 800 : ℝ)) ≤
      (2 / (428359419650533 / 5000000000 : ℝ) : ℝ) := by
    rw [show (263 / 800 : ℝ) - Real.pi * Real.exp (1051 / 800 : ℝ) =
      -(Real.pi * Real.exp (1051 / 800 : ℝ) - (263 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (117016516221615829 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (117016516221615829 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1051_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1051 / 1600 : ℝ) (263 / 400 : ℝ)) :
    (27381523 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (111766473 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1051_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1051_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1052_leftExp :
    (37247509851 / 10000000000 : ℝ) ≤ Real.exp (263 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (263 / 200 : ℝ) (520974891879 / 500000000000 : ℝ)
    (37247509851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1052_rightExp :
    Real.exp (1053 / 800 : ℝ) ≤ (37294098353 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1053 / 800 : ℝ) (520995242859 / 500000000000 : ℝ)
    (37294098353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1052_denomUpper :
    Real.exp (113875378327096329 / 10000000000000000 : ℝ) ≤ (441077442306017 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (113875378327096329 / 10000000000000000 : ℝ)
    (356852123163 / 250000000000 : ℝ) (441077442306017 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1052_denomLower :
    (173812528912693 / 2000000000 : ℝ) ≤ Real.exp (14215731745977849 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14215731745977849 / 1250000000000000 : ℝ) (142674167239
    / 100000000000 : ℝ) (173812528912693 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1052_product_lower :
    (14627059870977849 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (263 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1052_leftExp
    (by norm_num : (0 : ℝ) ≤ (37247509851 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1052_product_upper :
    Real.pi * Real.exp (1053 / 800 : ℝ) ≤ (117162878327096329 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1052_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1052_endpointLower :
    (108258623 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (263 / 400 : ℝ) (1053 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14627059870977849 / 1250000000000000 : ℝ) (Real.pi * Real.exp (263 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1052_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1053 / 800 : ℝ) - (263 / 800 : ℝ)) ≤
      (441077442306017 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1052_denomUpper
    linarith [hpThetaJensenCell1052_product_upper]
  have hi : (1 / (441077442306017 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1053 / 800 : ℝ) - (263 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (441077442306017 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (441077442306017 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((263 / 800 : ℝ) - Real.pi * Real.exp (1053 / 800 : ℝ)) := by
    rw [show (263 / 800 : ℝ) - Real.pi * Real.exp (1053 / 800 : ℝ) =
      -(Real.pi * Real.exp (1053 / 800 : ℝ) - (263 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (263 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (263 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1052_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (441077442306017 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1052_endpointUpper :
    hpThetaJensenKernelEndpointUpper (263 / 400 : ℝ) (1053 / 1600 : ℝ) ≤ (110475069 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1053 / 800 : ℝ)) (117162878327096329 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1053 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1052_product_upper
  have hD : (173812528912693 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (263 / 200 : ℝ) - (1053 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1052_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1052_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (263 / 200 : ℝ) - (1053 / 3200 : ℝ)) ≤
      (1 / (173812528912693 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (173812528912693 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1053 / 3200 : ℝ) - Real.pi * Real.exp (263 / 200 : ℝ)) ≤
      (2 / (173812528912693 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1053 / 3200 : ℝ) - Real.pi * Real.exp (263 / 200 : ℝ) =
      -(Real.pi * Real.exp (263 / 200 : ℝ) - (1053 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (117162878327096329 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (117162878327096329 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1052_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (263 / 400 : ℝ) (1053 / 1600 : ℝ)) :
    (108258623 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (110475069 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1052_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1052_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1053_leftExp :
    (37294098351 / 10000000000 : ℝ) ≤ Real.exp (1053 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1053 / 800 : ℝ) (1041990485717 / 1000000000000 : ℝ)
    (37294098351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1053_rightExp :
    Real.exp (527 / 400 : ℝ) ≤ (9335186281 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (527 / 400 : ℝ) (521015594633 / 500000000000 : ℝ)
    (9335186281 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1053_denomUpper :
    Real.exp (28504699624085633 / 2500000000000000 : ℝ) ≤ (447448963468843 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28504699624085633 / 2500000000000000 : ℝ) (357012095859
    / 250000000000 : ℝ) (447448963468843 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1053_denomLower :
    (220400105413033 / 2500000000 : ℝ) ≤ Real.exp (14233636378339349 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14233636378339349 / 1250000000000000 : ℝ) (1427380447471
    / 1000000000000 : ℝ) (220400105413033 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1053_product_lower :
    (14645355128339349 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1053 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1053_leftExp
    (by norm_num : (0 : ℝ) ≤ (37294098351 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1053_product_upper :
    Real.pi * Real.exp (527 / 400 : ℝ) ≤ (29327355874085633 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1053_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1053_endpointLower :
    (53501917 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1053 / 1600 : ℝ) (527 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14645355128339349 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1053 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1053_product_lower
  have hD : Real.exp (Real.pi * Real.exp (527 / 400 : ℝ) - (1053 / 3200 : ℝ)) ≤
      (447448963468843 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1053_denomUpper
    linarith [hpThetaJensenCell1053_product_upper]
  have hi : (1 / (447448963468843 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (527 / 400 : ℝ) - (1053 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (447448963468843 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (447448963468843 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1053 / 3200 : ℝ) - Real.pi * Real.exp (527 / 400 : ℝ)) := by
    rw [show (1053 / 3200 : ℝ) - Real.pi * Real.exp (527 / 400 : ℝ) =
      -(Real.pi * Real.exp (527 / 400 : ℝ) - (1053 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1053 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1053 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1053_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (447448963468843 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1053_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1053 / 1600 : ℝ) (527 / 800 : ℝ) ≤ (109196561 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (527 / 400 : ℝ)) (29327355874085633 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (527 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1053_product_upper
  have hD : (220400105413033 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1053 / 800 : ℝ) - (527 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1053_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1053_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1053 / 800 : ℝ) - (527 / 1600 : ℝ)) ≤
      (1 / (220400105413033 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (220400105413033 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((527 / 1600 : ℝ) - Real.pi * Real.exp (1053 / 800 : ℝ)) ≤
      (2 / (220400105413033 / 2500000000 : ℝ) : ℝ) := by
    rw [show (527 / 1600 : ℝ) - Real.pi * Real.exp (1053 / 800 : ℝ) =
      -(Real.pi * Real.exp (1053 / 800 : ℝ) - (527 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (29327355874085633 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (29327355874085633 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1053_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1053 / 1600 : ℝ) (527 / 800 : ℝ)) :
    (53501917 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (109196561 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1053_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1053_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1054_leftExp :
    (37340745121 / 10000000000 : ℝ) ≤ Real.exp (527 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (527 / 400 : ℝ) (208406237853 / 200000000000 : ℝ)
    (37340745121 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1054_rightExp :
    Real.exp (211 / 160 : ℝ) ≤ (58417891 / 15625000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (211 / 160 : ℝ) (208414378881 / 200000000000 : ℝ)
    (58417891 / 15625000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1054_denomUpper :
    Real.exp (178378753065363 / 15625000000000 : ℝ) ≤ (226960421827251 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (178378753065363 / 15625000000000 : ℝ) (142868937943 /
    100000000000 : ℝ) (226960421827251 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1054_denomLower :
    (447167725049933 / 5000000000 : ℝ) ≤ Real.exp (14251563893271579 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14251563893271579 / 1250000000000000 : ℝ) (71401016273 /
    50000000000 : ℝ) (447167725049933 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1054_product_lower :
    (14663673268271579 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (527 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1054_leftExp
    (by norm_num : (0 : ℝ) ≤ (37340745121 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1054_product_upper :
    Real.pi * Real.exp (211 / 160 : ℝ) ≤ (183525237440363 / 15625000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1054_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1054_endpointLower :
    (105761623 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (527 / 800 : ℝ) (211 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14663673268271579 / 1250000000000000 : ℝ) (Real.pi * Real.exp (527 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1054_product_lower
  have hD : Real.exp (Real.pi * Real.exp (211 / 160 : ℝ) - (527 / 1600 : ℝ)) ≤
      (226960421827251 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1054_denomUpper
    linarith [hpThetaJensenCell1054_product_upper]
  have hi : (1 / (226960421827251 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (211 / 160 : ℝ) - (527 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (226960421827251 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (226960421827251 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((527 / 1600 : ℝ) - Real.pi * Real.exp (211 / 160 : ℝ)) := by
    rw [show (527 / 1600 : ℝ) - Real.pi * Real.exp (211 / 160 : ℝ) =
      -(Real.pi * Real.exp (211 / 160 : ℝ) - (527 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (527 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (527 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1054_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (226960421827251 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1054_endpointUpper :
    hpThetaJensenKernelEndpointUpper (527 / 800 : ℝ) (211 / 320 : ℝ) ≤ (21586169 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (211 / 160 : ℝ)) (183525237440363 / 15625000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (211 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1054_product_upper
  have hD : (447167725049933 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (527 / 400 : ℝ) - (211 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1054_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1054_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (527 / 400 : ℝ) - (211 / 640 : ℝ)) ≤
      (1 / (447167725049933 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (447167725049933 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((211 / 640 : ℝ) - Real.pi * Real.exp (527 / 400 : ℝ)) ≤
      (2 / (447167725049933 / 5000000000 : ℝ) : ℝ) := by
    rw [show (211 / 640 : ℝ) - Real.pi * Real.exp (527 / 400 : ℝ) =
      -(Real.pi * Real.exp (527 / 400 : ℝ) - (211 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (183525237440363 / 15625000000000 : ℝ) ^ 2 - 6 *
      (183525237440363 / 15625000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1054_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (527 / 800 : ℝ) (211 / 320 : ℝ)) :
    (105761623 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (21586169 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1054_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1054_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1055_leftExp :
    (18693725119 / 5000000000 : ℝ) ≤ Real.exp (211 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (211 / 160 : ℝ) (260517973601 / 250000000000 : ℝ)
    (18693725119 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1055_rightExp :
    Real.exp (33 / 25 : ℝ) ≤ (18717106887 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 25 : ℝ) (1042112601133 / 1000000000000 : ℝ)
    (18717106887 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1055_denomUpper :
    Real.exp (57153094476450991 / 5000000000000000 : ℝ) ≤ (920989567948913 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (57153094476450991 / 5000000000000000 : ℝ) (178666435361
    / 125000000000 : ℝ) (920989567948913 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1055_denomLower :
    (226817767718411 / 2500000000 : ℝ) ≤ Real.exp (7134757160506181 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7134757160506181 / 625000000000000 : ℝ) (285732261733 /
    200000000000 : ℝ) (226817767718411 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1055_product_lower :
    (7341007160506181 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (211 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1055_leftExp
    (by norm_num : (0 : ℝ) ≤ (18693725119 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1055_product_upper :
    Real.pi * Real.exp (33 / 25 : ℝ) ≤ (58801531976450991 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1055_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1055_endpointLower :
    (52265943 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (211 / 320 : ℝ) (33 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7341007160506181 / 625000000000000 : ℝ) (Real.pi * Real.exp (211 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1055_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 25 : ℝ) - (211 / 640 : ℝ)) ≤
      (920989567948913 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1055_denomUpper
    linarith [hpThetaJensenCell1055_product_upper]
  have hi : (1 / (920989567948913 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 25 : ℝ) - (211 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (920989567948913 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (920989567948913 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((211 / 640 : ℝ) - Real.pi * Real.exp (33 / 25 : ℝ)) := by
    rw [show (211 / 640 : ℝ) - Real.pi * Real.exp (33 / 25 : ℝ) =
      -(Real.pi * Real.exp (33 / 25 : ℝ) - (211 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (211 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (211 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1055_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (920989567948913 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1055_endpointUpper :
    hpThetaJensenKernelEndpointUpper (211 / 320 : ℝ) (33 / 50 : ℝ) ≤ (13334727 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 25 : ℝ)) (58801531976450991 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1055_product_upper
  have hD : (226817767718411 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (211 / 160 : ℝ) - (33 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell1055_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1055_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (211 / 160 : ℝ) - (33 / 100 : ℝ)) ≤
      (1 / (226817767718411 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (226817767718411 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 100 : ℝ) - Real.pi * Real.exp (211 / 160 : ℝ)) ≤
      (2 / (226817767718411 / 2500000000 : ℝ) : ℝ) := by
    rw [show (33 / 100 : ℝ) - Real.pi * Real.exp (211 / 160 : ℝ) =
      -(Real.pi * Real.exp (211 / 160 : ℝ) - (33 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58801531976450991 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (58801531976450991 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1055_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (211 / 320 : ℝ) (33 / 50 : ℝ)) :
    (52265943 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13334727 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1055_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1055_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1056_leftExp :
    (9358553443 / 2500000000 : ℝ) ≤ Real.exp (33 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 25 : ℝ) (260528150283 / 250000000000 : ℝ)
    (9358553443 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1056_rightExp :
    Real.exp (1057 / 800 : ℝ) ≤ (37481035799 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1057 / 800 : ℝ) (260538327363 / 250000000000 : ℝ)
    (37481035799 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1056_denomUpper :
    Real.exp (114450159698887807 / 10000000000000000 : ℝ) ≤ (934345032580341 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (114450159698887807 / 10000000000000000 : ℝ)
    (142997469607 / 100000000000 : ℝ) (934345032580341 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1056_denomLower :
    (184082136642849 / 2000000000 : ℝ) ≤ Real.exp (3571871922262657 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3571871922262657 / 312500000000000 : ℝ) (714651699649 /
    500000000000 : ℝ) (184082136642849 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1056_product_lower :
    (3675094578512657 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1056_leftExp
    (by norm_num : (0 : ℝ) ≤ (9358553443 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1056_product_upper :
    Real.pi * Real.exp (1057 / 800 : ℝ) ≤ (117750159698887807 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1056_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1056_endpointLower :
    (103314523 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 50 : ℝ) (1057 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3675094578512657 / 312500000000000 : ℝ) (Real.pi * Real.exp (33 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1056_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1057 / 800 : ℝ) - (33 / 100 : ℝ)) ≤
      (934345032580341 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1056_denomUpper
    linarith [hpThetaJensenCell1056_product_upper]
  have hi : (1 / (934345032580341 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1057 / 800 : ℝ) - (33 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (934345032580341 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (934345032580341 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 100 : ℝ) - Real.pi * Real.exp (1057 / 800 : ℝ)) := by
    rw [show (33 / 100 : ℝ) - Real.pi * Real.exp (1057 / 800 : ℝ) =
      -(Real.pi * Real.exp (1057 / 800 : ℝ) - (33 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1056_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (934345032580341 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1056_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 50 : ℝ) (1057 / 1600 : ℝ) ≤ (26359343 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1057 / 800 : ℝ)) (117750159698887807 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1057 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1056_product_upper
  have hD : (184082136642849 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 25 : ℝ) - (1057 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1056_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1056_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 25 : ℝ) - (1057 / 3200 : ℝ)) ≤
      (1 / (184082136642849 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (184082136642849 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1057 / 3200 : ℝ) - Real.pi * Real.exp (33 / 25 : ℝ)) ≤
      (2 / (184082136642849 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1057 / 3200 : ℝ) - Real.pi * Real.exp (33 / 25 : ℝ) =
      -(Real.pi * Real.exp (33 / 25 : ℝ) - (1057 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (117750159698887807 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (117750159698887807 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1056_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 50 : ℝ) (1057 / 1600 : ℝ)) :
    (103314523 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (26359343 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1056_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1056_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1057_leftExp :
    (37481035797 / 10000000000 : ℝ) ≤ Real.exp (1057 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1057 / 800 : ℝ) (1042153309451 / 1000000000000 : ℝ)
    (37481035797 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1057_rightExp :
    Real.exp (529 / 400 : ℝ) ≤ (37527916387 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (529 / 400 : ℝ) (6513712621 / 6250000000 : ℝ)
    (37527916387 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1057_denomUpper :
    Real.exp (114594314425984491 / 10000000000000000 : ℝ) ≤ (947911607264163 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (114594314425984491 / 10000000000000000 : ℝ)
    (715309510613 / 500000000000 : ℝ) (947911607264163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1057_denomLower :
    (933757748946071 / 10000000000 : ℝ) ≤ Real.exp (14305484026446103 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14305484026446103 / 1250000000000000 : ℝ) (1429946599633
    / 1000000000000 : ℝ) (933757748946071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1057_product_lower :
    (14718765276446103 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1057 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1057_leftExp
    (by norm_num : (0 : ℝ) ≤ (37481035797 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1057_product_upper :
    Real.pi * Real.exp (529 / 400 : ℝ) ≤ (117897439425984491 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1057_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1057_endpointLower :
    (102109431 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1057 / 1600 : ℝ) (529 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14718765276446103 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1057 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1057_product_lower
  have hD : Real.exp (Real.pi * Real.exp (529 / 400 : ℝ) - (1057 / 3200 : ℝ)) ≤
      (947911607264163 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1057_denomUpper
    linarith [hpThetaJensenCell1057_product_upper]
  have hi : (1 / (947911607264163 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (529 / 400 : ℝ) - (1057 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (947911607264163 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (947911607264163 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1057 / 3200 : ℝ) - Real.pi * Real.exp (529 / 400 : ℝ)) := by
    rw [show (1057 / 3200 : ℝ) - Real.pi * Real.exp (529 / 400 : ℝ) =
      -(Real.pi * Real.exp (529 / 400 : ℝ) - (1057 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1057 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1057 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1057_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (947911607264163 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1057_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1057 / 1600 : ℝ) (529 / 800 : ℝ) ≤ (104209409 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (529 / 400 : ℝ)) (117897439425984491 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (529 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1057_product_upper
  have hD : (933757748946071 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1057 / 800 : ℝ) - (529 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1057_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1057_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1057 / 800 : ℝ) - (529 / 1600 : ℝ)) ≤
      (1 / (933757748946071 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (933757748946071 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((529 / 1600 : ℝ) - Real.pi * Real.exp (1057 / 800 : ℝ)) ≤
      (2 / (933757748946071 / 10000000000 : ℝ) : ℝ) := by
    rw [show (529 / 1600 : ℝ) - Real.pi * Real.exp (1057 / 800 : ℝ) =
      -(Real.pi * Real.exp (1057 / 800 : ℝ) - (529 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (117897439425984491 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (117897439425984491 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1057_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1057 / 1600 : ℝ) (529 / 800 : ℝ)) :
    (102109431 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (104209409 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1057_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1057_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1058_leftExp :
    (7505583277 / 2000000000 : ℝ) ≤ Real.exp (529 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (529 / 400 : ℝ) (1042194019359 / 1000000000000 : ℝ)
    (7505583277 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1058_rightExp :
    Real.exp (1059 / 800 : ℝ) ≤ (18787427807 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1059 / 800 : ℝ) (1042234730859 / 1000000000000 : ℝ)
    (18787427807 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1058_denomUpper :
    Real.exp (57369326686476551 / 5000000000000000 : ℝ) ≤ (240423220764959 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57369326686476551 / 5000000000000000 : ℝ) (286252892133
    / 200000000000 : ℝ) (240423220764959 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1058_denomLower :
    (473657895955849 / 5000000000 : ℝ) ≤ Real.exp (2864700672294623 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2864700672294623 / 250000000000000 : ℝ) (17882386399 /
    12500000000 : ℝ) (473657895955849 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1058_product_lower :
    (2947435047294623 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (529 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1058_leftExp
    (by norm_num : (0 : ℝ) ≤ (7505583277 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1058_product_upper :
    Real.pi * Real.exp (1059 / 800 : ℝ) ≤ (59022451686476551 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1058_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1058_endpointLower :
    (100916511 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (529 / 800 : ℝ) (1059 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2947435047294623 / 250000000000000 : ℝ) (Real.pi * Real.exp (529 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1058_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1059 / 800 : ℝ) - (529 / 1600 : ℝ)) ≤
      (240423220764959 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1058_denomUpper
    linarith [hpThetaJensenCell1058_product_upper]
  have hi : (1 / (240423220764959 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1059 / 800 : ℝ) - (529 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (240423220764959 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (240423220764959 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((529 / 1600 : ℝ) - Real.pi * Real.exp (1059 / 800 : ℝ)) := by
    rw [show (529 / 1600 : ℝ) - Real.pi * Real.exp (1059 / 800 : ℝ) =
      -(Real.pi * Real.exp (1059 / 800 : ℝ) - (529 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (529 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (529 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1058_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (240423220764959 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1058_endpointUpper :
    hpThetaJensenKernelEndpointUpper (529 / 800 : ℝ) (1059 / 1600 : ℝ) ≤ (51496913 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1059 / 800 : ℝ)) (59022451686476551 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1059 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1058_product_upper
  have hD : (473657895955849 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (529 / 400 : ℝ) - (1059 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1058_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1058_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (529 / 400 : ℝ) - (1059 / 3200 : ℝ)) ≤
      (1 / (473657895955849 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (473657895955849 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1059 / 3200 : ℝ) - Real.pi * Real.exp (529 / 400 : ℝ)) ≤
      (2 / (473657895955849 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1059 / 3200 : ℝ) - Real.pi * Real.exp (529 / 400 : ℝ) =
      -(Real.pi * Real.exp (529 / 400 : ℝ) - (1059 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59022451686476551 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (59022451686476551 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1058_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (529 / 800 : ℝ) (1059 / 1600 : ℝ)) :
    (100916511 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (51496913 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1058_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1058_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1059_leftExp :
    (37574855611 / 10000000000 : ℝ) ≤ Real.exp (1059 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1059 / 800 : ℝ) (521117365429 / 500000000000 : ℝ)
    (37574855611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1059_rightExp :
    Real.exp (53 / 40 : ℝ) ≤ (37621853551 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 40 : ℝ) (1042275443949 / 1000000000000 : ℝ)
    (37621853551 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1059_denomUpper :
    Real.exp (114883176762846743 / 10000000000000000 : ℝ) ≤ (487846257324093 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (114883176762846743 / 10000000000000000 : ℝ)
    (178988877079 / 125000000000 : ℝ) (487846257324093 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1059_denomLower :
    (480544200294559 / 5000000000 : ℝ) ≤ Real.exp (14341545723584089 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14341545723584089 / 1250000000000000 : ℝ) (1431236338453
    / 1000000000000 : ℝ) (480544200294559 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1059_product_lower :
    (14755608223584089 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1059 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1059_leftExp
    (by norm_num : (0 : ℝ) ≤ (37574855611 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1059_product_upper :
    Real.pi * Real.exp (53 / 40 : ℝ) ≤ (118192551762846743 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1059_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1059_endpointLower :
    (99735661 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1059 / 1600 : ℝ) (53 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14755608223584089 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1059 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1059_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 40 : ℝ) - (1059 / 3200 : ℝ)) ≤
      (487846257324093 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1059_denomUpper
    linarith [hpThetaJensenCell1059_product_upper]
  have hi : (1 / (487846257324093 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 40 : ℝ) - (1059 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (487846257324093 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (487846257324093 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1059 / 3200 : ℝ) - Real.pi * Real.exp (53 / 40 : ℝ)) := by
    rw [show (1059 / 3200 : ℝ) - Real.pi * Real.exp (53 / 40 : ℝ) =
      -(Real.pi * Real.exp (53 / 40 : ℝ) - (1059 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1059 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1059 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1059_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (487846257324093 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1059_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1059 / 1600 : ℝ) (53 / 80 : ℝ) ≤ (101790521 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 40 : ℝ)) (118192551762846743 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1059_product_upper
  have hD : (480544200294559 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1059 / 800 : ℝ) - (53 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1059_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1059_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1059 / 800 : ℝ) - (53 / 160 : ℝ)) ≤
      (1 / (480544200294559 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (480544200294559 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 160 : ℝ) - Real.pi * Real.exp (1059 / 800 : ℝ)) ≤
      (2 / (480544200294559 / 5000000000 : ℝ) : ℝ) := by
    rw [show (53 / 160 : ℝ) - Real.pi * Real.exp (1059 / 800 : ℝ) =
      -(Real.pi * Real.exp (1059 / 800 : ℝ) - (53 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (118192551762846743 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (118192551762846743 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1059_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1059 / 1600 : ℝ) (53 / 80 : ℝ)) :
    (99735661 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (101790521 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1059_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1059_endpointUpper

def hpThetaJensenCellsBatch052Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (124335207 / 10000000000 : ℝ)
  | 1 => (122921287 / 10000000000 : ℝ)
  | 2 => (6076061 / 500000000 : ℝ)
  | 3 => (7508431 / 625000000 : ℝ)
  | 4 => (29690551 / 2500000000 : ℝ)
  | 5 => (117403039 / 10000000000 : ℝ)
  | 6 => (116057291 / 10000000000 : ℝ)
  | 7 => (57362427 / 5000000000 : ℝ)
  | 8 => (113405621 / 10000000000 : ℝ)
  | 9 => (112099487 / 10000000000 : ℝ)
  | 10 => (22161269 / 2000000000 : ℝ)
  | 11 => (27381523 / 2500000000 : ℝ)
  | 12 => (108258623 / 10000000000 : ℝ)
  | 13 => (53501917 / 5000000000 : ℝ)
  | 14 => (105761623 / 10000000000 : ℝ)
  | 15 => (52265943 / 5000000000 : ℝ)
  | 16 => (103314523 / 10000000000 : ℝ)
  | 17 => (102109431 / 10000000000 : ℝ)
  | 18 => (100916511 / 10000000000 : ℝ)
  | 19 => (99735661 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch052Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7928347 / 625000000 : ℝ)
  | 1 => (125413223 / 10000000000 : ℝ)
  | 2 => (123986979 / 10000000000 : ℝ)
  | 3 => (30643677 / 2500000000 : ℝ)
  | 4 => (121176301 / 10000000000 : ℝ)
  | 5 => (119791647 / 10000000000 : ℝ)
  | 6 => (59210319 / 5000000000 : ℝ)
  | 7 => (29265791 / 2500000000 : ℝ)
  | 8 => (57859559 / 5000000000 : ℝ)
  | 9 => (14298549 / 1250000000 : ℝ)
  | 10 => (113070879 / 10000000000 : ℝ)
  | 11 => (111766473 / 10000000000 : ℝ)
  | 12 => (110475069 / 10000000000 : ℝ)
  | 13 => (109196561 / 10000000000 : ℝ)
  | 14 => (21586169 / 2000000000 : ℝ)
  | 15 => (13334727 / 1250000000 : ℝ)
  | 16 => (26359343 / 2500000000 : ℝ)
  | 17 => (104209409 / 10000000000 : ℝ)
  | 18 => (51496913 / 5000000000 : ℝ)
  | 19 => (101790521 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch052_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch052Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch052Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1040_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1041_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1042_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1043_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1044_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1045_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1046_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1047_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1048_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1049_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1050_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1051_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1052_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1053_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1054_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1055_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1056_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1057_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1058_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1059_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper] at h ⊢
    exact h

end HodgeProofHP
