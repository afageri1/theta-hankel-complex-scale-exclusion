import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell600_leftExp :
    (4234000033 / 2000000000 : ℝ) ≤ Real.exp (3 / 4 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 4 : ℝ) (511857158301 / 500000000000 : ℝ) (4234000033
    / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell600_rightExp :
    Real.exp (601 / 800 : ℝ) ≤ (21196479213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (601 / 800 : ℝ) (63984644139 / 62500000000 : ℝ)
    (21196479213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell600_denomUpper :
    Real.exp (64715710720206309 / 10000000000000000 : ℝ) ≤ (1292997250863 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (64715710720206309 / 10000000000000000 : ℝ)
    (1224137599913 / 1000000000000 : ℝ) (1292997250863 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell600_denomLower :
    (1281882521499 / 2000000000 : ℝ) ≤ Real.exp (1615734453959067 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1615734453959067 / 250000000000000 : ℝ) (611903692643 /
    500000000000 : ℝ) (1281882521499 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell600_product_lower :
    (1662687578959067 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 4 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell600_leftExp
    (by norm_num : (0 : ℝ) ≤ (4234000033 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell600_product_upper :
    Real.pi * Real.exp (601 / 800 : ℝ) ≤ (66590710720206309 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell600_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell600_endpointLower :
    (1059750259 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 8 : ℝ) (601 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1662687578959067 / 250000000000000 : ℝ) (Real.pi * Real.exp (3 / 4 : ℝ))
    (by norm_num) hpThetaJensenCell600_product_lower
  have hD : Real.exp (Real.pi * Real.exp (601 / 800 : ℝ) - (3 / 16 : ℝ)) ≤
      (1292997250863 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell600_denomUpper
    linarith [hpThetaJensenCell600_product_upper]
  have hi : (1 / (1292997250863 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (601 / 800 : ℝ) - (3 / 16 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1292997250863 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1292997250863 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 16 : ℝ) - Real.pi * Real.exp (601 / 800 : ℝ)) := by
    rw [show (3 / 16 : ℝ) - Real.pi * Real.exp (601 / 800 : ℝ) =
      -(Real.pi * Real.exp (601 / 800 : ℝ) - (3 / 16 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 4 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 4 : ℝ)) := by
    have h := hpThetaJensenCell600_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1292997250863 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell600_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 8 : ℝ) (601 / 1600 : ℝ) ≤ (4299313763 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (601 / 800 : ℝ)) (66590710720206309 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (601 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell600_product_upper
  have hD : (1281882521499 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 4 : ℝ) - (601 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell600_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell600_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 4 : ℝ) - (601 / 3200 : ℝ)) ≤
      (1 / (1281882521499 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1281882521499 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((601 / 3200 : ℝ) - Real.pi * Real.exp (3 / 4 : ℝ)) ≤
      (2 / (1281882521499 / 2000000000 : ℝ) : ℝ) := by
    rw [show (601 / 3200 : ℝ) - Real.pi * Real.exp (3 / 4 : ℝ) =
      -(Real.pi * Real.exp (3 / 4 : ℝ) - (601 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66590710720206309 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (66590710720206309 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell600_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 8 : ℝ) (601 / 1600 : ℝ)) :
    (1059750259 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4299313763 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell600_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell600_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell601_leftExp :
    (21196479211 / 10000000000 : ℝ) ≤ Real.exp (601 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (601 / 800 : ℝ) (1023754306223 / 1000000000000 : ℝ)
    (21196479211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell601_rightExp :
    Real.exp (301 / 400 : ℝ) ≤ (21222991379 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (301 / 400 : ℝ) (15996785897 / 15625000000 : ℝ)
    (21222991379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell601_denomUpper :
    Real.exp (64795876155326747 / 10000000000000000 : ℝ) ≤ (3258510695083 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (64795876155326747 / 10000000000000000 : ℝ)
    (1224444305589 / 1000000000000 : ℝ) (3258510695083 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell601_denomLower :
    (3230466600603 / 5000000000 : ℝ) ≤ Real.exp (8088679939680489 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8088679939680489 / 1250000000000000 : ℝ) (12241136101 /
    10000000000 : ℝ) (3230466600603 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell601_product_lower :
    (8323836189680489 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (601 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell601_leftExp
    (by norm_num : (0 : ℝ) ≤ (21196479211 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell601_product_upper :
    Real.pi * Real.exp (301 / 400 : ℝ) ≤ (66674001155326747 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell601_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell601_endpointLower :
    (2108607219 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (601 / 1600 : ℝ) (301 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8323836189680489 / 1250000000000000 : ℝ) (Real.pi * Real.exp (601 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell601_product_lower
  have hD : Real.exp (Real.pi * Real.exp (301 / 400 : ℝ) - (601 / 3200 : ℝ)) ≤
      (3258510695083 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell601_denomUpper
    linarith [hpThetaJensenCell601_product_upper]
  have hi : (1 / (3258510695083 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (301 / 400 : ℝ) - (601 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3258510695083 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3258510695083 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((601 / 3200 : ℝ) - Real.pi * Real.exp (301 / 400 : ℝ)) := by
    rw [show (601 / 3200 : ℝ) - Real.pi * Real.exp (301 / 400 : ℝ) =
      -(Real.pi * Real.exp (301 / 400 : ℝ) - (601 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (601 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (601 / 800 : ℝ)) := by
    have h := hpThetaJensenCell601_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3258510695083 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell601_endpointUpper :
    hpThetaJensenKernelEndpointUpper (601 / 1600 : ℝ) (301 / 800 : ℝ) ≤ (534657399 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (301 / 400 : ℝ)) (66674001155326747 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (301 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell601_product_upper
  have hD : (3230466600603 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (601 / 800 : ℝ) - (301 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell601_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell601_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (601 / 800 : ℝ) - (301 / 1600 : ℝ)) ≤
      (1 / (3230466600603 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3230466600603 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((301 / 1600 : ℝ) - Real.pi * Real.exp (601 / 800 : ℝ)) ≤
      (2 / (3230466600603 / 5000000000 : ℝ) : ℝ) := by
    rw [show (301 / 1600 : ℝ) - Real.pi * Real.exp (601 / 800 : ℝ) =
      -(Real.pi * Real.exp (601 / 800 : ℝ) - (301 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66674001155326747 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (66674001155326747 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell601_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (601 / 1600 : ℝ) (301 / 800 : ℝ)) :
    (2108607219 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (534657399 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell601_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell601_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell602_leftExp :
    (21222991377 / 10000000000 : ℝ) ≤ Real.exp (301 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (301 / 400 : ℝ) (1023794297407 / 1000000000000 : ℝ)
    (21222991377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell602_rightExp :
    Real.exp (603 / 800 : ℝ) ≤ (4249907341 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (603 / 800 : ℝ) (511917145077 / 500000000000 : ℝ)
    (4249907341 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell602_denomUpper :
    Real.exp (12975229153134213 / 2000000000000000 : ℝ) ≤ (1313908756511 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12975229153134213 / 2000000000000000 : ℝ) (48990059473 /
    40000000000 : ℝ) (1313908756511 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell602_denomLower :
    (6512935697739 / 10000000000 : ℝ) ≤ Real.exp (8098700615756523 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8098700615756523 / 1250000000000000 : ℝ) (38263134677 /
    31250000000 : ℝ) (6512935697739 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell602_product_lower :
    (8334247490756523 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (301 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell602_leftExp
    (by norm_num : (0 : ℝ) ≤ (21222991377 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell602_product_upper :
    Real.pi * Real.exp (603 / 800 : ℝ) ≤ (13351479153134213 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell602_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell602_endpointLower :
    (2097746823 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (301 / 800 : ℝ) (603 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8334247490756523 / 1250000000000000 : ℝ) (Real.pi * Real.exp (301 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell602_product_lower
  have hD : Real.exp (Real.pi * Real.exp (603 / 800 : ℝ) - (301 / 1600 : ℝ)) ≤
      (1313908756511 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell602_denomUpper
    linarith [hpThetaJensenCell602_product_upper]
  have hi : (1 / (1313908756511 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (603 / 800 : ℝ) - (301 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1313908756511 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1313908756511 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((301 / 1600 : ℝ) - Real.pi * Real.exp (603 / 800 : ℝ)) := by
    rw [show (301 / 1600 : ℝ) - Real.pi * Real.exp (603 / 800 : ℝ) =
      -(Real.pi * Real.exp (603 / 800 : ℝ) - (301 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (301 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (301 / 400 : ℝ)) := by
    have h := hpThetaJensenCell602_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1313908756511 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell602_endpointUpper :
    hpThetaJensenKernelEndpointUpper (301 / 800 : ℝ) (603 / 1600 : ℝ) ≤ (1063817747 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (603 / 800 : ℝ)) (13351479153134213 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (603 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell602_product_upper
  have hD : (6512935697739 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (301 / 400 : ℝ) - (603 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell602_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell602_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (301 / 400 : ℝ) - (603 / 3200 : ℝ)) ≤
      (1 / (6512935697739 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6512935697739 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((603 / 3200 : ℝ) - Real.pi * Real.exp (301 / 400 : ℝ)) ≤
      (2 / (6512935697739 / 10000000000 : ℝ) : ℝ) := by
    rw [show (603 / 3200 : ℝ) - Real.pi * Real.exp (301 / 400 : ℝ) =
      -(Real.pi * Real.exp (301 / 400 : ℝ) - (603 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13351479153134213 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (13351479153134213 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell602_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (301 / 800 : ℝ) (603 / 1600 : ℝ)) :
    (2097746823 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1063817747 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell602_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell602_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell603_leftExp :
    (332024011 / 156250000 : ℝ) ≤ Real.exp (603 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (603 / 800 : ℝ) (1023834290153 / 1000000000000 : ℝ)
    (332024011 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell603_rightExp :
    Real.exp (151 / 200 : ℝ) ≤ (10638057617 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (151 / 200 : ℝ) (511937142231 / 500000000000 : ℝ)
    (10638057617 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell603_denomUpper :
    Real.exp (32478259843163881 / 5000000000000000 : ℝ) ≤ (6622558546513 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32478259843163881 / 5000000000000000 : ℝ) (1225059144457
    / 1000000000000 : ℝ) (6622558546513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell603_denomLower :
    (656542514701 / 1000000000 : ℝ) ≤ Real.exp (126698973658189 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (126698973658189 / 19531250000000 : ℝ) (122472748479 /
    100000000000 : ℝ) (656542514701 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell603_product_lower :
    (130385497095689 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (603 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell603_leftExp
    (by norm_num : (0 : ℝ) ≤ (332024011 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell603_product_upper :
    Real.pi * Real.exp (151 / 200 : ℝ) ≤ (33420447343163881 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell603_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell603_endpointLower :
    (1043459687 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (603 / 1600 : ℝ) (151 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (130385497095689 / 19531250000000 : ℝ) (Real.pi * Real.exp (603 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell603_product_lower
  have hD : Real.exp (Real.pi * Real.exp (151 / 200 : ℝ) - (603 / 3200 : ℝ)) ≤
      (6622558546513 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell603_denomUpper
    linarith [hpThetaJensenCell603_product_upper]
  have hi : (1 / (6622558546513 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (151 / 200 : ℝ) - (603 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6622558546513 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6622558546513 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((603 / 3200 : ℝ) - Real.pi * Real.exp (151 / 200 : ℝ)) := by
    rw [show (603 / 3200 : ℝ) - Real.pi * Real.exp (151 / 200 : ℝ) =
      -(Real.pi * Real.exp (151 / 200 : ℝ) - (603 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (603 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (603 / 800 : ℝ)) := by
    have h := hpThetaJensenCell603_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6622558546513 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell603_endpointUpper :
    hpThetaJensenKernelEndpointUpper (603 / 1600 : ℝ) (151 / 400 : ℝ) ≤ (2116674623 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (151 / 200 : ℝ)) (33420447343163881 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (151 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell603_product_upper
  have hD : (656542514701 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (603 / 800 : ℝ) - (151 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell603_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell603_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (603 / 800 : ℝ) - (151 / 800 : ℝ)) ≤
      (1 / (656542514701 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (656542514701 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((151 / 800 : ℝ) - Real.pi * Real.exp (603 / 800 : ℝ)) ≤
      (2 / (656542514701 / 1000000000 : ℝ) : ℝ) := by
    rw [show (151 / 800 : ℝ) - Real.pi * Real.exp (603 / 800 : ℝ) =
      -(Real.pi * Real.exp (603 / 800 : ℝ) - (151 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33420447343163881 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (33420447343163881 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell603_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (603 / 1600 : ℝ) (151 / 400 : ℝ)) :
    (1043459687 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2116674623 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell603_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell603_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell604_leftExp :
    (21276115233 / 10000000000 : ℝ) ≤ Real.exp (151 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (151 / 200 : ℝ) (1023874284461 / 1000000000000 : ℝ)
    (21276115233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell604_rightExp :
    Real.exp (121 / 160 : ℝ) ≤ (21302727007 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (121 / 160 : ℝ) (255978570083 / 250000000000 : ℝ)
    (21302727007 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell604_denomUpper :
    Real.exp (65036998046102151 / 10000000000000000 : ℝ) ≤ (6676070851737 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65036998046102151 / 10000000000000000 : ℝ) (612683639649
    / 500000000000 : ℝ) (6676070851737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell604_denomLower :
    (661840665691 / 1000000000 : ℝ) ≤ Real.exp (8118781050883867 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8118781050883867 / 1250000000000000 : ℝ) (1225035136291
    / 1000000000000 : ℝ) (661840665691 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell604_product_lower :
    (8355109175883867 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (151 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell604_leftExp
    (by norm_num : (0 : ℝ) ≤ (21276115233 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell604_product_upper :
    Real.pi * Real.exp (121 / 160 : ℝ) ≤ (66924498046102151 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell604_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell604_endpointLower :
    (4152249829 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (151 / 400 : ℝ) (121 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8355109175883867 / 1250000000000000 : ℝ) (Real.pi * Real.exp (151 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell604_product_lower
  have hD : Real.exp (Real.pi * Real.exp (121 / 160 : ℝ) - (151 / 800 : ℝ)) ≤
      (6676070851737 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell604_denomUpper
    linarith [hpThetaJensenCell604_product_upper]
  have hi : (1 / (6676070851737 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (121 / 160 : ℝ) - (151 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6676070851737 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6676070851737 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((151 / 800 : ℝ) - Real.pi * Real.exp (121 / 160 : ℝ)) := by
    rw [show (151 / 800 : ℝ) - Real.pi * Real.exp (121 / 160 : ℝ) =
      -(Real.pi * Real.exp (121 / 160 : ℝ) - (151 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (151 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (151 / 200 : ℝ)) := by
    have h := hpThetaJensenCell604_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6676070851737 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell604_endpointUpper :
    hpThetaJensenKernelEndpointUpper (151 / 400 : ℝ) (121 / 320 : ℝ) ≤ (1052873513 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (121 / 160 : ℝ)) (66924498046102151 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (121 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell604_product_upper
  have hD : (661840665691 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (151 / 200 : ℝ) - (121 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell604_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell604_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (151 / 200 : ℝ) - (121 / 640 : ℝ)) ≤
      (1 / (661840665691 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (661840665691 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((121 / 640 : ℝ) - Real.pi * Real.exp (151 / 200 : ℝ)) ≤
      (2 / (661840665691 / 1000000000 : ℝ) : ℝ) := by
    rw [show (121 / 640 : ℝ) - Real.pi * Real.exp (151 / 200 : ℝ) =
      -(Real.pi * Real.exp (151 / 200 : ℝ) - (121 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66924498046102151 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (66924498046102151 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell604_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (151 / 400 : ℝ) (121 / 320 : ℝ)) :
    (4152249829 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1052873513 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell604_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell604_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell605_leftExp :
    (4260545401 / 2000000000 : ℝ) ≤ Real.exp (121 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (121 / 160 : ℝ) (1023914280331 / 1000000000000 : ℝ)
    (4260545401 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell605_rightExp :
    Real.exp (303 / 400 : ℝ) ≤ (10664686033 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (303 / 400 : ℝ) (204790855553 / 200000000000 : ℝ)
    (10664686033 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell605_denomUpper :
    Real.exp (32558790488470569 / 5000000000000000 : ℝ) ≤ (1682521482417 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32558790488470569 / 5000000000000000 : ℝ) (49027035687 /
    40000000000 : ℝ) (1682521482417 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell605_denomLower :
    (1667971348419 / 2500000000 : ℝ) ≤ Real.exp (1625768168427299 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1625768168427299 / 250000000000000 : ℝ) (1225343264979 /
    1000000000000 : ℝ) (1667971348419 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell605_product_lower :
    (1673111918427299 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (121 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell605_leftExp
    (by norm_num : (0 : ℝ) ≤ (4260545401 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell605_product_upper :
    Real.pi * Real.exp (303 / 400 : ℝ) ≤ (33504102988470569 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell605_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell605_endpointLower :
    (4130726973 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (121 / 320 : ℝ) (303 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1673111918427299 / 250000000000000 : ℝ) (Real.pi * Real.exp (121 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell605_product_lower
  have hD : Real.exp (Real.pi * Real.exp (303 / 400 : ℝ) - (121 / 640 : ℝ)) ≤
      (1682521482417 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell605_denomUpper
    linarith [hpThetaJensenCell605_product_upper]
  have hi : (1 / (1682521482417 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (303 / 400 : ℝ) - (121 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1682521482417 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1682521482417 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((121 / 640 : ℝ) - Real.pi * Real.exp (303 / 400 : ℝ)) := by
    rw [show (121 / 640 : ℝ) - Real.pi * Real.exp (303 / 400 : ℝ) =
      -(Real.pi * Real.exp (303 / 400 : ℝ) - (121 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (121 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (121 / 160 : ℝ)) := by
    have h := hpThetaJensenCell605_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1682521482417 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell605_endpointUpper :
    hpThetaJensenKernelEndpointUpper (121 / 320 : ℝ) (303 / 800 : ℝ) ≤ (523713187 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (303 / 400 : ℝ)) (33504102988470569 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (303 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell605_product_upper
  have hD : (1667971348419 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (121 / 160 : ℝ) - (303 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell605_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell605_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (121 / 160 : ℝ) - (303 / 1600 : ℝ)) ≤
      (1 / (1667971348419 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1667971348419 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((303 / 1600 : ℝ) - Real.pi * Real.exp (121 / 160 : ℝ)) ≤
      (2 / (1667971348419 / 2500000000 : ℝ) : ℝ) := by
    rw [show (303 / 1600 : ℝ) - Real.pi * Real.exp (121 / 160 : ℝ) =
      -(Real.pi * Real.exp (121 / 160 : ℝ) - (303 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33504102988470569 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (33504102988470569 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell605_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (121 / 320 : ℝ) (303 / 800 : ℝ)) :
    (4130726973 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (523713187 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell605_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell605_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell606_leftExp :
    (666542877 / 312500000 : ℝ) ≤ Real.exp (303 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (303 / 400 : ℝ) (255988569441 / 250000000000 : ℝ)
    (666542877 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell606_rightExp :
    Real.exp (607 / 800 : ℝ) ≤ (21356050451 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (607 / 800 : ℝ) (25599856919 / 25000000000 : ℝ)
    (21356050451 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell606_denomUpper :
    Real.exp (65198268604508443 / 10000000000000000 : ℝ) ≤ (3392304533789 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65198268604508443 / 10000000000000000 : ℝ)
    (1225984983891 / 1000000000000 : ℝ) (3392304533789 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell606_denomLower :
    (6725866589803 / 10000000000 : ℝ) ≤ Real.exp (254341053286273 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (254341053286273 / 39062500000000 : ℝ) (612825935853 /
    500000000000 : ℝ) (6725866589803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell606_product_lower :
    (261750721255023 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (303 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell606_leftExp
    (by norm_num : (0 : ℝ) ≤ (666542877 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell606_product_upper :
    Real.pi * Real.exp (607 / 800 : ℝ) ≤ (67092018604508443 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell606_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell606_endpointLower :
    (2054635133 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (303 / 800 : ℝ) (607 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (261750721255023 / 39062500000000 : ℝ) (Real.pi * Real.exp (303 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell606_product_lower
  have hD : Real.exp (Real.pi * Real.exp (607 / 800 : ℝ) - (303 / 1600 : ℝ)) ≤
      (3392304533789 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell606_denomUpper
    linarith [hpThetaJensenCell606_product_upper]
  have hi : (1 / (3392304533789 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (607 / 800 : ℝ) - (303 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3392304533789 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3392304533789 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((303 / 1600 : ℝ) - Real.pi * Real.exp (607 / 800 : ℝ)) := by
    rw [show (303 / 1600 : ℝ) - Real.pi * Real.exp (607 / 800 : ℝ) =
      -(Real.pi * Real.exp (607 / 800 : ℝ) - (303 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (303 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (303 / 400 : ℝ)) := by
    have h := hpThetaJensenCell606_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3392304533789 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell606_endpointUpper :
    hpThetaJensenKernelEndpointUpper (303 / 800 : ℝ) (607 / 1600 : ℝ) ≤ (2083991829 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (607 / 800 : ℝ)) (67092018604508443 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (607 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell606_product_upper
  have hD : (6725866589803 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (303 / 400 : ℝ) - (607 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell606_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell606_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (303 / 400 : ℝ) - (607 / 3200 : ℝ)) ≤
      (1 / (6725866589803 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6725866589803 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((607 / 3200 : ℝ) - Real.pi * Real.exp (303 / 400 : ℝ)) ≤
      (2 / (6725866589803 / 10000000000 : ℝ) : ℝ) := by
    rw [show (607 / 3200 : ℝ) - Real.pi * Real.exp (303 / 400 : ℝ) =
      -(Real.pi * Real.exp (303 / 400 : ℝ) - (607 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67092018604508443 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67092018604508443 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell606_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (303 / 800 : ℝ) (607 / 1600 : ℝ)) :
    (2054635133 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2083991829 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell606_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell606_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell607_leftExp :
    (21356050449 / 10000000000 : ℝ) ≤ Real.exp (607 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (607 / 800 : ℝ) (1023994276759 / 1000000000000 : ℝ)
    (21356050449 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell607_rightExp :
    Real.exp (19 / 25 : ℝ) ≤ (10691381103 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 25 : ℝ) (512017138659 / 500000000000 : ℝ)
    (10691381103 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell607_denomUpper :
    Real.exp (32639530533517079 / 5000000000000000 : ℝ) ≤ (3419822811271 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (32639530533517079 / 5000000000000000 : ℝ) (12262945553 /
    10000000000 : ℝ) (3419822811271 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell607_denomLower :
    (6780355527177 / 10000000000 : ℝ) ≤ Real.exp (8148999655271851 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8148999655271851 / 1250000000000000 : ℝ) (1225960957263
    / 1000000000000 : ℝ) (6780355527177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell607_product_lower :
    (8386499655271851 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (607 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell607_leftExp
    (by norm_num : (0 : ℝ) ≤ (21356050449 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell607_product_upper :
    Real.pi * Real.exp (19 / 25 : ℝ) ≤ (33587968033517079 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell607_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell607_endpointLower :
    (817575957 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (607 / 1600 : ℝ) (19 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8386499655271851 / 1250000000000000 : ℝ) (Real.pi * Real.exp (607 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell607_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 25 : ℝ) - (607 / 3200 : ℝ)) ≤
      (3419822811271 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell607_denomUpper
    linarith [hpThetaJensenCell607_product_upper]
  have hi : (1 / (3419822811271 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 25 : ℝ) - (607 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3419822811271 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3419822811271 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((607 / 3200 : ℝ) - Real.pi * Real.exp (19 / 25 : ℝ)) := by
    rw [show (607 / 3200 : ℝ) - Real.pi * Real.exp (19 / 25 : ℝ) =
      -(Real.pi * Real.exp (19 / 25 : ℝ) - (607 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (607 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (607 / 800 : ℝ)) := by
    have h := hpThetaJensenCell607_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3419822811271 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell607_endpointUpper :
    hpThetaJensenKernelEndpointUpper (607 / 1600 : ℝ) (19 / 50 : ℝ) ≤ (33170629 / 80000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 25 : ℝ)) (33587968033517079 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 50 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell607_product_upper
  have hD : (6780355527177 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (607 / 800 : ℝ) - (19 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell607_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell607_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (607 / 800 : ℝ) - (19 / 100 : ℝ)) ≤
      (1 / (6780355527177 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6780355527177 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 100 : ℝ) - Real.pi * Real.exp (607 / 800 : ℝ)) ≤
      (2 / (6780355527177 / 10000000000 : ℝ) : ℝ) := by
    rw [show (19 / 100 : ℝ) - Real.pi * Real.exp (607 / 800 : ℝ) =
      -(Real.pi * Real.exp (607 / 800 : ℝ) - (19 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33587968033517079 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (33587968033517079 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell607_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (607 / 1600 : ℝ) (19 / 50 : ℝ)) :
    (817575957 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (33170629 / 80000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell607_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell607_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell608_leftExp :
    (5345690551 / 2500000000 : ℝ) ≤ Real.exp (19 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 25 : ℝ) (1024034277317 / 1000000000000 : ℝ)
    (5345690551 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell608_rightExp :
    Real.exp (609 / 800 : ℝ) ≤ (21409507371 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (609 / 800 : ℝ) (512037139719 / 500000000000 : ℝ)
    (21409507371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell608_denomUpper :
    Real.exp (65359958490182003 / 10000000000000000 : ℝ) ≤ (6895201004549 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65359958490182003 / 10000000000000000 : ℝ)
    (1226604607207 / 1000000000000 : ℝ) (6895201004549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell608_denomLower :
    (1367071511867 / 2000000000 : ℝ) ≤ Real.exp (2039774677437149 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2039774677437149 / 312500000000000 : ℝ) (1226270522503 /
    1000000000000 : ℝ) (1367071511867 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell608_product_lower :
    (2099247333687149 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell608_leftExp
    (by norm_num : (0 : ℝ) ≤ (5345690551 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell608_product_upper :
    Real.pi * Real.exp (609 / 800 : ℝ) ≤ (67259958490182003 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell608_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell608_endpointLower :
    (1016638903 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 50 : ℝ) (609 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2099247333687149 / 312500000000000 : ℝ) (Real.pi * Real.exp (19 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell608_product_lower
  have hD : Real.exp (Real.pi * Real.exp (609 / 800 : ℝ) - (19 / 100 : ℝ)) ≤
      (6895201004549 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell608_denomUpper
    linarith [hpThetaJensenCell608_product_upper]
  have hi : (1 / (6895201004549 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (609 / 800 : ℝ) - (19 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6895201004549 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6895201004549 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 100 : ℝ) - Real.pi * Real.exp (609 / 800 : ℝ)) := by
    rw [show (19 / 100 : ℝ) - Real.pi * Real.exp (609 / 800 : ℝ) =
      -(Real.pi * Real.exp (609 / 800 : ℝ) - (19 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 25 : ℝ)) := by
    have h := hpThetaJensenCell608_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6895201004549 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell608_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 50 : ℝ) (609 / 1600 : ℝ) ≤ (2062370237 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (609 / 800 : ℝ)) (67259958490182003 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (609 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell608_product_upper
  have hD : (1367071511867 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 25 : ℝ) - (609 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell608_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell608_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 25 : ℝ) - (609 / 3200 : ℝ)) ≤
      (1 / (1367071511867 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1367071511867 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((609 / 3200 : ℝ) - Real.pi * Real.exp (19 / 25 : ℝ)) ≤
      (2 / (1367071511867 / 2000000000 : ℝ) : ℝ) := by
    rw [show (609 / 3200 : ℝ) - Real.pi * Real.exp (19 / 25 : ℝ) =
      -(Real.pi * Real.exp (19 / 25 : ℝ) - (609 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67259958490182003 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67259958490182003 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell608_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 50 : ℝ) (609 / 1600 : ℝ)) :
    (1016638903 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2062370237 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell608_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell608_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell609_leftExp :
    (21409507369 / 10000000000 : ℝ) ≤ Real.exp (609 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (609 / 800 : ℝ) (1024074279437 / 1000000000000 : ℝ)
    (21409507369 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell609_rightExp :
    Real.exp (61 / 80 : ℝ) ≤ (5359071497 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 80 : ℝ) (1024114283121 / 1000000000000 : ℝ)
    (5359071497 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell609_denomUpper :
    Real.exp (16360240251474721 / 2500000000000000 : ℝ) ≤ (3475640345261 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16360240251474721 / 2500000000000000 : ℝ) (1226915140443
    / 1000000000000 : ℝ) (3475640345261 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell609_denomLower :
    (6890878092871 / 10000000000 : ℝ) ≤ Real.exp (8169210884298931 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8169210884298931 / 1250000000000000 : ℝ) (1226580568231
    / 1000000000000 : ℝ) (6890878092871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell609_product_lower :
    (8407492134298931 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (609 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell609_leftExp
    (by norm_num : (0 : ℝ) ≤ (21409507369 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell609_product_upper :
    Real.pi * Real.exp (61 / 80 : ℝ) ≤ (16836021501474721 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell609_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell609_endpointLower :
    (4045297821 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (609 / 1600 : ℝ) (61 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8407492134298931 / 1250000000000000 : ℝ) (Real.pi * Real.exp (609 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell609_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 80 : ℝ) - (609 / 3200 : ℝ)) ≤
      (3475640345261 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell609_denomUpper
    linarith [hpThetaJensenCell609_product_upper]
  have hi : (1 / (3475640345261 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 80 : ℝ) - (609 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3475640345261 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3475640345261 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((609 / 3200 : ℝ) - Real.pi * Real.exp (61 / 80 : ℝ)) := by
    rw [show (609 / 3200 : ℝ) - Real.pi * Real.exp (61 / 80 : ℝ) =
      -(Real.pi * Real.exp (61 / 80 : ℝ) - (609 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (609 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (609 / 800 : ℝ)) := by
    have h := hpThetaJensenCell609_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3475640345261 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell609_endpointUpper :
    hpThetaJensenKernelEndpointUpper (609 / 1600 : ℝ) (61 / 160 : ℝ) ≤ (4103219287 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 80 : ℝ)) (16836021501474721 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell609_product_upper
  have hD : (6890878092871 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (609 / 800 : ℝ) - (61 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell609_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell609_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (609 / 800 : ℝ) - (61 / 320 : ℝ)) ≤
      (1 / (6890878092871 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6890878092871 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 320 : ℝ) - Real.pi * Real.exp (609 / 800 : ℝ)) ≤
      (2 / (6890878092871 / 10000000000 : ℝ) : ℝ) := by
    rw [show (61 / 320 : ℝ) - Real.pi * Real.exp (609 / 800 : ℝ) =
      -(Real.pi * Real.exp (609 / 800 : ℝ) - (61 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (16836021501474721 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (16836021501474721 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell609_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (609 / 1600 : ℝ) (61 / 160 : ℝ)) :
    (4045297821 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4103219287 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell609_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell609_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell610_leftExp :
    (10718142993 / 5000000000 : ℝ) ≤ Real.exp (61 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 80 : ℝ) (12801428539 / 12500000000 : ℝ)
    (10718142993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell610_rightExp :
    Real.exp (611 / 800 : ℝ) ≤ (214630981 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (611 / 800 : ℝ) (1024154288367 / 1000000000000 : ℝ)
    (214630981 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell610_denomUpper :
    Real.exp (655220687492733 / 100000000000000 : ℝ) ≤ (3503945111357 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (655220687492733 / 100000000000000 : ℝ) (1227226155851 /
    1000000000000 : ℝ) (3503945111357 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell610_denomLower :
    (868365325159 / 1250000000 : ℝ) ≤ Real.exp (4089668097708107 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4089668097708107 / 625000000000000 : ℝ) (613445547639 /
    500000000000 : ℝ) (868365325159 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell610_product_lower :
    (4209004035208107 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell610_leftExp
    (by norm_num : (0 : ℝ) ≤ (10718142993 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell610_product_upper :
    Real.pi * Real.exp (611 / 800 : ℝ) ≤ (674283187492733 / 100000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell610_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell610_endpointLower :
    (4024106487 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 160 : ℝ) (611 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4209004035208107 / 625000000000000 : ℝ) (Real.pi * Real.exp (61 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell610_product_lower
  have hD : Real.exp (Real.pi * Real.exp (611 / 800 : ℝ) - (61 / 320 : ℝ)) ≤
      (3503945111357 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell610_denomUpper
    linarith [hpThetaJensenCell610_product_upper]
  have hi : (1 / (3503945111357 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (611 / 800 : ℝ) - (61 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3503945111357 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3503945111357 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 320 : ℝ) - Real.pi * Real.exp (611 / 800 : ℝ)) := by
    rw [show (61 / 320 : ℝ) - Real.pi * Real.exp (611 / 800 : ℝ) =
      -(Real.pi * Real.exp (611 / 800 : ℝ) - (61 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 80 : ℝ)) := by
    have h := hpThetaJensenCell610_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3503945111357 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell610_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 160 : ℝ) (611 / 1600 : ℝ) ≤ (2040882571 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (611 / 800 : ℝ)) (674283187492733 / 100000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (611 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell610_product_upper
  have hD : (868365325159 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 80 : ℝ) - (611 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell610_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell610_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 80 : ℝ) - (611 / 3200 : ℝ)) ≤
      (1 / (868365325159 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (868365325159 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((611 / 3200 : ℝ) - Real.pi * Real.exp (61 / 80 : ℝ)) ≤
      (2 / (868365325159 / 1250000000 : ℝ) : ℝ) := by
    rw [show (611 / 3200 : ℝ) - Real.pi * Real.exp (61 / 80 : ℝ) =
      -(Real.pi * Real.exp (61 / 80 : ℝ) - (611 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (674283187492733 / 100000000000000 : ℝ) ^ 2 - 6 *
      (674283187492733 / 100000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell610_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 160 : ℝ) (611 / 1600 : ℝ)) :
    (4024106487 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2040882571 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell610_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell610_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell611_leftExp :
    (10731549049 / 5000000000 : ℝ) ≤ Real.exp (611 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (611 / 800 : ℝ) (512077144183 / 500000000000 : ℝ)
    (10731549049 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell611_rightExp :
    Real.exp (153 / 200 : ℝ) ≤ (21489943747 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (153 / 200 : ℝ) (40967771807 / 40000000000 : ℝ)
    (21489943747 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell611_denomUpper :
    Real.exp (65603281845968971 / 10000000000000000 : ℝ) ≤ (7065035201289 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65603281845968971 / 10000000000000000 : ℝ)
    (1227537654241 / 1000000000000 : ℝ) (7065035201289 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell611_denomLower :
    (1400699324699 / 2000000000 : ℝ) ≤ Real.exp (4094737329993251 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4094737329993251 / 625000000000000 : ℝ) (153400263061 /
    125000000000 : ℝ) (1400699324699 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell611_product_lower :
    (4214268579993251 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (611 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell611_leftExp
    (by norm_num : (0 : ℝ) ≤ (10731549049 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell611_product_upper :
    Real.pi * Real.exp (153 / 200 : ℝ) ≤ (67512656845968971 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell611_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell611_endpointLower :
    (800596337 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (611 / 1600 : ℝ) (153 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4214268579993251 / 625000000000000 : ℝ) (Real.pi * Real.exp (611 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell611_product_lower
  have hD : Real.exp (Real.pi * Real.exp (153 / 200 : ℝ) - (611 / 3200 : ℝ)) ≤
      (7065035201289 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell611_denomUpper
    linarith [hpThetaJensenCell611_product_upper]
  have hi : (1 / (7065035201289 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (153 / 200 : ℝ) - (611 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7065035201289 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7065035201289 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((611 / 3200 : ℝ) - Real.pi * Real.exp (153 / 200 : ℝ)) := by
    rw [show (611 / 3200 : ℝ) - Real.pi * Real.exp (153 / 200 : ℝ) =
      -(Real.pi * Real.exp (153 / 200 : ℝ) - (611 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (611 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (611 / 800 : ℝ)) := by
    have h := hpThetaJensenCell611_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7065035201289 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell611_endpointUpper :
    hpThetaJensenKernelEndpointUpper (611 / 1600 : ℝ) (153 / 400 : ℝ) ≤ (406037811 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (153 / 200 : ℝ)) (67512656845968971 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (153 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell611_product_upper
  have hD : (1400699324699 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (611 / 800 : ℝ) - (153 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell611_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell611_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (611 / 800 : ℝ) - (153 / 800 : ℝ)) ≤
      (1 / (1400699324699 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1400699324699 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((153 / 800 : ℝ) - Real.pi * Real.exp (611 / 800 : ℝ)) ≤
      (2 / (1400699324699 / 2000000000 : ℝ) : ℝ) := by
    rw [show (153 / 800 : ℝ) - Real.pi * Real.exp (611 / 800 : ℝ) =
      -(Real.pi * Real.exp (611 / 800 : ℝ) - (153 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67512656845968971 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67512656845968971 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell611_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (611 / 1600 : ℝ) (153 / 400 : ℝ)) :
    (800596337 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (406037811 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell611_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell611_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell612_leftExp :
    (10744971873 / 5000000000 : ℝ) ≤ Real.exp (153 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (153 / 200 : ℝ) (512097147587 / 500000000000 : ℝ)
    (10744971873 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell612_rightExp :
    Real.exp (613 / 800 : ℝ) ≤ (21516822973 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (613 / 800 : ℝ) (512117151773 / 500000000000 : ℝ)
    (21516822973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell612_denomUpper :
    Real.exp (65684600434215989 / 10000000000000000 : ℝ) ≤ (3561360649957 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65684600434215989 / 10000000000000000 : ℝ)
    (1227849636471 / 1000000000000 : ℝ) (3561360649957 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell612_denomLower :
    (3530302879201 / 5000000000 : ℝ) ≤ Real.exp (4099813147055227 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4099813147055227 / 625000000000000 : ℝ) (1227513596683 /
    1000000000000 : ℝ) (3530302879201 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell612_product_lower :
    (4219539709555227 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (153 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell612_leftExp
    (by norm_num : (0 : ℝ) ≤ (10744971873 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell612_product_upper :
    Real.pi * Real.exp (613 / 800 : ℝ) ≤ (67597100434215989 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell612_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell612_endpointLower :
    (995480871 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (153 / 400 : ℝ) (613 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4219539709555227 / 625000000000000 : ℝ) (Real.pi * Real.exp (153 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell612_product_lower
  have hD : Real.exp (Real.pi * Real.exp (613 / 800 : ℝ) - (153 / 800 : ℝ)) ≤
      (3561360649957 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell612_denomUpper
    linarith [hpThetaJensenCell612_product_upper]
  have hi : (1 / (3561360649957 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (613 / 800 : ℝ) - (153 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3561360649957 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3561360649957 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((153 / 800 : ℝ) - Real.pi * Real.exp (613 / 800 : ℝ)) := by
    rw [show (153 / 800 : ℝ) - Real.pi * Real.exp (613 / 800 : ℝ) =
      -(Real.pi * Real.exp (613 / 800 : ℝ) - (153 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (153 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (153 / 200 : ℝ)) := by
    have h := hpThetaJensenCell612_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3561360649957 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell612_endpointUpper :
    hpThetaJensenKernelEndpointUpper (153 / 400 : ℝ) (613 / 1600 : ℝ) ≤ (4039058267 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (613 / 800 : ℝ)) (67597100434215989 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (613 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell612_product_upper
  have hD : (3530302879201 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (153 / 200 : ℝ) - (613 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell612_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell612_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (153 / 200 : ℝ) - (613 / 3200 : ℝ)) ≤
      (1 / (3530302879201 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3530302879201 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((613 / 3200 : ℝ) - Real.pi * Real.exp (153 / 200 : ℝ)) ≤
      (2 / (3530302879201 / 5000000000 : ℝ) : ℝ) := by
    rw [show (613 / 3200 : ℝ) - Real.pi * Real.exp (153 / 200 : ℝ) =
      -(Real.pi * Real.exp (153 / 200 : ℝ) - (613 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67597100434215989 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67597100434215989 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell612_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (153 / 400 : ℝ) (613 / 1600 : ℝ)) :
    (995480871 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4039058267 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell612_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell612_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell613_leftExp :
    (21516822971 / 10000000000 : ℝ) ≤ Real.exp (613 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (613 / 800 : ℝ) (204846860709 / 200000000000 : ℝ)
    (21516822971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell613_rightExp :
    Real.exp (307 / 400 : ℝ) ≤ (21543735819 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (307 / 400 : ℝ) (25606857837 / 25000000000 : ℝ)
    (21543735819 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell613_denomUpper :
    Real.exp (65766024642819667 / 10000000000000000 : ℝ) ≤ (1436190850239 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65766024642819667 / 10000000000000000 : ℝ)
    (1228162103363 / 1000000000000 : ℝ) (1436190850239 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell613_denomLower :
    (7118255669107 / 10000000000 : ℝ) ≤ Real.exp (8209791113888729 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8209791113888729 / 1250000000000000 : ℝ) (1227825572683
    / 1000000000000 : ℝ) (7118255669107 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell613_product_lower :
    (8449634863888729 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (613 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell613_leftExp
    (by norm_num : (0 : ℝ) ≤ (21516822971 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell613_product_upper :
    Real.pi * Real.exp (307 / 400 : ℝ) ≤ (67681649642819667 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell613_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell613_endpointLower :
    (3960931953 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (613 / 1600 : ℝ) (307 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8449634863888729 / 1250000000000000 : ℝ) (Real.pi * Real.exp (613 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell613_product_lower
  have hD : Real.exp (Real.pi * Real.exp (307 / 400 : ℝ) - (613 / 3200 : ℝ)) ≤
      (1436190850239 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell613_denomUpper
    linarith [hpThetaJensenCell613_product_upper]
  have hi : (1 / (1436190850239 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (307 / 400 : ℝ) - (613 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1436190850239 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1436190850239 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((613 / 3200 : ℝ) - Real.pi * Real.exp (307 / 400 : ℝ)) := by
    rw [show (613 / 3200 : ℝ) - Real.pi * Real.exp (307 / 400 : ℝ) =
      -(Real.pi * Real.exp (307 / 400 : ℝ) - (613 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (613 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (613 / 800 : ℝ)) := by
    have h := hpThetaJensenCell613_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1436190850239 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell613_endpointUpper :
    hpThetaJensenKernelEndpointUpper (613 / 1600 : ℝ) (307 / 800 : ℝ) ≤ (803561137 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (307 / 400 : ℝ)) (67681649642819667 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (307 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell613_product_upper
  have hD : (7118255669107 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (613 / 800 : ℝ) - (307 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell613_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell613_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (613 / 800 : ℝ) - (307 / 1600 : ℝ)) ≤
      (1 / (7118255669107 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7118255669107 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((307 / 1600 : ℝ) - Real.pi * Real.exp (613 / 800 : ℝ)) ≤
      (2 / (7118255669107 / 10000000000 : ℝ) : ℝ) := by
    rw [show (307 / 1600 : ℝ) - Real.pi * Real.exp (613 / 800 : ℝ) =
      -(Real.pi * Real.exp (613 / 800 : ℝ) - (307 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67681649642819667 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67681649642819667 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell613_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (613 / 1600 : ℝ) (307 / 800 : ℝ)) :
    (3960931953 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (803561137 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell613_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell613_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell614_leftExp :
    (21543735817 / 10000000000 : ℝ) ≤ Real.exp (307 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (307 / 400 : ℝ) (1024274313479 / 1000000000000 : ℝ)
    (21543735817 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell614_rightExp :
    Real.exp (123 / 160 : ℝ) ≤ (21570682327 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (123 / 160 : ℝ) (1024314324977 / 1000000000000 : ℝ)
    (21570682327 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell614_denomUpper :
    Real.exp (65847554603726911 / 10000000000000000 : ℝ) ≤ (7239739857033 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65847554603726911 / 10000000000000000 : ℝ) (245695011151
    / 200000000000 : ℝ) (7239739857033 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell614_denomLower :
    (3588226045807 / 5000000000 : ℝ) ≤ Real.exp (8219969136600083 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8219969136600083 / 1250000000000000 : ℝ) (307034508337 /
    250000000000 : ℝ) (3588226045807 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell614_product_lower :
    (8460203511600083 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (307 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell614_leftExp
    (by norm_num : (0 : ℝ) ≤ (21543735817 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell614_product_upper :
    Real.pi * Real.exp (123 / 160 : ℝ) ≤ (67766304603726911 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell614_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell614_endpointLower :
    (98500179 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (307 / 800 : ℝ) (123 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8460203511600083 / 1250000000000000 : ℝ) (Real.pi * Real.exp (307 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell614_product_lower
  have hD : Real.exp (Real.pi * Real.exp (123 / 160 : ℝ) - (307 / 1600 : ℝ)) ≤
      (7239739857033 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell614_denomUpper
    linarith [hpThetaJensenCell614_product_upper]
  have hi : (1 / (7239739857033 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (123 / 160 : ℝ) - (307 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7239739857033 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7239739857033 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((307 / 1600 : ℝ) - Real.pi * Real.exp (123 / 160 : ℝ)) := by
    rw [show (307 / 1600 : ℝ) - Real.pi * Real.exp (123 / 160 : ℝ) =
      -(Real.pi * Real.exp (123 / 160 : ℝ) - (307 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (307 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (307 / 400 : ℝ)) := by
    have h := hpThetaJensenCell614_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7239739857033 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell614_endpointUpper :
    hpThetaJensenKernelEndpointUpper (307 / 800 : ℝ) (123 / 320 : ℝ) ≤ (3996620431 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (123 / 160 : ℝ)) (67766304603726911 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (123 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell614_product_upper
  have hD : (3588226045807 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (307 / 400 : ℝ) - (123 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell614_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell614_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (307 / 400 : ℝ) - (123 / 640 : ℝ)) ≤
      (1 / (3588226045807 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3588226045807 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((123 / 640 : ℝ) - Real.pi * Real.exp (307 / 400 : ℝ)) ≤
      (2 / (3588226045807 / 5000000000 : ℝ) : ℝ) := by
    rw [show (123 / 640 : ℝ) - Real.pi * Real.exp (307 / 400 : ℝ) =
      -(Real.pi * Real.exp (307 / 400 : ℝ) - (123 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67766304603726911 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67766304603726911 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell614_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (307 / 800 : ℝ) (123 / 320 : ℝ)) :
    (98500179 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3996620431 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell614_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell614_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell615_leftExp :
    (862827293 / 400000000 : ℝ) ≤ Real.exp (123 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (123 / 160 : ℝ) (64019645311 / 62500000000 : ℝ)
    (862827293 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell615_rightExp :
    Real.exp (77 / 100 : ℝ) ≤ (21597662539 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 100 : ℝ) (1024354338037 / 1000000000000 : ℝ)
    (21597662539 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell615_denomUpper :
    Real.exp (65929190448884627 / 10000000000000000 : ℝ) ≤ (3649541992979 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65929190448884627 / 10000000000000000 : ℝ) (614394247241
    / 500000000000 : ℝ) (3649541992979 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell615_denomLower :
    (7235200821791 / 10000000000 : ℝ) ≤ Real.exp (329206415133807 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (329206415133807 / 50000000000000 : ℝ) (1228450979503 /
    1000000000000 : ℝ) (7235200821791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell615_product_lower :
    (338831415133807 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (123 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell615_leftExp
    (by norm_num : (0 : ℝ) ≤ (862827293 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell615_product_upper :
    Real.pi * Real.exp (77 / 100 : ℝ) ≤ (67851065448884627 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell615_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell615_endpointLower :
    (3919149171 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (123 / 320 : ℝ) (77 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (338831415133807 / 50000000000000 : ℝ) (Real.pi * Real.exp (123 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell615_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 100 : ℝ) - (123 / 640 : ℝ)) ≤
      (3649541992979 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell615_denomUpper
    linarith [hpThetaJensenCell615_product_upper]
  have hi : (1 / (3649541992979 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 100 : ℝ) - (123 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3649541992979 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3649541992979 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((123 / 640 : ℝ) - Real.pi * Real.exp (77 / 100 : ℝ)) := by
    rw [show (123 / 640 : ℝ) - Real.pi * Real.exp (77 / 100 : ℝ) =
      -(Real.pi * Real.exp (77 / 100 : ℝ) - (123 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (123 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (123 / 160 : ℝ)) := by
    have h := hpThetaJensenCell615_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3649541992979 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell615_endpointUpper :
    hpThetaJensenKernelEndpointUpper (123 / 320 : ℝ) (77 / 200 : ℝ) ≤ (1987751287 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 100 : ℝ)) (67851065448884627 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell615_product_upper
  have hD : (7235200821791 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (123 / 160 : ℝ) - (77 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell615_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell615_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (123 / 160 : ℝ) - (77 / 400 : ℝ)) ≤
      (1 / (7235200821791 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7235200821791 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 400 : ℝ) - Real.pi * Real.exp (123 / 160 : ℝ)) ≤
      (2 / (7235200821791 / 10000000000 : ℝ) : ℝ) := by
    rw [show (77 / 400 : ℝ) - Real.pi * Real.exp (123 / 160 : ℝ) =
      -(Real.pi * Real.exp (123 / 160 : ℝ) - (77 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67851065448884627 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67851065448884627 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell615_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (123 / 320 : ℝ) (77 / 200 : ℝ)) :
    (3919149171 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1987751287 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell615_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell615_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell616_leftExp :
    (21597662537 / 10000000000 : ℝ) ≤ Real.exp (77 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (77 / 100 : ℝ) (256088584509 / 250000000000 : ℝ)
    (21597662537 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell616_rightExp :
    Real.exp (617 / 800 : ℝ) ≤ (21624676497 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (617 / 800 : ℝ) (1024394352659 / 1000000000000 : ℝ)
    (21624676497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell616_denomUpper :
    Real.exp (66010932310239721 / 10000000000000000 : ℝ) ≤ (7358992575477 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (66010932310239721 / 10000000000000000 : ℝ) (38409450637
    / 31250000000 : ℝ) (7358992575477 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell616_denomLower :
    (1823626931169 / 2500000000 : ℝ) ≤ Real.exp (8240364855617363 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8240364855617363 / 1250000000000000 : ℝ) (76797775749 /
    62500000000 : ℝ) (1823626931169 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell616_product_lower :
    (8481380480617363 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (77 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell616_leftExp
    (by norm_num : (0 : ℝ) ≤ (21597662537 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell616_product_upper :
    Real.pi * Real.exp (617 / 800 : ℝ) ≤ (67935932310239721 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell616_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell616_endpointLower :
    (3898358049 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 200 : ℝ) (617 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8481380480617363 / 1250000000000000 : ℝ) (Real.pi * Real.exp (77 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell616_product_lower
  have hD : Real.exp (Real.pi * Real.exp (617 / 800 : ℝ) - (77 / 400 : ℝ)) ≤
      (7358992575477 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell616_denomUpper
    linarith [hpThetaJensenCell616_product_upper]
  have hi : (1 / (7358992575477 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (617 / 800 : ℝ) - (77 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7358992575477 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7358992575477 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((77 / 400 : ℝ) - Real.pi * Real.exp (617 / 800 : ℝ)) := by
    rw [show (77 / 400 : ℝ) - Real.pi * Real.exp (617 / 800 : ℝ) =
      -(Real.pi * Real.exp (617 / 800 : ℝ) - (77 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (77 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (77 / 100 : ℝ)) := by
    have h := hpThetaJensenCell616_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7358992575477 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell616_endpointUpper :
    hpThetaJensenKernelEndpointUpper (77 / 200 : ℝ) (617 / 1600 : ℝ) ≤ (1977226089 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (617 / 800 : ℝ)) (67935932310239721 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (617 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell616_product_upper
  have hD : (1823626931169 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (77 / 100 : ℝ) - (617 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell616_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell616_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (77 / 100 : ℝ) - (617 / 3200 : ℝ)) ≤
      (1 / (1823626931169 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1823626931169 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((617 / 3200 : ℝ) - Real.pi * Real.exp (77 / 100 : ℝ)) ≤
      (2 / (1823626931169 / 2500000000 : ℝ) : ℝ) := by
    rw [show (617 / 3200 : ℝ) - Real.pi * Real.exp (77 / 100 : ℝ) =
      -(Real.pi * Real.exp (77 / 100 : ℝ) - (617 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67935932310239721 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (67935932310239721 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell616_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (77 / 200 : ℝ) (617 / 1600 : ℝ)) :
    (3898358049 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1977226089 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell616_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell616_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell617_leftExp :
    (4324935299 / 2000000000 : ℝ) ≤ Real.exp (617 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (617 / 800 : ℝ) (512197176329 / 500000000000 : ℝ)
    (4324935299 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell617_rightExp :
    Real.exp (309 / 400 : ℝ) ≤ (5412931061 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (309 / 400 : ℝ) (204886873769 / 200000000000 : ℝ)
    (5412931061 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell617_denomUpper :
    Real.exp (16523195080720173 / 2500000000000000 : ℝ) ≤ (3709735817057 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (16523195080720173 / 2500000000000000 : ℝ) (153677104289
    / 125000000000 : ℝ) (3709735817057 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell617_denomLower :
    (7354378733669 / 10000000000 : ℝ) ≤ Real.exp (1650116516982001 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1650116516982001 / 250000000000000 : ℝ) (1229078331629 /
    1000000000000 : ℝ) (7354378733669 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell617_product_lower :
    (1698397766982001 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (617 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell617_leftExp
    (by norm_num : (0 : ℝ) ≤ (4324935299 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell617_product_upper :
    Real.pi * Real.exp (309 / 400 : ℝ) ≤ (17005226330720173 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell617_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell617_endpointLower :
    (775526771 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (617 / 1600 : ℝ) (309 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1698397766982001 / 250000000000000 : ℝ) (Real.pi * Real.exp (617 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell617_product_lower
  have hD : Real.exp (Real.pi * Real.exp (309 / 400 : ℝ) - (617 / 3200 : ℝ)) ≤
      (3709735817057 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell617_denomUpper
    linarith [hpThetaJensenCell617_product_upper]
  have hi : (1 / (3709735817057 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (309 / 400 : ℝ) - (617 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3709735817057 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3709735817057 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((617 / 3200 : ℝ) - Real.pi * Real.exp (309 / 400 : ℝ)) := by
    rw [show (617 / 3200 : ℝ) - Real.pi * Real.exp (309 / 400 : ℝ) =
      -(Real.pi * Real.exp (309 / 400 : ℝ) - (617 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (617 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (617 / 800 : ℝ)) := by
    have h := hpThetaJensenCell617_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3709735817057 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell617_endpointUpper :
    hpThetaJensenKernelEndpointUpper (617 / 1600 : ℝ) (309 / 800 : ℝ) ≤ (3933469309 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (309 / 400 : ℝ)) (17005226330720173 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (309 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell617_product_upper
  have hD : (7354378733669 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (617 / 800 : ℝ) - (309 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell617_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell617_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (617 / 800 : ℝ) - (309 / 1600 : ℝ)) ≤
      (1 / (7354378733669 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7354378733669 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((309 / 1600 : ℝ) - Real.pi * Real.exp (617 / 800 : ℝ)) ≤
      (2 / (7354378733669 / 10000000000 : ℝ) : ℝ) := by
    rw [show (309 / 1600 : ℝ) - Real.pi * Real.exp (617 / 800 : ℝ) =
      -(Real.pi * Real.exp (617 / 800 : ℝ) - (309 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17005226330720173 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (17005226330720173 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell617_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (617 / 1600 : ℝ) (309 / 800 : ℝ)) :
    (775526771 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3933469309 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell617_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell617_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell618_leftExp :
    (10825862121 / 5000000000 : ℝ) ≤ Real.exp (309 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (309 / 400 : ℝ) (256108592211 / 250000000000 : ℝ)
    (10825862121 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell618_rightExp :
    Real.exp (619 / 800 : ℝ) ≤ (10839402911 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (619 / 800 : ℝ) (204894877319 / 200000000000 : ℝ)
    (10839402911 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell618_denomUpper :
    Real.exp (33087367309377223 / 5000000000000000 : ℝ) ≤ (58441619049 / 78125000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33087367309377223 / 5000000000000000 : ℝ) (1229731737107
    / 1000000000000 : ℝ) (58441619049 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell618_denomLower :
    (1853704963477 / 2500000000 : ℝ) ≤ Real.exp (4130406791554579 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4130406791554579 / 625000000000000 : ℝ) (1229392739291 /
    1000000000000 : ℝ) (1853704963477 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell618_product_lower :
    (4251305229054579 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (309 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell618_leftExp
    (by norm_num : (0 : ℝ) ≤ (10825862121 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell618_product_upper :
    Real.pi * Real.exp (619 / 800 : ℝ) ≤ (34052992309377223 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell618_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell618_endpointLower :
    (482122081 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (309 / 800 : ℝ) (619 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4251305229054579 / 625000000000000 : ℝ) (Real.pi * Real.exp (309 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell618_product_lower
  have hD : Real.exp (Real.pi * Real.exp (619 / 800 : ℝ) - (309 / 1600 : ℝ)) ≤
      (58441619049 / 78125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell618_denomUpper
    linarith [hpThetaJensenCell618_product_upper]
  have hi : (1 / (58441619049 / 78125000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (619 / 800 : ℝ) - (309 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (58441619049 / 78125000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (58441619049 / 78125000 : ℝ) : ℝ) ≤
      2 * Real.exp ((309 / 1600 : ℝ) - Real.pi * Real.exp (619 / 800 : ℝ)) := by
    rw [show (309 / 1600 : ℝ) - Real.pi * Real.exp (619 / 800 : ℝ) =
      -(Real.pi * Real.exp (619 / 800 : ℝ) - (309 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (309 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (309 / 400 : ℝ)) := by
    have h := hpThetaJensenCell618_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (58441619049 / 78125000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell618_endpointUpper :
    hpThetaJensenKernelEndpointUpper (309 / 800 : ℝ) (619 / 1600 : ℝ) ≤ (3912554027 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (619 / 800 : ℝ)) (34052992309377223 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (619 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell618_product_upper
  have hD : (1853704963477 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (309 / 400 : ℝ) - (619 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell618_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell618_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (309 / 400 : ℝ) - (619 / 3200 : ℝ)) ≤
      (1 / (1853704963477 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1853704963477 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((619 / 3200 : ℝ) - Real.pi * Real.exp (309 / 400 : ℝ)) ≤
      (2 / (1853704963477 / 2500000000 : ℝ) : ℝ) := by
    rw [show (619 / 3200 : ℝ) - Real.pi * Real.exp (309 / 400 : ℝ) =
      -(Real.pi * Real.exp (309 / 400 : ℝ) - (619 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34052992309377223 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (34052992309377223 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell618_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (309 / 800 : ℝ) (619 / 1600 : ℝ)) :
    (482122081 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3912554027 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell618_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell618_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell619_leftExp :
    (1083940291 / 500000000 : ℝ) ≤ Real.exp (619 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (619 / 800 : ℝ) (512237193297 / 500000000000 : ℝ)
    (1083940291 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell619_rightExp :
    Real.exp (31 / 40 : ℝ) ≤ (21705921273 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 40 : ℝ) (1024514405907 / 1000000000000 : ℝ)
    (21705921273 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell619_denomUpper :
    Real.exp (66256795329807889 / 10000000000000000 : ℝ) ≤ (942770691873 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (66256795329807889 / 10000000000000000 : ℝ) (123004712961
    / 100000000000 : ℝ) (942770691873 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell619_denomLower :
    (7475837157791 / 10000000000 : ℝ) ≤ Real.exp (413552893335409 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (413552893335409 / 62500000000000 : ℝ) (122970763581 /
    100000000000 : ℝ) (7475837157791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell619_product_lower :
    (425662268335409 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (619 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell619_leftExp
    (by norm_num : (0 : ℝ) ≤ (1083940291 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell619_product_upper :
    Real.pi * Real.exp (31 / 40 : ℝ) ≤ (68191170329807889 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell619_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell619_endpointLower :
    (3836386487 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (619 / 1600 : ℝ) (31 / 80 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (425662268335409 / 62500000000000 : ℝ) (Real.pi * Real.exp (619 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell619_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 40 : ℝ) - (619 / 3200 : ℝ)) ≤
      (942770691873 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell619_denomUpper
    linarith [hpThetaJensenCell619_product_upper]
  have hi : (1 / (942770691873 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 40 : ℝ) - (619 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (942770691873 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (942770691873 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((619 / 3200 : ℝ) - Real.pi * Real.exp (31 / 40 : ℝ)) := by
    rw [show (619 / 3200 : ℝ) - Real.pi * Real.exp (31 / 40 : ℝ) =
      -(Real.pi * Real.exp (31 / 40 : ℝ) - (619 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (619 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (619 / 800 : ℝ)) := by
    have h := hpThetaJensenCell619_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (942770691873 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell619_endpointUpper :
    hpThetaJensenKernelEndpointUpper (619 / 1600 : ℝ) (31 / 80 : ℝ) ≤ (3891706391 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 40 : ℝ)) (68191170329807889 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell619_product_upper
  have hD : (7475837157791 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (619 / 800 : ℝ) - (31 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell619_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell619_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (619 / 800 : ℝ) - (31 / 160 : ℝ)) ≤
      (1 / (7475837157791 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7475837157791 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 160 : ℝ) - Real.pi * Real.exp (619 / 800 : ℝ)) ≤
      (2 / (7475837157791 / 10000000000 : ℝ) : ℝ) := by
    rw [show (31 / 160 : ℝ) - Real.pi * Real.exp (619 / 800 : ℝ) =
      -(Real.pi * Real.exp (619 / 800 : ℝ) - (31 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68191170329807889 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (68191170329807889 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell619_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (619 / 1600 : ℝ) (31 / 80 : ℝ)) :
    (3836386487 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3891706391 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell619_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell619_endpointUpper

def hpThetaJensenCellsBatch030Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1059750259 / 2500000000 : ℝ)
  | 1 => (2108607219 / 5000000000 : ℝ)
  | 2 => (2097746823 / 5000000000 : ℝ)
  | 3 => (1043459687 / 2500000000 : ℝ)
  | 4 => (4152249829 / 10000000000 : ℝ)
  | 5 => (4130726973 / 10000000000 : ℝ)
  | 6 => (2054635133 / 5000000000 : ℝ)
  | 7 => (817575957 / 2000000000 : ℝ)
  | 8 => (1016638903 / 2500000000 : ℝ)
  | 9 => (4045297821 / 10000000000 : ℝ)
  | 10 => (4024106487 / 10000000000 : ℝ)
  | 11 => (800596337 / 2000000000 : ℝ)
  | 12 => (995480871 / 2500000000 : ℝ)
  | 13 => (3960931953 / 10000000000 : ℝ)
  | 14 => (98500179 / 250000000 : ℝ)
  | 15 => (3919149171 / 10000000000 : ℝ)
  | 16 => (3898358049 / 10000000000 : ℝ)
  | 17 => (775526771 / 2000000000 : ℝ)
  | 18 => (482122081 / 1250000000 : ℝ)
  | 19 => (3836386487 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch030Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4299313763 / 10000000000 : ℝ)
  | 1 => (534657399 / 1250000000 : ℝ)
  | 2 => (1063817747 / 2500000000 : ℝ)
  | 3 => (2116674623 / 5000000000 : ℝ)
  | 4 => (1052873513 / 2500000000 : ℝ)
  | 5 => (523713187 / 1250000000 : ℝ)
  | 6 => (2083991829 / 5000000000 : ℝ)
  | 7 => (33170629 / 80000000 : ℝ)
  | 8 => (2062370237 / 5000000000 : ℝ)
  | 9 => (4103219287 / 10000000000 : ℝ)
  | 10 => (2040882571 / 5000000000 : ℝ)
  | 11 => (406037811 / 1000000000 : ℝ)
  | 12 => (4039058267 / 10000000000 : ℝ)
  | 13 => (803561137 / 2000000000 : ℝ)
  | 14 => (3996620431 / 10000000000 : ℝ)
  | 15 => (1987751287 / 5000000000 : ℝ)
  | 16 => (1977226089 / 5000000000 : ℝ)
  | 17 => (3933469309 / 10000000000 : ℝ)
  | 18 => (3912554027 / 10000000000 : ℝ)
  | 19 => (3891706391 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch030_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch030Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch030Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell600_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell601_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell602_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell603_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell604_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell605_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell606_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell607_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell608_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell609_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell610_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell611_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell612_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell613_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell614_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell615_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell616_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell617_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell618_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell619_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper] at h ⊢
    exact h

end HodgeProofHP
