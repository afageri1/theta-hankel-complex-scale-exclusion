import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell940_leftExp :
    (32381429437 / 10000000000 : ℝ) ≤ Real.exp (47 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 40 : ℝ) (1037401210713 / 1000000000000 : ℝ)
    (32381429437 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell940_rightExp :
    Real.exp (941 / 800 : ℝ) ≤ (6484386307 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (941 / 800 : ℝ) (1037441734991 / 1000000000000 : ℝ)
    (6484386307 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell940_denomUpper :
    Real.exp (19783802631367051 / 2000000000000000 : ℝ) ≤ (98848062513479 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19783802631367051 / 2000000000000000 : ℝ) (68111421899 /
    50000000000 : ℝ) (98848062513479 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell940_denomLower :
    (195134932496771 / 10000000000 : ℝ) ≤ Real.exp (12348576833480463 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12348576833480463 / 1250000000000000 : ℝ) (21276147647 /
    15625000000 : ℝ) (195134932496771 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell940_product_lower :
    (12716154958480463 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell940_leftExp
    (by norm_num : (0 : ℝ) ≤ (32381429437 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell940_product_upper :
    Real.pi * Real.exp (941 / 800 : ℝ) ≤ (20371302631367051 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell940_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell940_endpointLower :
    (89257183 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 80 : ℝ) (941 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12716154958480463 / 1250000000000000 : ℝ) (Real.pi * Real.exp (47 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell940_product_lower
  have hD : Real.exp (Real.pi * Real.exp (941 / 800 : ℝ) - (47 / 160 : ℝ)) ≤
      (98848062513479 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell940_denomUpper
    linarith [hpThetaJensenCell940_product_upper]
  have hi : (1 / (98848062513479 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (941 / 800 : ℝ) - (47 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (98848062513479 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (98848062513479 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 160 : ℝ) - Real.pi * Real.exp (941 / 800 : ℝ)) := by
    rw [show (47 / 160 : ℝ) - Real.pi * Real.exp (941 / 800 : ℝ) =
      -(Real.pi * Real.exp (941 / 800 : ℝ) - (47 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 40 : ℝ)) := by
    have h := hpThetaJensenCell940_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (98848062513479 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell940_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 80 : ℝ) (941 / 1600 : ℝ) ≤ (363654013 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (941 / 800 : ℝ)) (20371302631367051 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (941 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell940_product_upper
  have hD : (195134932496771 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 40 : ℝ) - (941 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell940_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell940_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 40 : ℝ) - (941 / 3200 : ℝ)) ≤
      (1 / (195134932496771 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (195134932496771 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((941 / 3200 : ℝ) - Real.pi * Real.exp (47 / 40 : ℝ)) ≤
      (2 / (195134932496771 / 10000000000 : ℝ) : ℝ) := by
    rw [show (941 / 3200 : ℝ) - Real.pi * Real.exp (47 / 40 : ℝ) =
      -(Real.pi * Real.exp (47 / 40 : ℝ) - (941 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20371302631367051 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (20371302631367051 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell940_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 80 : ℝ) (941 / 1600 : ℝ)) :
    (89257183 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (363654013 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell940_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell940_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell941_leftExp :
    (32421931533 / 10000000000 : ℝ) ≤ Real.exp (941 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (941 / 800 : ℝ) (103744173499 / 100000000000 : ℝ)
    (32421931533 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell941_rightExp :
    Real.exp (471 / 400 : ℝ) ≤ (32462484289 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (471 / 400 : ℝ) (20749645217 / 20000000000 : ℝ)
    (32462484289 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell941_denomUpper :
    Real.exp (99043288404932377 / 10000000000000000 : ℝ) ≤ (200168328390447 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (99043288404932377 / 10000000000000000 : ℝ) (681378787981
    / 500000000000 : ℝ) (200168328390447 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell941_denomLower :
    (19757196285419 / 1000000000 : ℝ) ≤ Real.exp (12364091341077567 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12364091341077567 / 1250000000000000 : ℝ) (1362201694171
    / 1000000000000 : ℝ) (19757196285419 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell941_product_lower :
    (12732060091077567 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (941 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell941_leftExp
    (by norm_num : (0 : ℝ) ≤ (32421931533 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell941_product_upper :
    Real.pi * Real.exp (471 / 400 : ℝ) ≤ (101983913404932377 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell941_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell941_endpointLower :
    (353578231 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (941 / 1600 : ℝ) (471 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12732060091077567 / 1250000000000000 : ℝ) (Real.pi * Real.exp (941 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell941_product_lower
  have hD : Real.exp (Real.pi * Real.exp (471 / 400 : ℝ) - (941 / 3200 : ℝ)) ≤
      (200168328390447 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell941_denomUpper
    linarith [hpThetaJensenCell941_product_upper]
  have hi : (1 / (200168328390447 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (471 / 400 : ℝ) - (941 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (200168328390447 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (200168328390447 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((941 / 3200 : ℝ) - Real.pi * Real.exp (471 / 400 : ℝ)) := by
    rw [show (941 / 3200 : ℝ) - Real.pi * Real.exp (471 / 400 : ℝ) =
      -(Real.pi * Real.exp (471 / 400 : ℝ) - (941 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (941 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (941 / 800 : ℝ)) := by
    have h := hpThetaJensenCell941_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (200168328390447 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell941_endpointUpper :
    hpThetaJensenKernelEndpointUpper (941 / 1600 : ℝ) (471 / 800 : ℝ) ≤ (360145101 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (471 / 400 : ℝ)) (101983913404932377 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (471 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell941_product_upper
  have hD : (19757196285419 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (941 / 800 : ℝ) - (471 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell941_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell941_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (941 / 800 : ℝ) - (471 / 1600 : ℝ)) ≤
      (1 / (19757196285419 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (19757196285419 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((471 / 1600 : ℝ) - Real.pi * Real.exp (941 / 800 : ℝ)) ≤
      (2 / (19757196285419 / 1000000000 : ℝ) : ℝ) := by
    rw [show (471 / 1600 : ℝ) - Real.pi * Real.exp (941 / 800 : ℝ) =
      -(Real.pi * Real.exp (941 / 800 : ℝ) - (471 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (101983913404932377 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (101983913404932377 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell941_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (941 / 1600 : ℝ) (471 / 800 : ℝ)) :
    (353578231 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (360145101 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell941_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell941_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell942_leftExp :
    (32462484287 / 10000000000 : ℝ) ≤ Real.exp (471 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (471 / 400 : ℝ) (1037482260849 / 1000000000000 : ℝ)
    (32462484287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell942_rightExp :
    Real.exp (943 / 800 : ℝ) ≤ (16251543883 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (943 / 800 : ℝ) (259380697073 / 250000000000 : ℝ)
    (16251543883 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell942_denomUpper :
    Real.exp (49583861502025619 / 5000000000000000 : ℝ) ≤ (202674676440367 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (49583861502025619 / 5000000000000000 : ℝ) (1363287598359
    / 1000000000000 : ℝ) (202674676440367 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell942_denomLower :
    (10002130637727 / 500000000 : ℝ) ≤ Real.exp (12379625742020613 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12379625742020613 / 1250000000000000 : ℝ) (1362730821593
    / 1000000000000 : ℝ) (10002130637727 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell942_product_lower :
    (12747985117020613 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (471 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell942_leftExp
    (by norm_num : (0 : ℝ) ≤ (32462484287 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell942_product_upper :
    Real.pi * Real.exp (943 / 800 : ℝ) ≤ (51055736502025619 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell942_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell942_endpointLower :
    (87538847 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (471 / 800 : ℝ) (943 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12747985117020613 / 1250000000000000 : ℝ) (Real.pi * Real.exp (471 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell942_product_lower
  have hD : Real.exp (Real.pi * Real.exp (943 / 800 : ℝ) - (471 / 1600 : ℝ)) ≤
      (202674676440367 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell942_denomUpper
    linarith [hpThetaJensenCell942_product_upper]
  have hi : (1 / (202674676440367 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (943 / 800 : ℝ) - (471 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (202674676440367 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (202674676440367 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((471 / 1600 : ℝ) - Real.pi * Real.exp (943 / 800 : ℝ)) := by
    rw [show (471 / 1600 : ℝ) - Real.pi * Real.exp (943 / 800 : ℝ) =
      -(Real.pi * Real.exp (943 / 800 : ℝ) - (471 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (471 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (471 / 400 : ℝ)) := by
    have h := hpThetaJensenCell942_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (202674676440367 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell942_endpointUpper :
    hpThetaJensenKernelEndpointUpper (471 / 800 : ℝ) (943 / 1600 : ℝ) ≤ (356664259 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (943 / 800 : ℝ)) (51055736502025619 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (943 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell942_product_upper
  have hD : (10002130637727 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (471 / 400 : ℝ) - (943 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell942_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell942_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (471 / 400 : ℝ) - (943 / 3200 : ℝ)) ≤
      (1 / (10002130637727 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10002130637727 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((943 / 3200 : ℝ) - Real.pi * Real.exp (471 / 400 : ℝ)) ≤
      (2 / (10002130637727 / 500000000 : ℝ) : ℝ) := by
    rw [show (943 / 3200 : ℝ) - Real.pi * Real.exp (471 / 400 : ℝ) =
      -(Real.pi * Real.exp (471 / 400 : ℝ) - (943 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51055736502025619 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (51055736502025619 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell942_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (471 / 800 : ℝ) (943 / 1600 : ℝ)) :
    (87538847 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (356664259 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell942_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell942_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell943_leftExp :
    (8125771941 / 2500000000 : ℝ) ≤ Real.exp (943 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (943 / 800 : ℝ) (1037522788291 / 1000000000000 : ℝ)
    (8125771941 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell943_rightExp :
    Real.exp (59 / 50 : ℝ) ≤ (3254374203 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 50 : ℝ) (518781658659 / 500000000000 : ℝ)
    (3254374203 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell943_denomUpper :
    Real.exp (9929231715525379 / 1000000000000000 : ℝ) ≤ (51303920303637 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9929231715525379 / 1000000000000000 : ℝ) (13638185069 /
    10000000000 : ℝ) (51303920303637 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell943_denomLower :
    (12659211616847 / 625000000 : ℝ) ≤ Real.exp (3098795015458759 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3098795015458759 / 312500000000000 : ℝ) (1363260833411 /
    1000000000000 : ℝ) (12659211616847 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell943_product_lower :
    (3190982515458759 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (943 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell943_leftExp
    (by norm_num : (0 : ℝ) ≤ (8125771941 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell943_product_upper :
    Real.pi * Real.exp (59 / 50 : ℝ) ≤ (10223919215525379 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell943_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell943_endpointLower :
    (346760037 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (943 / 1600 : ℝ) (59 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3190982515458759 / 312500000000000 : ℝ) (Real.pi * Real.exp (943 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell943_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 50 : ℝ) - (943 / 3200 : ℝ)) ≤
      (51303920303637 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell943_denomUpper
    linarith [hpThetaJensenCell943_product_upper]
  have hi : (1 / (51303920303637 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 50 : ℝ) - (943 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51303920303637 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51303920303637 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((943 / 3200 : ℝ) - Real.pi * Real.exp (59 / 50 : ℝ)) := by
    rw [show (943 / 3200 : ℝ) - Real.pi * Real.exp (59 / 50 : ℝ) =
      -(Real.pi * Real.exp (59 / 50 : ℝ) - (943 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (943 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (943 / 800 : ℝ)) := by
    have h := hpThetaJensenCell943_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51303920303637 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell943_endpointUpper :
    hpThetaJensenKernelEndpointUpper (943 / 1600 : ℝ) (59 / 100 : ℝ) ≤ (353211319 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 50 : ℝ)) (10223919215525379 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell943_product_upper
  have hD : (12659211616847 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (943 / 800 : ℝ) - (59 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell943_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell943_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (943 / 800 : ℝ) - (59 / 200 : ℝ)) ≤
      (1 / (12659211616847 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12659211616847 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 200 : ℝ) - Real.pi * Real.exp (943 / 800 : ℝ)) ≤
      (2 / (12659211616847 / 625000000 : ℝ) : ℝ) := by
    rw [show (59 / 200 : ℝ) - Real.pi * Real.exp (943 / 800 : ℝ) =
      -(Real.pi * Real.exp (943 / 800 : ℝ) - (59 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10223919215525379 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (10223919215525379 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell943_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (943 / 1600 : ℝ) (59 / 100 : ℝ)) :
    (346760037 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (353211319 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell943_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell943_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell944_leftExp :
    (8135935507 / 2500000000 : ℝ) ≤ Real.exp (59 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 50 : ℝ) (1037563317317 / 1000000000000 : ℝ)
    (8135935507 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell944_rightExp :
    Real.exp (189 / 160 : ℝ) ≤ (16292223571 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (189 / 160 : ℝ) (518801923963 / 500000000000 : ℝ)
    (16292223571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell944_denomUpper :
    Real.exp (49708535525088603 / 5000000000000000 : ℝ) ≤ (41558372557791 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49708535525088603 / 5000000000000000 : ℝ) (341087575819
    / 250000000000 : ℝ) (41558372557791 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell944_denomLower :
    (205086793924581 / 10000000000 : ℝ) ≤ Real.exp (3102688581413393 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3102688581413393 / 312500000000000 : ℝ) (340947932839 /
    250000000000 : ℝ) (205086793924581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell944_product_lower :
    (3194973737663393 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell944_leftExp
    (by norm_num : (0 : ℝ) ≤ (8135935507 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell944_product_upper :
    Real.pi * Real.exp (189 / 160 : ℝ) ≤ (51183535525088603 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell944_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell944_endpointLower :
    (343392017 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 100 : ℝ) (189 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3194973737663393 / 312500000000000 : ℝ) (Real.pi * Real.exp (59 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell944_product_lower
  have hD : Real.exp (Real.pi * Real.exp (189 / 160 : ℝ) - (59 / 200 : ℝ)) ≤
      (41558372557791 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell944_denomUpper
    linarith [hpThetaJensenCell944_product_upper]
  have hi : (1 / (41558372557791 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (189 / 160 : ℝ) - (59 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (41558372557791 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (41558372557791 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 200 : ℝ) - Real.pi * Real.exp (189 / 160 : ℝ)) := by
    rw [show (59 / 200 : ℝ) - Real.pi * Real.exp (189 / 160 : ℝ) =
      -(Real.pi * Real.exp (189 / 160 : ℝ) - (59 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 50 : ℝ)) := by
    have h := hpThetaJensenCell944_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (41558372557791 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell944_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 100 : ℝ) (189 / 320 : ℝ) ≤ (349786117 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (189 / 160 : ℝ)) (51183535525088603 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (189 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell944_product_upper
  have hD : (205086793924581 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 50 : ℝ) - (189 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell944_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell944_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 50 : ℝ) - (189 / 640 : ℝ)) ≤
      (1 / (205086793924581 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (205086793924581 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((189 / 640 : ℝ) - Real.pi * Real.exp (59 / 50 : ℝ)) ≤
      (2 / (205086793924581 / 10000000000 : ℝ) : ℝ) := by
    rw [show (189 / 640 : ℝ) - Real.pi * Real.exp (59 / 50 : ℝ) =
      -(Real.pi * Real.exp (59 / 50 : ℝ) - (189 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51183535525088603 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (51183535525088603 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell944_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 100 : ℝ) (189 / 320 : ℝ)) :
    (343392017 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (349786117 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell944_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell944_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell945_leftExp :
    (1629222357 / 500000000 : ℝ) ≤ Real.exp (189 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (189 / 160 : ℝ) (41504153917 / 40000000000 : ℝ)
    (1629222357 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell945_rightExp :
    Real.exp (473 / 400 : ℝ) ≤ (32625203169 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (473 / 400 : ℝ) (518822190059 / 500000000000 : ℝ)
    (32625203169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell945_denomUpper :
    Real.exp (99541984899308217 / 10000000000000000 : ℝ) ≤ (105201875006601 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (99541984899308217 / 10000000000000000 : ℝ)
    (1364882989263 / 1000000000000 : ℝ) (105201875006601 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell945_denomLower :
    (207661356663917 / 10000000000 : ℝ) ≤ Real.exp (621317427871543 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (621317427871543 / 62500000000000 : ℝ) (682161758559 /
    500000000000 : ℝ) (207661356663917 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell945_product_lower :
    (639793990371543 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (189 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell945_leftExp
    (by norm_num : (0 : ℝ) ≤ (1629222357 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell945_product_upper :
    Real.pi * Real.exp (473 / 400 : ℝ) ≤ (102495109899308217 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell945_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell945_endpointLower :
    (170025581 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (189 / 320 : ℝ) (473 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (639793990371543 / 62500000000000 : ℝ) (Real.pi * Real.exp (189 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell945_product_lower
  have hD : Real.exp (Real.pi * Real.exp (473 / 400 : ℝ) - (189 / 640 : ℝ)) ≤
      (105201875006601 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell945_denomUpper
    linarith [hpThetaJensenCell945_product_upper]
  have hi : (1 / (105201875006601 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (473 / 400 : ℝ) - (189 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (105201875006601 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (105201875006601 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((189 / 640 : ℝ) - Real.pi * Real.exp (473 / 400 : ℝ)) := by
    rw [show (189 / 640 : ℝ) - Real.pi * Real.exp (473 / 400 : ℝ) =
      -(Real.pi * Real.exp (473 / 400 : ℝ) - (189 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (189 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (189 / 160 : ℝ)) := by
    have h := hpThetaJensenCell945_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (105201875006601 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell945_endpointUpper :
    hpThetaJensenKernelEndpointUpper (189 / 320 : ℝ) (473 / 800 : ℝ) ≤ (43298561 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (473 / 400 : ℝ)) (102495109899308217 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (473 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell945_product_upper
  have hD : (207661356663917 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (189 / 160 : ℝ) - (473 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell945_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell945_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (189 / 160 : ℝ) - (473 / 1600 : ℝ)) ≤
      (1 / (207661356663917 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (207661356663917 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((473 / 1600 : ℝ) - Real.pi * Real.exp (189 / 160 : ℝ)) ≤
      (2 / (207661356663917 / 10000000000 : ℝ) : ℝ) := by
    rw [show (473 / 1600 : ℝ) - Real.pi * Real.exp (189 / 160 : ℝ) =
      -(Real.pi * Real.exp (189 / 160 : ℝ) - (473 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (102495109899308217 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (102495109899308217 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell945_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (189 / 320 : ℝ) (473 / 800 : ℝ)) :
    (170025581 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (43298561 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell945_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell945_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell946_leftExp :
    (32625203167 / 10000000000 : ℝ) ≤ Real.exp (473 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (473 / 400 : ℝ) (1037644380117 / 1000000000000 : ℝ)
    (32625203167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell946_rightExp :
    Real.exp (947 / 800 : ℝ) ≤ (8166502543 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (947 / 800 : ℝ) (518842456947 / 500000000000 : ℝ)
    (8166502543 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell946_denomUpper :
    Real.exp (24916764723570999 / 2500000000000000 : ℝ) ≤ (213051879854473 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (24916764723570999 / 2500000000000000 : ℝ) (1365416566557
    / 1000000000000 : ℝ) (213051879854473 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell946_denomLower :
    (210271602599759 / 10000000000 : ℝ) ≤ Real.exp (12441962783477733 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12441962783477733 / 1250000000000000 : ℝ) (170607024059
    / 125000000000 : ℝ) (210271602599759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell946_product_lower :
    (12811884658477733 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (473 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell946_leftExp
    (by norm_num : (0 : ℝ) ≤ (32625203167 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell946_product_upper :
    Real.pi * Real.exp (947 / 800 : ℝ) ≤ (25655827223570999 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell946_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell946_endpointLower :
    (336737313 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (473 / 800 : ℝ) (947 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12811884658477733 / 1250000000000000 : ℝ) (Real.pi * Real.exp (473 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell946_product_lower
  have hD : Real.exp (Real.pi * Real.exp (947 / 800 : ℝ) - (473 / 1600 : ℝ)) ≤
      (213051879854473 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell946_denomUpper
    linarith [hpThetaJensenCell946_product_upper]
  have hi : (1 / (213051879854473 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (947 / 800 : ℝ) - (473 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (213051879854473 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (213051879854473 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((473 / 1600 : ℝ) - Real.pi * Real.exp (947 / 800 : ℝ)) := by
    rw [show (473 / 1600 : ℝ) - Real.pi * Real.exp (947 / 800 : ℝ) =
      -(Real.pi * Real.exp (947 / 800 : ℝ) - (473 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (473 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (473 / 400 : ℝ)) := by
    have h := hpThetaJensenCell946_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (213051879854473 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell946_endpointUpper :
    hpThetaJensenKernelEndpointUpper (473 / 800 : ℝ) (947 / 1600 : ℝ) ≤ (343018267 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (947 / 800 : ℝ)) (25655827223570999 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (947 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell946_product_upper
  have hD : (210271602599759 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (473 / 400 : ℝ) - (947 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell946_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell946_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (473 / 400 : ℝ) - (947 / 3200 : ℝ)) ≤
      (1 / (210271602599759 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (210271602599759 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((947 / 3200 : ℝ) - Real.pi * Real.exp (473 / 400 : ℝ)) ≤
      (2 / (210271602599759 / 10000000000 : ℝ) : ℝ) := by
    rw [show (947 / 3200 : ℝ) - Real.pi * Real.exp (473 / 400 : ℝ) =
      -(Real.pi * Real.exp (473 / 400 : ℝ) - (947 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (25655827223570999 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (25655827223570999 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell946_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (473 / 800 : ℝ) (947 / 1600 : ℝ)) :
    (336737313 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (343018267 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell946_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell946_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell947_leftExp :
    (3266601017 / 1000000000 : ℝ) ≤ Real.exp (947 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (947 / 800 : ℝ) (1037684913893 / 1000000000000 : ℝ)
    (3266601017 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell947_rightExp :
    Real.exp (237 / 200 : ℝ) ≤ (6541373643 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (237 / 200 : ℝ) (259431362313 / 250000000000 : ℝ)
    (6541373643 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell947_denomUpper :
    Real.exp (19958458647233299 / 2000000000000000 : ℝ) ≤ (215736798160481 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (19958458647233299 / 2000000000000000 : ℝ) (1365951036901
    / 1000000000000 : ℝ) (215736798160481 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell947_denomLower :
    (21291806837649 / 1000000000 : ℝ) ≤ Real.exp (1245759702774883 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1245759702774883 / 125000000000000 : ℝ) (1365389759117 /
    1000000000000 : ℝ) (21291806837649 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell947_product_lower :
    (1282790952774883 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (947 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell947_leftExp
    (by norm_num : (0 : ℝ) ≤ (3266601017 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell947_product_upper :
    Real.pi * Real.exp (237 / 200 : ℝ) ≤ (20550333647233299 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell947_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell947_endpointLower :
    (166725153 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (947 / 1600 : ℝ) (237 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1282790952774883 / 125000000000000 : ℝ) (Real.pi * Real.exp (947 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell947_product_lower
  have hD : Real.exp (Real.pi * Real.exp (237 / 200 : ℝ) - (947 / 3200 : ℝ)) ≤
      (215736798160481 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell947_denomUpper
    linarith [hpThetaJensenCell947_product_upper]
  have hi : (1 / (215736798160481 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (237 / 200 : ℝ) - (947 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (215736798160481 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (215736798160481 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((947 / 3200 : ℝ) - Real.pi * Real.exp (237 / 200 : ℝ)) := by
    rw [show (947 / 3200 : ℝ) - Real.pi * Real.exp (237 / 200 : ℝ) =
      -(Real.pi * Real.exp (237 / 200 : ℝ) - (947 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (947 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (947 / 800 : ℝ)) := by
    have h := hpThetaJensenCell947_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (215736798160481 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell947_endpointUpper :
    hpThetaJensenKernelEndpointUpper (947 / 1600 : ℝ) (237 / 400 : ℝ) ≤ (339675291 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (237 / 200 : ℝ)) (20550333647233299 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (237 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell947_product_upper
  have hD : (21291806837649 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (947 / 800 : ℝ) - (237 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell947_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell947_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (947 / 800 : ℝ) - (237 / 800 : ℝ)) ≤
      (1 / (21291806837649 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (21291806837649 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((237 / 800 : ℝ) - Real.pi * Real.exp (947 / 800 : ℝ)) ≤
      (2 / (21291806837649 / 1000000000 : ℝ) : ℝ) := by
    rw [show (237 / 800 : ℝ) - Real.pi * Real.exp (947 / 800 : ℝ) =
      -(Real.pi * Real.exp (947 / 800 : ℝ) - (237 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (20550333647233299 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (20550333647233299 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell947_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (947 / 1600 : ℝ) (237 / 400 : ℝ)) :
    (166725153 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (339675291 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell947_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell947_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell948_leftExp :
    (32706868213 / 10000000000 : ℝ) ≤ Real.exp (237 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (237 / 200 : ℝ) (1037725449251 / 1000000000000 : ℝ)
    (32706868213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell948_rightExp :
    Real.exp (949 / 800 : ℝ) ≤ (32747777363 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (949 / 800 : ℝ) (518882993097 / 500000000000 : ℝ)
    (32747777363 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell948_denomUpper :
    Real.exp (99917688129159259 / 10000000000000000 : ℝ) ≤ (218459059647469 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (99917688129159259 / 10000000000000000 : ℝ)
    (1366486402051 / 1000000000000 : ℝ) (218459059647469 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell948_denomLower :
    (43120259896773 / 2000000000 : ℝ) ≤ Real.exp (12473251315376887 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12473251315376887 / 1250000000000000 : ℝ) (1365924218793
    / 1000000000000 : ℝ) (43120259896773 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell948_product_lower :
    (12843954440376887 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (237 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell948_leftExp
    (by norm_num : (0 : ℝ) ≤ (32706868213 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell948_product_upper :
    Real.pi * Real.exp (949 / 800 : ℝ) ≤ (102880188129159259 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell948_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell948_endpointLower :
    (16509499 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (237 / 400 : ℝ) (949 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12843954440376887 / 1250000000000000 : ℝ) (Real.pi * Real.exp (237 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell948_product_lower
  have hD : Real.exp (Real.pi * Real.exp (949 / 800 : ℝ) - (237 / 800 : ℝ)) ≤
      (218459059647469 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell948_denomUpper
    linarith [hpThetaJensenCell948_product_upper]
  have hi : (1 / (218459059647469 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (949 / 800 : ℝ) - (237 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (218459059647469 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (218459059647469 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((237 / 800 : ℝ) - Real.pi * Real.exp (949 / 800 : ℝ)) := by
    rw [show (237 / 800 : ℝ) - Real.pi * Real.exp (949 / 800 : ℝ) =
      -(Real.pi * Real.exp (949 / 800 : ℝ) - (237 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (237 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (237 / 200 : ℝ)) := by
    have h := hpThetaJensenCell948_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (218459059647469 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell948_endpointUpper :
    hpThetaJensenKernelEndpointUpper (237 / 400 : ℝ) (949 / 1600 : ℝ) ≤ (84089849 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (949 / 800 : ℝ)) (102880188129159259 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (949 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell948_product_upper
  have hD : (43120259896773 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (237 / 200 : ℝ) - (949 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell948_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell948_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (237 / 200 : ℝ) - (949 / 3200 : ℝ)) ≤
      (1 / (43120259896773 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (43120259896773 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((949 / 3200 : ℝ) - Real.pi * Real.exp (237 / 200 : ℝ)) ≤
      (2 / (43120259896773 / 2000000000 : ℝ) : ℝ) := by
    rw [show (949 / 3200 : ℝ) - Real.pi * Real.exp (237 / 200 : ℝ) =
      -(Real.pi * Real.exp (237 / 200 : ℝ) - (949 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (102880188129159259 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (102880188129159259 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell948_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (237 / 400 : ℝ) (949 / 1600 : ℝ)) :
    (16509499 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (84089849 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell948_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell948_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell949_leftExp :
    (32747777361 / 10000000000 : ℝ) ≤ Real.exp (949 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (949 / 800 : ℝ) (1037765986193 / 1000000000000 : ℝ)
    (32747777361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell949_rightExp :
    Real.exp (19 / 16 : ℝ) ≤ (409859221 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 16 : ℝ) (12972581559 / 12500000000 : ℝ)
    (409859221 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell949_denomUpper :
    Real.exp (1250540547179053 / 125000000000000 : ℝ) ≤ (221219227940819 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1250540547179053 / 125000000000000 : ℝ) (683511331877 /
    500000000000 : ℝ) (221219227940819 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell949_denomLower :
    (109160925147159 / 5000000000 : ℝ) ≤ Real.exp (12488925671887339 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12488925671887339 / 1250000000000000 : ℝ) (1366459573257
    / 1000000000000 : ℝ) (109160925147159 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell949_product_lower :
    (12860019421887339 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (949 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell949_leftExp
    (by norm_num : (0 : ℝ) ≤ (32747777361 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell949_product_upper :
    Real.pi * Real.exp (19 / 16 : ℝ) ≤ (1287610859679053 / 125000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell949_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell949_endpointLower :
    (326956173 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (949 / 1600 : ℝ) (19 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12860019421887339 / 1250000000000000 : ℝ) (Real.pi * Real.exp (949 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell949_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 16 : ℝ) - (949 / 3200 : ℝ)) ≤
      (221219227940819 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell949_denomUpper
    linarith [hpThetaJensenCell949_product_upper]
  have hi : (1 / (221219227940819 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 16 : ℝ) - (949 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (221219227940819 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (221219227940819 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((949 / 3200 : ℝ) - Real.pi * Real.exp (19 / 16 : ℝ)) := by
    rw [show (949 / 3200 : ℝ) - Real.pi * Real.exp (19 / 16 : ℝ) =
      -(Real.pi * Real.exp (19 / 16 : ℝ) - (949 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (949 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (949 / 800 : ℝ)) := by
    have h := hpThetaJensenCell949_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (221219227940819 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell949_endpointUpper :
    hpThetaJensenKernelEndpointUpper (949 / 1600 : ℝ) (19 / 32 : ℝ) ≤ (16653521 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 16 : ℝ)) (1287610859679053 / 125000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell949_product_upper
  have hD : (109160925147159 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (949 / 800 : ℝ) - (19 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell949_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell949_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (949 / 800 : ℝ) - (19 / 64 : ℝ)) ≤
      (1 / (109160925147159 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (109160925147159 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 64 : ℝ) - Real.pi * Real.exp (949 / 800 : ℝ)) ≤
      (2 / (109160925147159 / 5000000000 : ℝ) : ℝ) := by
    rw [show (19 / 64 : ℝ) - Real.pi * Real.exp (949 / 800 : ℝ) =
      -(Real.pi * Real.exp (949 / 800 : ℝ) - (19 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1287610859679053 / 125000000000000 : ℝ) ^ 2 - 6 *
      (1287610859679053 / 125000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell949_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (949 / 1600 : ℝ) (19 / 32 : ℝ)) :
    (326956173 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16653521 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell949_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell949_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell950_leftExp :
    (16394368839 / 5000000000 : ℝ) ≤ Real.exp (19 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 16 : ℝ) (1037806524719 / 1000000000000 : ℝ)
    (16394368839 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell950_rightExp :
    Real.exp (951 / 800 : ℝ) ≤ (32829749229 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (951 / 800 : ℝ) (1037847064829 / 1000000000000 : ℝ)
    (32829749229 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell950_denomUpper :
    Real.exp (100168960369581797 / 10000000000000000 : ℝ) ≤ (22401787572023 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (100168960369581797 / 10000000000000000 : ℝ)
    (1367559823747 / 1000000000000 : ℝ) (22401787572023 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell950_denomLower :
    (55270071019723 / 2500000000 : ℝ) ≤ Real.exp (6252310061206461 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6252310061206461 / 625000000000000 : ℝ) (10679654877 /
    7812500000 : ℝ) (55270071019723 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell950_product_lower :
    (6438052248706461 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell950_leftExp
    (by norm_num : (0 : ℝ) ≤ (16394368839 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell950_product_upper :
    Real.pi * Real.exp (951 / 800 : ℝ) ≤ (103137710369581797 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell950_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell950_endpointLower :
    (161874363 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 32 : ℝ) (951 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6438052248706461 / 625000000000000 : ℝ) (Real.pi * Real.exp (19 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell950_product_lower
  have hD : Real.exp (Real.pi * Real.exp (951 / 800 : ℝ) - (19 / 64 : ℝ)) ≤
      (22401787572023 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell950_denomUpper
    linarith [hpThetaJensenCell950_product_upper]
  have hi : (1 / (22401787572023 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (951 / 800 : ℝ) - (19 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (22401787572023 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (22401787572023 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 64 : ℝ) - Real.pi * Real.exp (951 / 800 : ℝ)) := by
    rw [show (19 / 64 : ℝ) - Real.pi * Real.exp (951 / 800 : ℝ) =
      -(Real.pi * Real.exp (951 / 800 : ℝ) - (19 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 16 : ℝ)) := by
    have h := hpThetaJensenCell950_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (22401787572023 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell950_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 32 : ℝ) (951 / 1600 : ℝ) ≤ (164904099 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (951 / 800 : ℝ)) (103137710369581797 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (951 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell950_product_upper
  have hD : (55270071019723 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 16 : ℝ) - (951 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell950_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell950_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 16 : ℝ) - (951 / 3200 : ℝ)) ≤
      (1 / (55270071019723 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (55270071019723 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((951 / 3200 : ℝ) - Real.pi * Real.exp (19 / 16 : ℝ)) ≤
      (2 / (55270071019723 / 2500000000 : ℝ) : ℝ) := by
    rw [show (951 / 3200 : ℝ) - Real.pi * Real.exp (19 / 16 : ℝ) =
      -(Real.pi * Real.exp (19 / 16 : ℝ) - (951 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (103137710369581797 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (103137710369581797 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell950_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 32 : ℝ) (951 / 1600 : ℝ)) :
    (161874363 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (164904099 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell950_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell950_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell951_leftExp :
    (32829749227 / 10000000000 : ℝ) ≤ Real.exp (951 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (951 / 800 : ℝ) (259461766207 / 250000000000 : ℝ)
    (32829749227 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell951_rightExp :
    Real.exp (119 / 100 : ℝ) ≤ (1314832483 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (119 / 100 : ℝ) (518943803261 / 500000000000 : ℝ)
    (1314832483 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell951_denomUpper :
    Real.exp (4011793524765419 / 400000000000000 : ℝ) ≤ (226855585074103 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4011793524765419 / 400000000000000 : ℝ) (273619576759 /
    200000000000 : ℝ) (226855585074103 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell951_denomLower :
    (111938586578631 / 5000000000 : ℝ) ≤ Real.exp (12520334691693673 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12520334691693673 / 1250000000000000 : ℝ) (1367532973527
    / 1000000000000 : ℝ) (111938586578631 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell951_product_lower :
    (12892209691693673 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (951 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell951_leftExp
    (by norm_num : (0 : ℝ) ≤ (32829749227 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell951_product_upper :
    Real.pi * Real.exp (119 / 100 : ℝ) ≤ (4130668524765419 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell951_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell951_endpointLower :
    (160283739 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (951 / 1600 : ℝ) (119 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12892209691693673 / 1250000000000000 : ℝ) (Real.pi * Real.exp (951 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell951_product_lower
  have hD : Real.exp (Real.pi * Real.exp (119 / 100 : ℝ) - (951 / 3200 : ℝ)) ≤
      (226855585074103 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell951_denomUpper
    linarith [hpThetaJensenCell951_product_upper]
  have hi : (1 / (226855585074103 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (119 / 100 : ℝ) - (951 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (226855585074103 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (226855585074103 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((951 / 3200 : ℝ) - Real.pi * Real.exp (119 / 100 : ℝ)) := by
    rw [show (951 / 3200 : ℝ) - Real.pi * Real.exp (119 / 100 : ℝ) =
      -(Real.pi * Real.exp (119 / 100 : ℝ) - (951 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (951 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (951 / 800 : ℝ)) := by
    have h := hpThetaJensenCell951_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (226855585074103 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell951_endpointUpper :
    hpThetaJensenKernelEndpointUpper (951 / 1600 : ℝ) (119 / 200 : ℝ) ≤ (326572571 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (119 / 100 : ℝ)) (4130668524765419 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (119 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell951_product_upper
  have hD : (111938586578631 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (951 / 800 : ℝ) - (119 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell951_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell951_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (951 / 800 : ℝ) - (119 / 400 : ℝ)) ≤
      (1 / (111938586578631 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (111938586578631 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((119 / 400 : ℝ) - Real.pi * Real.exp (951 / 800 : ℝ)) ≤
      (2 / (111938586578631 / 5000000000 : ℝ) : ℝ) := by
    rw [show (119 / 400 : ℝ) - Real.pi * Real.exp (951 / 800 : ℝ) =
      -(Real.pi * Real.exp (951 / 800 : ℝ) - (119 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4130668524765419 / 400000000000000 : ℝ) ^ 2 - 6 *
      (4130668524765419 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell951_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (951 / 1600 : ℝ) (119 / 200 : ℝ)) :
    (160283739 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (326572571 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell951_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell951_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell952_leftExp :
    (32870812073 / 10000000000 : ℝ) ≤ Real.exp (119 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (119 / 100 : ℝ) (1037887606521 / 1000000000000 : ℝ)
    (32870812073 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell952_rightExp :
    Real.exp (953 / 800 : ℝ) ≤ (32911926281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (953 / 800 : ℝ) (518964074899 / 500000000000 : ℝ)
    (32911926281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell952_denomUpper :
    Real.exp (100420877220905633 / 10000000000000000 : ℝ) ≤ (9189317896381 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (100420877220905633 / 10000000000000000 : ℝ)
    (1368636845643 / 1000000000000 : ℝ) (9189317896381 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell952_denomLower :
    (226713099262497 / 10000000000 : ℝ) ≤ Real.exp (12536069405255027 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12536069405255027 / 1250000000000000 : ℝ) (1368071022837
    / 1000000000000 : ℝ) (226713099262497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell952_product_lower :
    (12908335030255027 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (119 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell952_leftExp
    (by norm_num : (0 : ℝ) ≤ (32870812073 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell952_product_upper :
    Real.pi * Real.exp (953 / 800 : ℝ) ≤ (103395877220905633 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell952_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell952_endpointLower :
    (31741227 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (119 / 200 : ℝ) (953 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12908335030255027 / 1250000000000000 : ℝ) (Real.pi * Real.exp (119 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell952_product_lower
  have hD : Real.exp (Real.pi * Real.exp (953 / 800 : ℝ) - (119 / 400 : ℝ)) ≤
      (9189317896381 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell952_denomUpper
    linarith [hpThetaJensenCell952_product_upper]
  have hi : (1 / (9189317896381 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (953 / 800 : ℝ) - (119 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9189317896381 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9189317896381 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((119 / 400 : ℝ) - Real.pi * Real.exp (953 / 800 : ℝ)) := by
    rw [show (119 / 400 : ℝ) - Real.pi * Real.exp (953 / 800 : ℝ) =
      -(Real.pi * Real.exp (953 / 800 : ℝ) - (119 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (119 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (119 / 100 : ℝ)) := by
    have h := hpThetaJensenCell952_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9189317896381 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell952_endpointUpper :
    hpThetaJensenKernelEndpointUpper (119 / 200 : ℝ) (953 / 1600 : ℝ) ≤ (2586907 / 80000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (953 / 800 : ℝ)) (103395877220905633 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (953 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell952_product_upper
  have hD : (226713099262497 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (119 / 100 : ℝ) - (953 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell952_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell952_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (119 / 100 : ℝ) - (953 / 3200 : ℝ)) ≤
      (1 / (226713099262497 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (226713099262497 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((953 / 3200 : ℝ) - Real.pi * Real.exp (119 / 100 : ℝ)) ≤
      (2 / (226713099262497 / 10000000000 : ℝ) : ℝ) := by
    rw [show (953 / 3200 : ℝ) - Real.pi * Real.exp (119 / 100 : ℝ) =
      -(Real.pi * Real.exp (119 / 100 : ℝ) - (953 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (103395877220905633 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (103395877220905633 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell952_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (119 / 200 : ℝ) (953 / 1600 : ℝ)) :
    (31741227 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2586907 / 80000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell952_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell952_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell953_leftExp :
    (32911926279 / 10000000000 : ℝ) ≤ Real.exp (953 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (953 / 800 : ℝ) (1037928149797 / 1000000000000 : ℝ)
    (32911926279 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell953_rightExp :
    Real.exp (477 / 400 : ℝ) ≤ (4119136489 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (477 / 400 : ℝ) (1037968694659 / 1000000000000 : ℝ)
    (4119136489 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell953_denomUpper :
    Real.exp (12568384734886977 / 1250000000000000 : ℝ) ≤ (232650563863011 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (12568384734886977 / 1250000000000000 : ℝ) (1369176711063
    / 1000000000000 : ℝ) (232650563863011 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell953_denomLower :
    (22958865340881 / 1000000000 : ℝ) ≤ Real.exp (12551824287837021 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12551824287837021 / 1250000000000000 : ℝ) (1368609973927
    / 1000000000000 : ℝ) (22958865340881 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell953_product_lower :
    (12924480537837021 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (953 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell953_leftExp
    (by norm_num : (0 : ℝ) ≤ (32911926279 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell953_product_upper :
    Real.pi * Real.exp (477 / 400 : ℝ) ≤ (12940650359886977 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell953_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell953_endpointLower :
    (314282941 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (953 / 1600 : ℝ) (477 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12924480537837021 / 1250000000000000 : ℝ) (Real.pi * Real.exp (953 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell953_product_lower
  have hD : Real.exp (Real.pi * Real.exp (477 / 400 : ℝ) - (953 / 3200 : ℝ)) ≤
      (232650563863011 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell953_denomUpper
    linarith [hpThetaJensenCell953_product_upper]
  have hi : (1 / (232650563863011 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (477 / 400 : ℝ) - (953 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (232650563863011 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (232650563863011 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((953 / 3200 : ℝ) - Real.pi * Real.exp (477 / 400 : ℝ)) := by
    rw [show (953 / 3200 : ℝ) - Real.pi * Real.exp (477 / 400 : ℝ) =
      -(Real.pi * Real.exp (477 / 400 : ℝ) - (953 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (953 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (953 / 800 : ℝ)) := by
    have h := hpThetaJensenCell953_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (232650563863011 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell953_endpointUpper :
    hpThetaJensenKernelEndpointUpper (953 / 1600 : ℝ) (477 / 800 : ℝ) ≤ (6403609 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (477 / 400 : ℝ)) (12940650359886977 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (477 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell953_product_upper
  have hD : (22958865340881 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (953 / 800 : ℝ) - (477 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell953_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell953_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (953 / 800 : ℝ) - (477 / 1600 : ℝ)) ≤
      (1 / (22958865340881 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (22958865340881 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((477 / 1600 : ℝ) - Real.pi * Real.exp (953 / 800 : ℝ)) ≤
      (2 / (22958865340881 / 1000000000 : ℝ) : ℝ) := by
    rw [show (477 / 1600 : ℝ) - Real.pi * Real.exp (953 / 800 : ℝ) =
      -(Real.pi * Real.exp (953 / 800 : ℝ) - (477 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12940650359886977 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (12940650359886977 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell953_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (953 / 1600 : ℝ) (477 / 800 : ℝ)) :
    (314282941 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6403609 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell953_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell953_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell954_leftExp :
    (3295309191 / 1000000000 : ℝ) ≤ Real.exp (477 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (477 / 400 : ℝ) (518984347329 / 500000000000 : ℝ)
    (3295309191 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell954_rightExp :
    Real.exp (191 / 160 : ℝ) ≤ (32994309033 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (191 / 160 : ℝ) (1038009241103 / 1000000000000 : ℝ)
    (32994309033 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell954_denomUpper :
    Real.exp (100673440297909569 / 10000000000000000 : ℝ) ≤ (9424361813459 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (100673440297909569 / 10000000000000000 : ℝ)
    (1369717481829 / 1000000000000 : ℝ) (9424361813459 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell954_denomLower :
    (11625221817993 / 500000000 : ℝ) ≤ Real.exp (1256759936496509 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1256759936496509 / 125000000000000 : ℝ) (136914982857 /
    100000000000 : ℝ) (11625221817993 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell954_product_lower :
    (1294064623996509 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (477 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell954_leftExp
    (by norm_num : (0 : ℝ) ≤ (3295309191 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell954_product_upper :
    Real.pi * Real.exp (191 / 160 : ℝ) ≤ (103654690297909569 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell954_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell954_endpointLower :
    (62235867 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (477 / 800 : ℝ) (191 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1294064623996509 / 125000000000000 : ℝ) (Real.pi * Real.exp (477 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell954_product_lower
  have hD : Real.exp (Real.pi * Real.exp (191 / 160 : ℝ) - (477 / 1600 : ℝ)) ≤
      (9424361813459 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell954_denomUpper
    linarith [hpThetaJensenCell954_product_upper]
  have hi : (1 / (9424361813459 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (191 / 160 : ℝ) - (477 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9424361813459 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9424361813459 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((477 / 1600 : ℝ) - Real.pi * Real.exp (191 / 160 : ℝ)) := by
    rw [show (477 / 1600 : ℝ) - Real.pi * Real.exp (191 / 160 : ℝ) =
      -(Real.pi * Real.exp (191 / 160 : ℝ) - (477 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (477 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (477 / 400 : ℝ)) := by
    have h := hpThetaJensenCell954_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9424361813459 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell954_endpointUpper :
    hpThetaJensenKernelEndpointUpper (477 / 800 : ℝ) (191 / 320 : ℝ) ≤ (79255909 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (191 / 160 : ℝ)) (103654690297909569 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (191 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell954_product_upper
  have hD : (11625221817993 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (477 / 400 : ℝ) - (191 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell954_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell954_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (477 / 400 : ℝ) - (191 / 640 : ℝ)) ≤
      (1 / (11625221817993 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11625221817993 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((191 / 640 : ℝ) - Real.pi * Real.exp (477 / 400 : ℝ)) ≤
      (2 / (11625221817993 / 500000000 : ℝ) : ℝ) := by
    rw [show (191 / 640 : ℝ) - Real.pi * Real.exp (477 / 400 : ℝ) =
      -(Real.pi * Real.exp (477 / 400 : ℝ) - (191 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (103654690297909569 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (103654690297909569 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell954_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (477 / 800 : ℝ) (191 / 320 : ℝ)) :
    (62235867 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (79255909 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell954_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell954_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell955_leftExp :
    (3299430903 / 1000000000 : ℝ) ≤ Real.exp (191 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (191 / 160 : ℝ) (519004620551 / 500000000000 : ℝ)
    (3299430903 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell955_rightExp :
    Real.exp (239 / 200 : ℝ) ≤ (16517788853 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (239 / 200 : ℝ) (1038049789131 / 1000000000000 : ℝ)
    (16517788853 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell955_denomUpper :
    Real.exp (50399982336062829 / 5000000000000000 : ℝ) ≤ (238609012465053 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (50399982336062829 / 5000000000000000 : ℝ) (1370259159681
    / 1000000000000 : ℝ) (238609012465053 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell955_denomLower :
    (235461058578309 / 10000000000 : ℝ) ≤ Real.exp (1258339466177197 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1258339466177197 / 125000000000000 : ℝ) (136969058853 /
    100000000000 : ℝ) (235461058578309 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell955_product_lower :
    (1295683216177197 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (191 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell955_leftExp
    (by norm_num : (0 : ℝ) ≤ (3299430903 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell955_product_upper :
    Real.pi * Real.exp (239 / 200 : ℝ) ≤ (51892169836062829 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell955_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell955_endpointLower :
    (308101291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (191 / 320 : ℝ) (239 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1295683216177197 / 125000000000000 : ℝ) (Real.pi * Real.exp (191 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell955_product_lower
  have hD : Real.exp (Real.pi * Real.exp (239 / 200 : ℝ) - (191 / 640 : ℝ)) ≤
      (238609012465053 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell955_denomUpper
    linarith [hpThetaJensenCell955_product_upper]
  have hi : (1 / (238609012465053 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (239 / 200 : ℝ) - (191 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (238609012465053 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (238609012465053 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((191 / 640 : ℝ) - Real.pi * Real.exp (239 / 200 : ℝ)) := by
    rw [show (191 / 640 : ℝ) - Real.pi * Real.exp (239 / 200 : ℝ) =
      -(Real.pi * Real.exp (239 / 200 : ℝ) - (191 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (191 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (191 / 160 : ℝ)) := by
    have h := hpThetaJensenCell955_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (238609012465053 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell955_endpointUpper :
    hpThetaJensenKernelEndpointUpper (191 / 320 : ℝ) (239 / 400 : ℝ) ≤ (313892771 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (239 / 200 : ℝ)) (51892169836062829 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (239 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell955_product_upper
  have hD : (235461058578309 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (191 / 160 : ℝ) - (239 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell955_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell955_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (191 / 160 : ℝ) - (239 / 800 : ℝ)) ≤
      (1 / (235461058578309 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (235461058578309 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((239 / 800 : ℝ) - Real.pi * Real.exp (191 / 160 : ℝ)) ≤
      (2 / (235461058578309 / 10000000000 : ℝ) : ℝ) := by
    rw [show (239 / 800 : ℝ) - Real.pi * Real.exp (191 / 160 : ℝ) =
      -(Real.pi * Real.exp (191 / 160 : ℝ) - (239 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (51892169836062829 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (51892169836062829 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell955_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (191 / 320 : ℝ) (239 / 400 : ℝ)) :
    (308101291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (313892771 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell955_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell955_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell956_leftExp :
    (4129447213 / 1250000000 : ℝ) ≤ Real.exp (239 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (239 / 200 : ℝ) (103804978913 / 100000000000 : ℝ)
    (4129447213 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell956_rightExp :
    Real.exp (957 / 800 : ℝ) ≤ (33076897997 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (957 / 800 : ℝ) (519045169371 / 500000000000 : ℝ)
    (33076897997 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell956_denomUpper :
    Real.exp (100926651209089221 / 10000000000000000 : ℝ) ≤ (48330219256783 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (100926651209089221 / 10000000000000000 : ℝ)
    (274160349283 / 200000000000 : ℝ) (48330219256783 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell956_denomLower :
    (11922957025369 / 500000000 : ℝ) ≤ Real.exp (1574901275472887 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1574901275472887 / 156250000000000 : ℝ) (1370232255583 /
    1000000000000 : ℝ) (11922957025369 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell956_product_lower :
    (1621629791097887 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (239 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell956_leftExp
    (by norm_num : (0 : ℝ) ≤ (4129447213 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell956_product_upper :
    Real.pi * Real.exp (957 / 800 : ℝ) ≤ (103914151209089221 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell956_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell956_endpointLower :
    (305048653 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (239 / 400 : ℝ) (957 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1621629791097887 / 156250000000000 : ℝ) (Real.pi * Real.exp (239 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell956_product_lower
  have hD : Real.exp (Real.pi * Real.exp (957 / 800 : ℝ) - (239 / 800 : ℝ)) ≤
      (48330219256783 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell956_denomUpper
    linarith [hpThetaJensenCell956_product_upper]
  have hi : (1 / (48330219256783 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (957 / 800 : ℝ) - (239 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (48330219256783 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (48330219256783 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((239 / 800 : ℝ) - Real.pi * Real.exp (957 / 800 : ℝ)) := by
    rw [show (239 / 800 : ℝ) - Real.pi * Real.exp (957 / 800 : ℝ) =
      -(Real.pi * Real.exp (957 / 800 : ℝ) - (239 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (239 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (239 / 200 : ℝ)) := by
    have h := hpThetaJensenCell956_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (48330219256783 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell956_endpointUpper :
    hpThetaJensenKernelEndpointUpper (239 / 400 : ℝ) (957 / 1600 : ℝ) ≤ (310787697 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (957 / 800 : ℝ)) (103914151209089221 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (957 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell956_product_upper
  have hD : (11922957025369 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (239 / 200 : ℝ) - (957 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell956_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell956_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (239 / 200 : ℝ) - (957 / 3200 : ℝ)) ≤
      (1 / (11922957025369 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11922957025369 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((957 / 3200 : ℝ) - Real.pi * Real.exp (239 / 200 : ℝ)) ≤
      (2 / (11922957025369 / 500000000 : ℝ) : ℝ) := by
    rw [show (957 / 3200 : ℝ) - Real.pi * Real.exp (239 / 200 : ℝ) =
      -(Real.pi * Real.exp (239 / 200 : ℝ) - (957 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (103914151209089221 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (103914151209089221 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell956_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (239 / 400 : ℝ) (957 / 1600 : ℝ)) :
    (305048653 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (310787697 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell956_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell956_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell957_leftExp :
    (6615379599 / 2000000000 : ℝ) ≤ Real.exp (957 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (957 / 800 : ℝ) (1038090338741 / 1000000000000 : ℝ)
    (6615379599 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell957_rightExp :
    Real.exp (479 / 400 : ℝ) ≤ (8279567493 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (479 / 400 : ℝ) (519065444969 / 500000000000 : ℝ)
    (8279567493 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell957_denomUpper :
    Real.exp (25263375029036349 / 2500000000000000 : ℝ) ≤ (244735938101563 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (25263375029036349 / 2500000000000000 : ℝ) (1371345243827
    / 1000000000000 : ℝ) (244735938101563 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell957_denomLower :
    (241499312570813 / 10000000000 : ℝ) ≤ Real.exp (2523009203147701 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2523009203147701 / 250000000000000 : ℝ) (685387415743 /
    500000000000 : ℝ) (241499312570813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell957_product_lower :
    (2597852953147701 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (957 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell957_leftExp
    (by norm_num : (0 : ℝ) ≤ (6615379599 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell957_product_upper :
    Real.pi * Real.exp (479 / 400 : ℝ) ≤ (26011031279036349 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell957_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell957_endpointLower :
    (18876329 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (957 / 1600 : ℝ) (479 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2597852953147701 / 250000000000000 : ℝ) (Real.pi * Real.exp (957 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell957_product_lower
  have hD : Real.exp (Real.pi * Real.exp (479 / 400 : ℝ) - (957 / 3200 : ℝ)) ≤
      (244735938101563 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell957_denomUpper
    linarith [hpThetaJensenCell957_product_upper]
  have hi : (1 / (244735938101563 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (479 / 400 : ℝ) - (957 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (244735938101563 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (244735938101563 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((957 / 3200 : ℝ) - Real.pi * Real.exp (479 / 400 : ℝ)) := by
    rw [show (957 / 3200 : ℝ) - Real.pi * Real.exp (479 / 400 : ℝ) =
      -(Real.pi * Real.exp (479 / 400 : ℝ) - (957 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (957 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (957 / 800 : ℝ)) := by
    have h := hpThetaJensenCell957_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (244735938101563 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell957_endpointUpper :
    hpThetaJensenKernelEndpointUpper (957 / 1600 : ℝ) (479 / 800 : ℝ) ≤ (153854127 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (479 / 400 : ℝ)) (26011031279036349 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (479 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell957_product_upper
  have hD : (241499312570813 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (957 / 800 : ℝ) - (479 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell957_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell957_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (957 / 800 : ℝ) - (479 / 1600 : ℝ)) ≤
      (1 / (241499312570813 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (241499312570813 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((479 / 1600 : ℝ) - Real.pi * Real.exp (957 / 800 : ℝ)) ≤
      (2 / (241499312570813 / 10000000000 : ℝ) : ℝ) := by
    rw [show (479 / 1600 : ℝ) - Real.pi * Real.exp (957 / 800 : ℝ) =
      -(Real.pi * Real.exp (957 / 800 : ℝ) - (479 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26011031279036349 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (26011031279036349 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell957_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (957 / 1600 : ℝ) (479 / 800 : ℝ)) :
    (18876329 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (153854127 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell957_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell957_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell958_leftExp :
    (3311826997 / 1000000000 : ℝ) ≤ Real.exp (479 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (479 / 400 : ℝ) (1038130889937 / 1000000000000 : ℝ)
    (3311826997 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell958_rightExp :
    Real.exp (959 / 800 : ℝ) ≤ (16579846847 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (959 / 800 : ℝ) (519085721359 / 500000000000 : ℝ)
    (16579846847 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell958_denomUpper :
    Real.exp (50590255795607271 / 5000000000000000 : ℝ) ≤ (9914567579683 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (50590255795607271 / 5000000000000000 : ℝ) (1371889653681
    / 1000000000000 : ℝ) (9914567579683 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell958_denomLower :
    (48916443151339 / 2000000000 : ℝ) ≤ Real.exp (1263090212394903 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1263090212394903 / 125000000000000 : ℝ) (27426366361 /
    20000000000 : ℝ) (48916443151339 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell958_product_lower :
    (1300551149894903 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (479 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell958_leftExp
    (by norm_num : (0 : ℝ) ≤ (3311826997 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell958_product_upper :
    Real.pi * Real.exp (959 / 800 : ℝ) ≤ (52087130795607271 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell958_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell958_endpointLower :
    (59803793 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (479 / 800 : ℝ) (959 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1300551149894903 / 125000000000000 : ℝ) (Real.pi * Real.exp (479 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell958_product_lower
  have hD : Real.exp (Real.pi * Real.exp (959 / 800 : ℝ) - (479 / 1600 : ℝ)) ≤
      (9914567579683 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell958_denomUpper
    linarith [hpThetaJensenCell958_product_upper]
  have hi : (1 / (9914567579683 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (959 / 800 : ℝ) - (479 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9914567579683 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9914567579683 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((479 / 1600 : ℝ) - Real.pi * Real.exp (959 / 800 : ℝ)) := by
    rw [show (479 / 1600 : ℝ) - Real.pi * Real.exp (959 / 800 : ℝ) =
      -(Real.pi * Real.exp (959 / 800 : ℝ) - (479 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (479 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (479 / 400 : ℝ)) := by
    have h := hpThetaJensenCell958_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9914567579683 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell958_endpointUpper :
    hpThetaJensenKernelEndpointUpper (479 / 800 : ℝ) (959 / 1600 : ℝ) ≤ (304654283 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (959 / 800 : ℝ)) (52087130795607271 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (959 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell958_product_upper
  have hD : (48916443151339 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (479 / 400 : ℝ) - (959 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell958_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell958_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (479 / 400 : ℝ) - (959 / 3200 : ℝ)) ≤
      (1 / (48916443151339 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (48916443151339 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((959 / 3200 : ℝ) - Real.pi * Real.exp (479 / 400 : ℝ)) ≤
      (2 / (48916443151339 / 2000000000 : ℝ) : ℝ) := by
    rw [show (959 / 3200 : ℝ) - Real.pi * Real.exp (479 / 400 : ℝ) =
      -(Real.pi * Real.exp (479 / 400 : ℝ) - (959 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (52087130795607271 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (52087130795607271 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell958_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (479 / 800 : ℝ) (959 / 1600 : ℝ)) :
    (59803793 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (304654283 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell958_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell958_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell959_leftExp :
    (8289923423 / 2500000000 : ℝ) ≤ Real.exp (959 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (959 / 800 : ℝ) (1038171442717 / 1000000000000 : ℝ)
    (8289923423 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell959_rightExp :
    Real.exp (6 / 5 : ℝ) ≤ (8300292307 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6 / 5 : ℝ) (519105998541 / 500000000000 : ℝ)
    (8300292307 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell959_denomUpper :
    Real.exp (25326921459625051 / 2500000000000000 : ℝ) ≤ (125518256398873 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25326921459625051 / 2500000000000000 : ℝ) (686217488883
    / 500000000000 : ℝ) (125518256398873 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell959_denomLower :
    (247708501218167 / 10000000000 : ℝ) ≤ Real.exp (3161694638288677 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3161694638288677 / 312500000000000 : ℝ) (1371862717037 /
    1000000000000 : ℝ) (247708501218167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell959_product_lower :
    (3255444638288677 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (959 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell959_leftExp
    (by norm_num : (0 : ℝ) ≤ (8289923423 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell959_product_upper :
    Real.pi * Real.exp (6 / 5 : ℝ) ≤ (26076140209625051 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell959_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell959_endpointLower :
    (148020801 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (959 / 1600 : ℝ) (3 / 5 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3255444638288677 / 312500000000000 : ℝ) (Real.pi * Real.exp (959 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell959_product_lower
  have hD : Real.exp (Real.pi * Real.exp (6 / 5 : ℝ) - (959 / 3200 : ℝ)) ≤
      (125518256398873 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell959_denomUpper
    linarith [hpThetaJensenCell959_product_upper]
  have hi : (1 / (125518256398873 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (6 / 5 : ℝ) - (959 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (125518256398873 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (125518256398873 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((959 / 3200 : ℝ) - Real.pi * Real.exp (6 / 5 : ℝ)) := by
    rw [show (959 / 3200 : ℝ) - Real.pi * Real.exp (6 / 5 : ℝ) =
      -(Real.pi * Real.exp (6 / 5 : ℝ) - (959 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (959 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (959 / 800 : ℝ)) := by
    have h := hpThetaJensenCell959_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (125518256398873 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell959_endpointUpper :
    hpThetaJensenKernelEndpointUpper (959 / 1600 : ℝ) (3 / 5 : ℝ) ≤ (301625627 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (6 / 5 : ℝ)) (26076140209625051 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 5 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell959_product_upper
  have hD : (247708501218167 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (959 / 800 : ℝ) - (3 / 10 : ℝ)) := by
    apply le_trans hpThetaJensenCell959_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell959_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (959 / 800 : ℝ) - (3 / 10 : ℝ)) ≤
      (1 / (247708501218167 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (247708501218167 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 10 : ℝ) - Real.pi * Real.exp (959 / 800 : ℝ)) ≤
      (2 / (247708501218167 / 10000000000 : ℝ) : ℝ) := by
    rw [show (3 / 10 : ℝ) - Real.pi * Real.exp (959 / 800 : ℝ) =
      -(Real.pi * Real.exp (959 / 800 : ℝ) - (3 / 10 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26076140209625051 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (26076140209625051 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell959_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (959 / 1600 : ℝ) (3 / 5 : ℝ)) :
    (148020801 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (301625627 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell959_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell959_endpointUpper

def hpThetaJensenCellsBatch047Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (89257183 / 2500000000 : ℝ)
  | 1 => (353578231 / 10000000000 : ℝ)
  | 2 => (87538847 / 2500000000 : ℝ)
  | 3 => (346760037 / 10000000000 : ℝ)
  | 4 => (343392017 / 10000000000 : ℝ)
  | 5 => (170025581 / 5000000000 : ℝ)
  | 6 => (336737313 / 10000000000 : ℝ)
  | 7 => (166725153 / 5000000000 : ℝ)
  | 8 => (16509499 / 500000000 : ℝ)
  | 9 => (326956173 / 10000000000 : ℝ)
  | 10 => (161874363 / 5000000000 : ℝ)
  | 11 => (160283739 / 5000000000 : ℝ)
  | 12 => (31741227 / 1000000000 : ℝ)
  | 13 => (314282941 / 10000000000 : ℝ)
  | 14 => (62235867 / 2000000000 : ℝ)
  | 15 => (308101291 / 10000000000 : ℝ)
  | 16 => (305048653 / 10000000000 : ℝ)
  | 17 => (18876329 / 625000000 : ℝ)
  | 18 => (59803793 / 2000000000 : ℝ)
  | 19 => (148020801 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch047Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (363654013 / 10000000000 : ℝ)
  | 1 => (360145101 / 10000000000 : ℝ)
  | 2 => (356664259 / 10000000000 : ℝ)
  | 3 => (353211319 / 10000000000 : ℝ)
  | 4 => (349786117 / 10000000000 : ℝ)
  | 5 => (43298561 / 1250000000 : ℝ)
  | 6 => (343018267 / 10000000000 : ℝ)
  | 7 => (339675291 / 10000000000 : ℝ)
  | 8 => (84089849 / 2500000000 : ℝ)
  | 9 => (16653521 / 500000000 : ℝ)
  | 10 => (164904099 / 5000000000 : ℝ)
  | 11 => (326572571 / 10000000000 : ℝ)
  | 12 => (2586907 / 80000000 : ℝ)
  | 13 => (6403609 / 200000000 : ℝ)
  | 14 => (79255909 / 2500000000 : ℝ)
  | 15 => (313892771 / 10000000000 : ℝ)
  | 16 => (310787697 / 10000000000 : ℝ)
  | 17 => (153854127 / 5000000000 : ℝ)
  | 18 => (304654283 / 10000000000 : ℝ)
  | 19 => (301625627 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch047_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch047Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch047Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell940_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell941_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell942_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell943_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell944_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell945_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell946_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell947_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell948_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell949_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell950_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell951_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell952_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell953_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell954_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell955_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell956_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell957_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell958_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell959_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper] at h ⊢
    exact h

end HodgeProofHP
