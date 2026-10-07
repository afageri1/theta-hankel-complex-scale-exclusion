import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell240_leftExp :
    (539943523 / 400000000 : ℝ) ≤ Real.exp (3 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 10 : ℝ) (252354770741 / 250000000000 : ℝ) (539943523
    / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell240_rightExp :
    Real.exp (241 / 800 : ℝ) ≤ (6757735931 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (241 / 800 : ℝ) (126182314271 / 125000000000 : ℝ)
    (6757735931 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell240_denomUpper :
    Real.exp (20855055896678083 / 5000000000000000 : ℝ) ≤ (647809241321 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20855055896678083 / 5000000000000000 : ℝ) (227844064173
    / 200000000000 : ℝ) (647809241321 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell240_denomLower :
    (644180021647 / 10000000000 : ℝ) ≤ Real.exp (208269656538577 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (208269656538577 / 50000000000000 : ℝ) (284755083081 /
    250000000000 : ℝ) (644180021647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell240_product_lower :
    (212035281538577 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell240_leftExp
    (by norm_num : (0 : ℝ) ≤ (539943523 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell240_product_upper :
    Real.pi * Real.exp (241 / 800 : ℝ) ≤ (21230055896678083 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell240_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell240_endpointLower :
    (14353022537 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 20 : ℝ) (241 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (212035281538577 / 50000000000000 : ℝ) (Real.pi * Real.exp (3 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell240_product_lower
  have hD : Real.exp (Real.pi * Real.exp (241 / 800 : ℝ) - (3 / 40 : ℝ)) ≤
      (647809241321 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell240_denomUpper
    linarith [hpThetaJensenCell240_product_upper]
  have hi : (1 / (647809241321 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (241 / 800 : ℝ) - (3 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (647809241321 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (647809241321 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 40 : ℝ) - Real.pi * Real.exp (241 / 800 : ℝ)) := by
    rw [show (3 / 40 : ℝ) - Real.pi * Real.exp (241 / 800 : ℝ) =
      -(Real.pi * Real.exp (241 / 800 : ℝ) - (3 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 10 : ℝ)) := by
    have h := hpThetaJensenCell240_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (647809241321 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell240_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 20 : ℝ) (241 / 1600 : ℝ) ≤ (3629513379 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (241 / 800 : ℝ)) (21230055896678083 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (241 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell240_product_upper
  have hD : (644180021647 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 10 : ℝ) - (241 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell240_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell240_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 10 : ℝ) - (241 / 3200 : ℝ)) ≤
      (1 / (644180021647 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (644180021647 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((241 / 3200 : ℝ) - Real.pi * Real.exp (3 / 10 : ℝ)) ≤
      (2 / (644180021647 / 10000000000 : ℝ) : ℝ) := by
    rw [show (241 / 3200 : ℝ) - Real.pi * Real.exp (3 / 10 : ℝ) =
      -(Real.pi * Real.exp (3 / 10 : ℝ) - (241 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21230055896678083 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21230055896678083 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell240_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 20 : ℝ) (241 / 1600 : ℝ)) :
    (14353022537 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3629513379 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell240_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell240_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell241_leftExp :
    (675773593 / 500000000 : ℝ) ≤ Real.exp (241 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (241 / 800 : ℝ) (1009458514167 / 1000000000000 : ℝ)
    (675773593 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell241_rightExp :
    Real.exp (121 / 400 : ℝ) ≤ (2706475353 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (121 / 400 : ℝ) (1009497946911 / 1000000000000 : ℝ)
    (2706475353 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell241_denomUpper :
    Real.exp (8352019023657329 / 2000000000000000 : ℝ) ≤ (32552765651 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8352019023657329 / 2000000000000000 : ℝ) (569699139287 /
    500000000000 : ℝ) (32552765651 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell241_denomLower :
    (647403611621 / 10000000000 : ℝ) ≤ Real.exp (260649051697507 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (260649051697507 / 62500000000000 : ℝ) (1139198022547 /
    1000000000000 : ℝ) (647403611621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell241_product_lower :
    (265375614197507 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (241 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell241_leftExp
    (by norm_num : (0 : ℝ) ≤ (675773593 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell241_product_upper :
    Real.pi * Real.exp (121 / 400 : ℝ) ≤ (8502644023657329 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell241_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell241_endpointLower :
    (3581749347 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (241 / 1600 : ℝ) (121 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (265375614197507 / 62500000000000 : ℝ) (Real.pi * Real.exp (241 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell241_product_lower
  have hD : Real.exp (Real.pi * Real.exp (121 / 400 : ℝ) - (241 / 3200 : ℝ)) ≤
      (32552765651 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell241_denomUpper
    linarith [hpThetaJensenCell241_product_upper]
  have hi : (1 / (32552765651 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (121 / 400 : ℝ) - (241 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32552765651 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32552765651 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((241 / 3200 : ℝ) - Real.pi * Real.exp (121 / 400 : ℝ)) := by
    rw [show (241 / 3200 : ℝ) - Real.pi * Real.exp (121 / 400 : ℝ) =
      -(Real.pi * Real.exp (121 / 400 : ℝ) - (241 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (241 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (241 / 800 : ℝ)) := by
    have h := hpThetaJensenCell241_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32552765651 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell241_endpointUpper :
    hpThetaJensenKernelEndpointUpper (241 / 1600 : ℝ) (121 / 800 : ℝ) ≤ (14491806169 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (121 / 400 : ℝ)) (8502644023657329 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (121 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell241_product_upper
  have hD : (647403611621 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (241 / 800 : ℝ) - (121 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell241_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell241_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (241 / 800 : ℝ) - (121 / 1600 : ℝ)) ≤
      (1 / (647403611621 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (647403611621 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((121 / 1600 : ℝ) - Real.pi * Real.exp (241 / 800 : ℝ)) ≤
      (2 / (647403611621 / 10000000000 : ℝ) : ℝ) := by
    rw [show (121 / 1600 : ℝ) - Real.pi * Real.exp (241 / 800 : ℝ) =
      -(Real.pi * Real.exp (241 / 800 : ℝ) - (121 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8502644023657329 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (8502644023657329 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell241_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (241 / 1600 : ℝ) (121 / 800 : ℝ)) :
    (3581749347 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14491806169 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell241_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell241_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell242_leftExp :
    (13532376763 / 10000000000 : ℝ) ≤ Real.exp (121 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (121 / 400 : ℝ) (100949794691 / 100000000000 : ℝ)
    (13532376763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell242_rightExp :
    Real.exp (243 / 800 : ℝ) ≤ (13549302813 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (243 / 800 : ℝ) (201907476239 / 200000000000 : ℝ)
    (13549302813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell242_denomUpper :
    Real.exp (41810144872201109 / 10000000000000000 : ℝ) ≤ (32716099843 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41810144872201109 / 10000000000000000 : ℝ)
    (1139576500647 / 1000000000000 : ℝ) (32716099843 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell242_denomLower :
    (8133095621 / 125000000 : ℝ) ≤ Real.exp (5219228947453337 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5219228947453337 / 1250000000000000 : ℝ) (1139375976713
    / 1000000000000 : ℝ) (8133095621 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell242_product_lower :
    (5314150822453337 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (121 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell242_leftExp
    (by norm_num : (0 : ℝ) ≤ (13532376763 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell242_product_upper :
    Real.pi * Real.exp (243 / 800 : ℝ) ≤ (42566394872201109 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell242_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell242_endpointLower :
    (2860181111 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (121 / 800 : ℝ) (243 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5314150822453337 / 1250000000000000 : ℝ) (Real.pi * Real.exp (121 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell242_product_lower
  have hD : Real.exp (Real.pi * Real.exp (243 / 800 : ℝ) - (121 / 1600 : ℝ)) ≤
      (32716099843 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell242_denomUpper
    linarith [hpThetaJensenCell242_product_upper]
  have hi : (1 / (32716099843 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (243 / 800 : ℝ) - (121 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32716099843 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32716099843 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((121 / 1600 : ℝ) - Real.pi * Real.exp (243 / 800 : ℝ)) := by
    rw [show (121 / 1600 : ℝ) - Real.pi * Real.exp (243 / 800 : ℝ) =
      -(Real.pi * Real.exp (243 / 800 : ℝ) - (121 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (121 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (121 / 400 : ℝ)) := by
    have h := hpThetaJensenCell242_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32716099843 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell242_endpointUpper :
    hpThetaJensenKernelEndpointUpper (121 / 800 : ℝ) (243 / 1600 : ℝ) ≤ (2893098253 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (243 / 800 : ℝ)) (42566394872201109 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (243 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell242_product_upper
  have hD : (8133095621 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (121 / 400 : ℝ) - (243 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell242_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell242_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (121 / 400 : ℝ) - (243 / 3200 : ℝ)) ≤
      (1 / (8133095621 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8133095621 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((243 / 3200 : ℝ) - Real.pi * Real.exp (121 / 400 : ℝ)) ≤
      (2 / (8133095621 / 125000000 : ℝ) : ℝ) := by
    rw [show (243 / 3200 : ℝ) - Real.pi * Real.exp (121 / 400 : ℝ) =
      -(Real.pi * Real.exp (121 / 400 : ℝ) - (243 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42566394872201109 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42566394872201109 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell242_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (121 / 800 : ℝ) (243 / 1600 : ℝ)) :
    (2860181111 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2893098253 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell242_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell242_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell243_leftExp :
    (13549302811 / 10000000000 : ℝ) ≤ Real.exp (243 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (243 / 800 : ℝ) (504768690597 / 500000000000 : ℝ)
    (13549302811 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell243_rightExp :
    Real.exp (61 / 200 : ℝ) ≤ (13566250031 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 200 : ℝ) (1009576817019 / 1000000000000 : ℝ)
    (13566250031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell243_denomUpper :
    Real.exp (41860261133639383 / 10000000000000000 : ℝ) ≤ (328804722467 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41860261133639383 / 10000000000000000 : ℝ)
    (1139754987479 / 1000000000000 : ℝ) (328804722467 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell243_denomLower :
    (653912286947 / 10000000000 : ℝ) ≤ Real.exp (5225485164576889 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5225485164576889 / 1250000000000000 : ℝ) (1139554195237
    / 1000000000000 : ℝ) (653912286947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell243_product_lower :
    (5320797664576889 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (243 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell243_leftExp
    (by norm_num : (0 : ℝ) ≤ (13549302811 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell243_product_upper :
    Real.pi * Real.exp (61 / 200 : ℝ) ≤ (42619636133639383 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell243_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell243_endpointLower :
    (14274747513 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (243 / 1600 : ℝ) (61 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5320797664576889 / 1250000000000000 : ℝ) (Real.pi * Real.exp (243 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell243_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 200 : ℝ) - (243 / 3200 : ℝ)) ≤
      (328804722467 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell243_denomUpper
    linarith [hpThetaJensenCell243_product_upper]
  have hi : (1 / (328804722467 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 200 : ℝ) - (243 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (328804722467 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (328804722467 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((243 / 3200 : ℝ) - Real.pi * Real.exp (61 / 200 : ℝ)) := by
    rw [show (243 / 3200 : ℝ) - Real.pi * Real.exp (61 / 200 : ℝ) =
      -(Real.pi * Real.exp (61 / 200 : ℝ) - (243 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (243 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (243 / 800 : ℝ)) := by
    have h := hpThetaJensenCell243_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (328804722467 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell243_endpointUpper :
    hpThetaJensenKernelEndpointUpper (243 / 1600 : ℝ) (61 / 400 : ℝ) ≤ (14439109269 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 200 : ℝ)) (42619636133639383 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell243_product_upper
  have hD : (653912286947 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (243 / 800 : ℝ) - (61 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell243_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell243_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (243 / 800 : ℝ) - (61 / 800 : ℝ)) ≤
      (1 / (653912286947 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (653912286947 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 800 : ℝ) - Real.pi * Real.exp (243 / 800 : ℝ)) ≤
      (2 / (653912286947 / 10000000000 : ℝ) : ℝ) := by
    rw [show (61 / 800 : ℝ) - Real.pi * Real.exp (243 / 800 : ℝ) =
      -(Real.pi * Real.exp (243 / 800 : ℝ) - (61 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42619636133639383 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42619636133639383 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell243_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (243 / 1600 : ℝ) (61 / 400 : ℝ)) :
    (14274747513 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14439109269 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell243_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell243_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell244_leftExp :
    (13566250029 / 10000000000 : ℝ) ≤ Real.exp (61 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 200 : ℝ) (504788408509 / 500000000000 : ℝ)
    (13566250029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell244_rightExp :
    Real.exp (49 / 160 : ℝ) ≤ (13583218447 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 160 : ℝ) (63101015899 / 62500000000 : ℝ)
    (13583218447 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell244_denomUpper :
    Real.exp (41910443990566071 / 10000000000000000 : ℝ) ≤ (330458905609 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41910443990566071 / 10000000000000000 : ℝ)
    (1139933739499 / 1000000000000 : ℝ) (330458905609 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell244_denomLower :
    (8214970943 / 125000000 : ℝ) ≤ Real.exp (5231749695138271 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5231749695138271 / 1250000000000000 : ℝ) (227946535703 /
    200000000000 : ℝ) (8214970943 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell244_product_lower :
    (5327452820138271 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell244_leftExp
    (by norm_num : (0 : ℝ) ≤ (13566250029 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell244_product_upper :
    Real.pi * Real.exp (49 / 160 : ℝ) ≤ (42672943990566071 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell244_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell244_endpointLower :
    (356213093 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 400 : ℝ) (49 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5327452820138271 / 1250000000000000 : ℝ) (Real.pi * Real.exp (61 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell244_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 160 : ℝ) - (61 / 800 : ℝ)) ≤
      (330458905609 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell244_denomUpper
    linarith [hpThetaJensenCell244_product_upper]
  have hi : (1 / (330458905609 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 160 : ℝ) - (61 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (330458905609 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (330458905609 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 800 : ℝ) - Real.pi * Real.exp (49 / 160 : ℝ)) := by
    rw [show (61 / 800 : ℝ) - Real.pi * Real.exp (49 / 160 : ℝ) =
      -(Real.pi * Real.exp (49 / 160 : ℝ) - (61 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 200 : ℝ)) := by
    have h := hpThetaJensenCell244_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (330458905609 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell244_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 400 : ℝ) (49 / 320 : ℝ) ≤ (14412660661 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 160 : ℝ)) (42672943990566071 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell244_product_upper
  have hD : (8214970943 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 200 : ℝ) - (49 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell244_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell244_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 200 : ℝ) - (49 / 640 : ℝ)) ≤
      (1 / (8214970943 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8214970943 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 640 : ℝ) - Real.pi * Real.exp (61 / 200 : ℝ)) ≤
      (2 / (8214970943 / 125000000 : ℝ) : ℝ) := by
    rw [show (49 / 640 : ℝ) - Real.pi * Real.exp (61 / 200 : ℝ) =
      -(Real.pi * Real.exp (61 / 200 : ℝ) - (49 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42672943990566071 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42672943990566071 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell244_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 400 : ℝ) (49 / 320 : ℝ)) :
    (356213093 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14412660661 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell244_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell244_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell245_leftExp :
    (2716643689 / 2000000000 : ℝ) ≤ Real.exp (49 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 160 : ℝ) (1009616254383 / 1000000000000 : ℝ)
    (2716643689 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell245_rightExp :
    Real.exp (123 / 400 : ℝ) ≤ (6800104043 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (123 / 400 : ℝ) (1009655693289 / 1000000000000 : ℝ)
    (6800104043 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell245_denomUpper :
    Real.exp (20980346760760499 / 5000000000000000 : ℝ) ≤ (166061812591 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20980346760760499 / 5000000000000000 : ℝ) (71257047319 /
    62500000000 : ℝ) (166061812591 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell245_denomLower :
    (660503969037 / 10000000000 : ℝ) ≤ Real.exp (1047604510026611 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1047604510026611 / 250000000000000 : ℝ) (35622232093 /
    31250000000 : ℝ) (660503969037 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell245_product_lower :
    (1066823260026611 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell245_leftExp
    (by norm_num : (0 : ℝ) ≤ (2716643689 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell245_product_upper :
    Real.pi * Real.exp (123 / 400 : ℝ) ≤ (21363159260760499 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell245_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell245_endpointLower :
    (2844446931 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 320 : ℝ) (123 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1066823260026611 / 250000000000000 : ℝ) (Real.pi * Real.exp (49 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell245_product_lower
  have hD : Real.exp (Real.pi * Real.exp (123 / 400 : ℝ) - (49 / 640 : ℝ)) ≤
      (166061812591 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell245_denomUpper
    linarith [hpThetaJensenCell245_product_upper]
  have hi : (1 / (166061812591 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (123 / 400 : ℝ) - (49 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (166061812591 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (166061812591 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 640 : ℝ) - Real.pi * Real.exp (123 / 400 : ℝ)) := by
    rw [show (49 / 640 : ℝ) - Real.pi * Real.exp (123 / 400 : ℝ) =
      -(Real.pi * Real.exp (123 / 400 : ℝ) - (49 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 160 : ℝ)) := by
    have h := hpThetaJensenCell245_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (166061812591 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell245_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 320 : ℝ) (123 / 800 : ℝ) ≤ (899134119 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (123 / 400 : ℝ)) (21363159260760499 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (123 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell245_product_upper
  have hD : (660503969037 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 160 : ℝ) - (123 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell245_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell245_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 160 : ℝ) - (123 / 1600 : ℝ)) ≤
      (1 / (660503969037 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (660503969037 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((123 / 1600 : ℝ) - Real.pi * Real.exp (49 / 160 : ℝ)) ≤
      (2 / (660503969037 / 10000000000 : ℝ) : ℝ) := by
    rw [show (123 / 1600 : ℝ) - Real.pi * Real.exp (49 / 160 : ℝ) =
      -(Real.pi * Real.exp (49 / 160 : ℝ) - (123 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21363159260760499 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21363159260760499 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell245_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 320 : ℝ) (123 / 800 : ℝ)) :
    (2844446931 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (899134119 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell245_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell245_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell246_leftExp :
    (3400052021 / 2500000000 : ℝ) ≤ Real.exp (123 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (123 / 400 : ℝ) (126206961661 / 125000000000 : ℝ)
    (3400052021 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell246_rightExp :
    Real.exp (247 / 800 : ℝ) ≤ (425538093 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (247 / 800 : ℝ) (201939026747 / 200000000000 : ℝ)
    (425538093 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell246_denomUpper :
    Real.exp (1312844056702149 / 312500000000000 : ℝ) ≤ (667597918877 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1312844056702149 / 312500000000000 : ℝ) (570146020361 /
    500000000000 : ℝ) (667597918877 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell246_denomLower :
    (26553252891 / 400000000 : ℝ) ≤ Real.exp (1311075934844679 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1311075934844679 / 312500000000000 : ℝ) (142511305127 /
    125000000000 : ℝ) (26553252891 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell246_product_lower :
    (1335197028594679 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (123 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell246_leftExp
    (by norm_num : (0 : ℝ) ≤ (3400052021 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell246_product_upper :
    Real.pi * Real.exp (247 / 800 : ℝ) ≤ (1336867494202149 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell246_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell246_endpointLower :
    (14195880777 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (123 / 800 : ℝ) (247 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1335197028594679 / 312500000000000 : ℝ) (Real.pi * Real.exp (123 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell246_product_lower
  have hD : Real.exp (Real.pi * Real.exp (247 / 800 : ℝ) - (123 / 1600 : ℝ)) ≤
      (667597918877 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell246_denomUpper
    linarith [hpThetaJensenCell246_product_upper]
  have hi : (1 / (667597918877 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (247 / 800 : ℝ) - (123 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (667597918877 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (667597918877 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((123 / 1600 : ℝ) - Real.pi * Real.exp (247 / 800 : ℝ)) := by
    rw [show (123 / 1600 : ℝ) - Real.pi * Real.exp (247 / 800 : ℝ) =
      -(Real.pi * Real.exp (247 / 800 : ℝ) - (123 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (123 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (123 / 400 : ℝ)) := by
    have h := hpThetaJensenCell246_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (667597918877 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell246_endpointUpper :
    hpThetaJensenKernelEndpointUpper (123 / 800 : ℝ) (247 / 1600 : ℝ) ≤ (14359565481 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (247 / 800 : ℝ)) (1336867494202149 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (247 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell246_product_upper
  have hD : (26553252891 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (123 / 400 : ℝ) - (247 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell246_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell246_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (123 / 400 : ℝ) - (247 / 3200 : ℝ)) ≤
      (1 / (26553252891 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (26553252891 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((247 / 3200 : ℝ) - Real.pi * Real.exp (123 / 400 : ℝ)) ≤
      (2 / (26553252891 / 400000000 : ℝ) : ℝ) := by
    rw [show (247 / 3200 : ℝ) - Real.pi * Real.exp (123 / 400 : ℝ) =
      -(Real.pi * Real.exp (123 / 400 : ℝ) - (247 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1336867494202149 / 312500000000000 : ℝ) ^ 2 - 6 *
      (1336867494202149 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell246_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (123 / 800 : ℝ) (247 / 1600 : ℝ)) :
    (14195880777 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14359565481 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell246_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell246_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell247_leftExp :
    (6808609487 / 5000000000 : ℝ) ≤ Real.exp (247 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (247 / 800 : ℝ) (504847566867 / 500000000000 : ℝ)
    (6808609487 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell247_rightExp :
    Real.exp (31 / 100 : ℝ) ≤ (6817125571 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 100 : ℝ) (1009734575721 / 1000000000000 : ℝ)
    (6817125571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell247_denomUpper :
    Real.exp (21030696473974603 / 5000000000000000 : ℝ) ≤ (26838798959 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21030696473974603 / 5000000000000000 : ℝ) (4561886363 /
    4000000000 : ℝ) (26838798959 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell247_denomLower :
    (667179891581 / 10000000000 : ℝ) ≤ Real.exp (2625296636935413 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2625296636935413 / 625000000000000 : ℝ) (142533715133 /
    125000000000 : ℝ) (667179891581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell247_product_lower :
    (2673734136935413 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (247 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell247_leftExp
    (by norm_num : (0 : ℝ) ≤ (6808609487 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell247_product_upper :
    Real.pi * Real.exp (31 / 100 : ℝ) ≤ (21416633973974603 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell247_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell247_endpointLower :
    (14169462567 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (247 / 1600 : ℝ) (31 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2673734136935413 / 625000000000000 : ℝ) (Real.pi * Real.exp (247 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell247_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 100 : ℝ) - (247 / 3200 : ℝ)) ≤
      (26838798959 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell247_denomUpper
    linarith [hpThetaJensenCell247_product_upper]
  have hi : (1 / (26838798959 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 100 : ℝ) - (247 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (26838798959 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (26838798959 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((247 / 3200 : ℝ) - Real.pi * Real.exp (31 / 100 : ℝ)) := by
    rw [show (247 / 3200 : ℝ) - Real.pi * Real.exp (31 / 100 : ℝ) =
      -(Real.pi * Real.exp (31 / 100 : ℝ) - (247 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (247 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (247 / 800 : ℝ)) := by
    have h := hpThetaJensenCell247_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (26838798959 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell247_endpointUpper :
    hpThetaJensenKernelEndpointUpper (247 / 1600 : ℝ) (31 / 200 : ℝ) ≤ (2866583971 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 100 : ℝ)) (21416633973974603 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell247_product_upper
  have hD : (667179891581 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (247 / 800 : ℝ) - (31 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell247_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell247_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (247 / 800 : ℝ) - (31 / 400 : ℝ)) ≤
      (1 / (667179891581 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (667179891581 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 400 : ℝ) - Real.pi * Real.exp (247 / 800 : ℝ)) ≤
      (2 / (667179891581 / 10000000000 : ℝ) : ℝ) := by
    rw [show (31 / 400 : ℝ) - Real.pi * Real.exp (247 / 800 : ℝ) =
      -(Real.pi * Real.exp (247 / 800 : ℝ) - (31 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21416633973974603 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21416633973974603 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell247_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (247 / 1600 : ℝ) (31 / 200 : ℝ)) :
    (14169462567 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2866583971 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell247_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell247_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell248_leftExp :
    (13634251141 / 10000000000 : ℝ) ≤ Real.exp (31 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 100 : ℝ) (25243364393 / 25000000000 : ℝ)
    (13634251141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell248_rightExp :
    Real.exp (249 / 800 : ℝ) ≤ (3412826153 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (249 / 800 : ℝ) (63110876203 / 62500000000 : ℝ)
    (3412826153 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell248_denomUpper :
    Real.exp (10527960752481729 / 2500000000000000 : ℝ) ≤ (337181787417 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10527960752481729 / 2500000000000000 : ℝ) (57032570381 /
    50000000000 : ℝ) (337181787417 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell248_denomLower :
    (335274917149 / 5000000000 : ℝ) ≤ Real.exp (5256891163819559 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5256891163819559 / 1250000000000000 : ℝ) (1140449267529
    / 1000000000000 : ℝ) (335274917149 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell248_product_lower :
    (5354156788819559 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell248_leftExp
    (by norm_num : (0 : ℝ) ≤ (13634251141 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell248_product_upper :
    Real.pi * Real.exp (249 / 800 : ℝ) ≤ (10721710752481729 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell248_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell248_endpointLower :
    (14142980489 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 200 : ℝ) (249 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5354156788819559 / 1250000000000000 : ℝ) (Real.pi * Real.exp (31 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell248_product_lower
  have hD : Real.exp (Real.pi * Real.exp (249 / 800 : ℝ) - (31 / 400 : ℝ)) ≤
      (337181787417 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell248_denomUpper
    linarith [hpThetaJensenCell248_product_upper]
  have hi : (1 / (337181787417 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (249 / 800 : ℝ) - (31 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (337181787417 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (337181787417 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 400 : ℝ) - Real.pi * Real.exp (249 / 800 : ℝ)) := by
    rw [show (31 / 400 : ℝ) - Real.pi * Real.exp (249 / 800 : ℝ) =
      -(Real.pi * Real.exp (249 / 800 : ℝ) - (31 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 100 : ℝ)) := by
    have h := hpThetaJensenCell248_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (337181787417 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell248_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 200 : ℝ) (249 / 1600 : ℝ) ≤ (2861241901 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (249 / 800 : ℝ)) (10721710752481729 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (249 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell248_product_upper
  have hD : (335274917149 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 100 : ℝ) - (249 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell248_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell248_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 100 : ℝ) - (249 / 3200 : ℝ)) ≤
      (1 / (335274917149 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (335274917149 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((249 / 3200 : ℝ) - Real.pi * Real.exp (31 / 100 : ℝ)) ≤
      (2 / (335274917149 / 5000000000 : ℝ) : ℝ) := by
    rw [show (249 / 3200 : ℝ) - Real.pi * Real.exp (31 / 100 : ℝ) =
      -(Real.pi * Real.exp (31 / 100 : ℝ) - (249 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10721710752481729 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10721710752481729 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell248_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 200 : ℝ) (249 / 1600 : ℝ)) :
    (14142980489 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2861241901 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell248_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell248_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell249_leftExp :
    (13651304611 / 10000000000 : ℝ) ≤ Real.exp (249 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (249 / 800 : ℝ) (1009774019247 / 1000000000000 : ℝ)
    (13651304611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell249_rightExp :
    Real.exp (5 / 16 : ℝ) ≤ (3417094853 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5 / 16 : ℝ) (252453366079 / 250000000000 : ℝ)
    (3417094853 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell249_denomUpper :
    Real.exp (10540590020520829 / 2500000000000000 : ℝ) ≤ (338889440729 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10540590020520829 / 2500000000000000 : ℝ) (570415745869
    / 500000000000 : ℝ) (338889440729 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell249_denomLower :
    (134788261807 / 2000000000 : ℝ) ≤ Real.exp (5263197419435089 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5263197419435089 / 1250000000000000 : ℝ) (570314540409 /
    500000000000 : ℝ) (134788261807 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell249_product_lower :
    (5360853669435089 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (249 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell249_leftExp
    (by norm_num : (0 : ℝ) ≤ (13651304611 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell249_product_upper :
    Real.pi * Real.exp (5 / 16 : ℝ) ≤ (10735121270520829 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell249_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell249_endpointLower :
    (2823287003 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (249 / 1600 : ℝ) (5 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5360853669435089 / 1250000000000000 : ℝ) (Real.pi * Real.exp (249 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell249_product_lower
  have hD : Real.exp (Real.pi * Real.exp (5 / 16 : ℝ) - (249 / 3200 : ℝ)) ≤
      (338889440729 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell249_denomUpper
    linarith [hpThetaJensenCell249_product_upper]
  have hi : (1 / (338889440729 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (5 / 16 : ℝ) - (249 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (338889440729 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (338889440729 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((249 / 3200 : ℝ) - Real.pi * Real.exp (5 / 16 : ℝ)) := by
    rw [show (249 / 3200 : ℝ) - Real.pi * Real.exp (5 / 16 : ℝ) =
      -(Real.pi * Real.exp (5 / 16 : ℝ) - (249 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (249 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (249 / 800 : ℝ)) := by
    have h := hpThetaJensenCell249_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (338889440729 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell249_endpointUpper :
    hpThetaJensenKernelEndpointUpper (249 / 1600 : ℝ) (5 / 32 : ℝ) ≤ (1427943491 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (5 / 16 : ℝ)) (10735121270520829 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (5 / 32 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell249_product_upper
  have hD : (134788261807 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (249 / 800 : ℝ) - (5 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell249_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell249_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (249 / 800 : ℝ) - (5 / 64 : ℝ)) ≤
      (1 / (134788261807 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (134788261807 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((5 / 64 : ℝ) - Real.pi * Real.exp (249 / 800 : ℝ)) ≤
      (2 / (134788261807 / 2000000000 : ℝ) : ℝ) := by
    rw [show (5 / 64 : ℝ) - Real.pi * Real.exp (249 / 800 : ℝ) =
      -(Real.pi * Real.exp (249 / 800 : ℝ) - (5 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10735121270520829 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10735121270520829 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell249_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (249 / 1600 : ℝ) (5 / 32 : ℝ)) :
    (2823287003 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1427943491 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell249_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell249_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell250_leftExp :
    (13668379411 / 10000000000 : ℝ) ≤ Real.exp (5 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5 / 16 : ℝ) (201962692863 / 200000000000 : ℝ)
    (13668379411 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell250_rightExp :
    Real.exp (251 / 800 : ℝ) ≤ (13685475569 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (251 / 800 : ℝ) (40394116437 / 40000000000 : ℝ)
    (13685475569 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell250_denomUpper :
    Real.exp (42212944249241417 / 10000000000000000 : ℝ) ≤ (681216055497 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42212944249241417 / 10000000000000000 : ℝ)
    (1141011843527 / 1000000000000 : ℝ) (681216055497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell250_denomLower :
    (677354475957 / 10000000000 : ℝ) ≤ Real.exp (5269512051320289 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5269512051320289 / 1250000000000000 : ℝ) (1140809161351
    / 1000000000000 : ℝ) (677354475957 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell250_product_lower :
    (5367558926320289 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (5 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell250_leftExp
    (by norm_num : (0 : ℝ) ≤ (13668379411 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell250_product_upper :
    Real.pi * Real.exp (251 / 800 : ℝ) ≤ (42994194249241417 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell250_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell250_endpointLower :
    (1761228327 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (5 / 32 : ℝ) (251 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5367558926320289 / 1250000000000000 : ℝ) (Real.pi * Real.exp (5 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell250_product_lower
  have hD : Real.exp (Real.pi * Real.exp (251 / 800 : ℝ) - (5 / 64 : ℝ)) ≤
      (681216055497 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell250_denomUpper
    linarith [hpThetaJensenCell250_product_upper]
  have hi : (1 / (681216055497 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (251 / 800 : ℝ) - (5 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (681216055497 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (681216055497 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((5 / 64 : ℝ) - Real.pi * Real.exp (251 / 800 : ℝ)) := by
    rw [show (5 / 64 : ℝ) - Real.pi * Real.exp (251 / 800 : ℝ) =
      -(Real.pi * Real.exp (251 / 800 : ℝ) - (5 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (5 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (5 / 16 : ℝ)) := by
    have h := hpThetaJensenCell250_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (681216055497 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell250_endpointUpper :
    hpThetaJensenKernelEndpointUpper (5 / 32 : ℝ) (251 / 1600 : ℝ) ≤ (14252596543 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (251 / 800 : ℝ)) (42994194249241417 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (251 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell250_product_upper
  have hD : (677354475957 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (5 / 16 : ℝ) - (251 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell250_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell250_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (5 / 16 : ℝ) - (251 / 3200 : ℝ)) ≤
      (1 / (677354475957 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (677354475957 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((251 / 3200 : ℝ) - Real.pi * Real.exp (5 / 16 : ℝ)) ≤
      (2 / (677354475957 / 10000000000 : ℝ) : ℝ) := by
    rw [show (251 / 3200 : ℝ) - Real.pi * Real.exp (5 / 16 : ℝ) =
      -(Real.pi * Real.exp (5 / 16 : ℝ) - (251 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42994194249241417 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (42994194249241417 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell250_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (5 / 32 : ℝ) (251 / 1600 : ℝ)) :
    (1761228327 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14252596543 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell250_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell250_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell251_leftExp :
    (855342223 / 625000000 : ℝ) ≤ Real.exp (251 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (251 / 800 : ℝ) (252463227731 / 250000000000 : ℝ)
    (855342223 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell251_rightExp :
    Real.exp (63 / 200 : ℝ) ≤ (1370259311 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (63 / 200 : ℝ) (40395694363 / 40000000000 : ℝ)
    (1370259311 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell251_denomUpper :
    Real.exp (4226359559622423 / 1000000000000000 : ℝ) ≤ (684675259847 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4226359559622423 / 1000000000000000 : ℝ) (228238492681 /
    200000000000 : ℝ) (684675259847 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell251_denomLower :
    (170197374139 / 2500000000 : ℝ) ≤ Real.exp (329739691879877 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (329739691879877 / 78125000000000 : ℝ) (285247377387 /
    250000000000 : ℝ) (170197374139 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell251_product_lower :
    (335892035629877 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (251 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell251_leftExp
    (by norm_num : (0 : ℝ) ≤ (855342223 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell251_product_upper :
    Real.pi * Real.exp (63 / 200 : ℝ) ≤ (4304797059622423 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell251_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell251_endpointLower :
    (14063155767 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (251 / 1600 : ℝ) (63 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (335892035629877 / 78125000000000 : ℝ) (Real.pi * Real.exp (251 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell251_product_lower
  have hD : Real.exp (Real.pi * Real.exp (63 / 200 : ℝ) - (251 / 3200 : ℝ)) ≤
      (684675259847 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell251_denomUpper
    linarith [hpThetaJensenCell251_product_upper]
  have hi : (1 / (684675259847 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (63 / 200 : ℝ) - (251 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (684675259847 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (684675259847 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((251 / 3200 : ℝ) - Real.pi * Real.exp (63 / 200 : ℝ)) := by
    rw [show (251 / 3200 : ℝ) - Real.pi * Real.exp (63 / 200 : ℝ) =
      -(Real.pi * Real.exp (63 / 200 : ℝ) - (251 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (251 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (251 / 800 : ℝ)) := by
    have h := hpThetaJensenCell251_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (684675259847 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell251_endpointUpper :
    hpThetaJensenKernelEndpointUpper (251 / 1600 : ℝ) (63 / 400 : ℝ) ≤ (14225694881 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (63 / 200 : ℝ)) (4304797059622423 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (63 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell251_product_upper
  have hD : (170197374139 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (251 / 800 : ℝ) - (63 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell251_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell251_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (251 / 800 : ℝ) - (63 / 800 : ℝ)) ≤
      (1 / (170197374139 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (170197374139 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((63 / 800 : ℝ) - Real.pi * Real.exp (251 / 800 : ℝ)) ≤
      (2 / (170197374139 / 2500000000 : ℝ) : ℝ) := by
    rw [show (63 / 800 : ℝ) - Real.pi * Real.exp (251 / 800 : ℝ) =
      -(Real.pi * Real.exp (251 / 800 : ℝ) - (63 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4304797059622423 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (4304797059622423 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell251_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (251 / 1600 : ℝ) (63 / 400 : ℝ)) :
    (14063155767 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14225694881 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell251_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell251_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell252_leftExp :
    (13702593109 / 10000000000 : ℝ) ≤ Real.exp (63 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (63 / 200 : ℝ) (504946179537 / 500000000000 : ℝ)
    (13702593109 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell252_rightExp :
    Real.exp (253 / 800 : ℝ) ≤ (13719732061 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (253 / 800 : ℝ) (504965904383 / 500000000000 : ℝ)
    (13719732061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell252_denomUpper :
    Real.exp (42314314204713173 / 10000000000000000 : ℝ) ≤ (688156658601 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42314314204713173 / 10000000000000000 : ℝ) (570686675891
    / 500000000000 : ℝ) (688156658601 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell252_denomLower :
    (136849306733 / 2000000000 : ℝ) ≤ Real.exp (5282166486311191 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5282166486311191 / 1250000000000000 : ℝ) (1141170125829
    / 1000000000000 : ℝ) (136849306733 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell252_product_lower :
    (5380994611311191 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (63 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell252_leftExp
    (by norm_num : (0 : ℝ) ≤ (13702593109 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell252_product_upper :
    Real.pi * Real.exp (253 / 800 : ℝ) ≤ (43101814204713173 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell252_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell252_endpointLower :
    (2807284589 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 400 : ℝ) (253 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5380994611311191 / 1250000000000000 : ℝ) (Real.pi * Real.exp (63 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell252_product_lower
  have hD : Real.exp (Real.pi * Real.exp (253 / 800 : ℝ) - (63 / 800 : ℝ)) ≤
      (688156658601 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell252_denomUpper
    linarith [hpThetaJensenCell252_product_upper]
  have hi : (1 / (688156658601 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (253 / 800 : ℝ) - (63 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (688156658601 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (688156658601 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((63 / 800 : ℝ) - Real.pi * Real.exp (253 / 800 : ℝ)) := by
    rw [show (63 / 800 : ℝ) - Real.pi * Real.exp (253 / 800 : ℝ) =
      -(Real.pi * Real.exp (253 / 800 : ℝ) - (63 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (63 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (63 / 200 : ℝ)) := by
    have h := hpThetaJensenCell252_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (688156658601 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell252_endpointUpper :
    hpThetaJensenKernelEndpointUpper (63 / 400 : ℝ) (253 / 1600 : ℝ) ≤ (7099365199 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (253 / 800 : ℝ)) (43101814204713173 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (253 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell252_product_upper
  have hD : (136849306733 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (63 / 200 : ℝ) - (253 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell252_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell252_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (63 / 200 : ℝ) - (253 / 3200 : ℝ)) ≤
      (1 / (136849306733 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (136849306733 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((253 / 3200 : ℝ) - Real.pi * Real.exp (63 / 200 : ℝ)) ≤
      (2 / (136849306733 / 2000000000 : ℝ) : ℝ) := by
    rw [show (253 / 3200 : ℝ) - Real.pi * Real.exp (63 / 200 : ℝ) =
      -(Real.pi * Real.exp (63 / 200 : ℝ) - (253 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43101814204713173 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (43101814204713173 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell252_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (63 / 400 : ℝ) (253 / 1600 : ℝ)) :
    (2807284589 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7099365199 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell252_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell252_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell253_leftExp :
    (685986603 / 500000000 : ℝ) ≤ Real.exp (253 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (253 / 800 : ℝ) (201986361753 / 200000000000 : ℝ)
    (685986603 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell253_rightExp :
    Real.exp (127 / 400 : ℝ) ≤ (13736892449 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (127 / 400 : ℝ) (504985629999 / 500000000000 : ℝ)
    (13736892449 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell253_denomUpper :
    Real.exp (42365100159531257 / 10000000000000000 : ℝ) ≤ (691660417467 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42365100159531257 / 10000000000000000 : ℝ)
    (1141554509081 / 1000000000000 : ℝ) (691660417467 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell253_denomLower :
    (343862875647 / 5000000000 : ℝ) ≤ Real.exp (264425315511497 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (264425315511497 / 62500000000000 : ℝ) (228270202121 /
    200000000000 : ℝ) (343862875647 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell253_product_lower :
    (269386253011497 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (253 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell253_leftExp
    (by norm_num : (0 : ℝ) ≤ (685986603 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell253_product_upper :
    Real.pi * Real.exp (127 / 400 : ℝ) ≤ (43155725159531257 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell253_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell253_endpointLower :
    (700481431 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (253 / 1600 : ℝ) (127 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (269386253011497 / 62500000000000 : ℝ) (Real.pi * Real.exp (253 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell253_product_lower
  have hD : Real.exp (Real.pi * Real.exp (127 / 400 : ℝ) - (253 / 3200 : ℝ)) ≤
      (691660417467 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell253_denomUpper
    linarith [hpThetaJensenCell253_product_upper]
  have hi : (1 / (691660417467 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (127 / 400 : ℝ) - (253 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (691660417467 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (691660417467 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((253 / 3200 : ℝ) - Real.pi * Real.exp (127 / 400 : ℝ)) := by
    rw [show (253 / 3200 : ℝ) - Real.pi * Real.exp (127 / 400 : ℝ) =
      -(Real.pi * Real.exp (127 / 400 : ℝ) - (253 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (253 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (253 / 800 : ℝ)) := by
    have h := hpThetaJensenCell253_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (691660417467 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell253_endpointUpper :
    hpThetaJensenKernelEndpointUpper (253 / 1600 : ℝ) (127 / 800 : ℝ) ≤ (7085851787 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (127 / 400 : ℝ)) (43155725159531257 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (127 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell253_product_upper
  have hD : (343862875647 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (253 / 800 : ℝ) - (127 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell253_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell253_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (253 / 800 : ℝ) - (127 / 1600 : ℝ)) ≤
      (1 / (343862875647 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (343862875647 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((127 / 1600 : ℝ) - Real.pi * Real.exp (253 / 800 : ℝ)) ≤
      (2 / (343862875647 / 5000000000 : ℝ) : ℝ) := by
    rw [show (127 / 1600 : ℝ) - Real.pi * Real.exp (253 / 800 : ℝ) =
      -(Real.pi * Real.exp (253 / 800 : ℝ) - (127 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43155725159531257 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (43155725159531257 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell253_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (253 / 1600 : ℝ) (127 / 800 : ℝ)) :
    (700481431 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7085851787 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell253_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell253_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell254_leftExp :
    (429277889 / 312500000 : ℝ) ≤ Real.exp (127 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (127 / 400 : ℝ) (1009971259997 / 1000000000000 : ℝ)
    (429277889 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell254_rightExp :
    Real.exp (51 / 160 : ℝ) ≤ (6877037151 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 160 : ℝ) (1010010712771 / 1000000000000 : ℝ)
    (6877037151 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell254_denomUpper :
    Real.exp (21207976774321543 / 5000000000000000 : ℝ) ≤ (173796675921 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21207976774321543 / 5000000000000000 : ℝ) (1141735935733
    / 1000000000000 : ℝ) (173796675921 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell254_denomLower :
    (691227314987 / 10000000000 : ℝ) ≤ Real.exp (165464204763661 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (165464204763661 / 39062500000000 : ℝ) (142691520537 /
    125000000000 : ℝ) (691227314987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell254_product_lower :
    (168576997732411 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (127 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell254_leftExp
    (by norm_num : (0 : ℝ) ≤ (429277889 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell254_product_upper :
    Real.pi * Real.exp (51 / 160 : ℝ) ≤ (21604851774321543 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell254_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell254_endpointLower :
    (2796554653 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (127 / 800 : ℝ) (51 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (168576997732411 / 39062500000000 : ℝ) (Real.pi * Real.exp (127 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell254_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 160 : ℝ) - (127 / 1600 : ℝ)) ≤
      (173796675921 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell254_denomUpper
    linarith [hpThetaJensenCell254_product_upper]
  have hi : (1 / (173796675921 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 160 : ℝ) - (127 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (173796675921 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (173796675921 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((127 / 1600 : ℝ) - Real.pi * Real.exp (51 / 160 : ℝ)) := by
    rw [show (127 / 1600 : ℝ) - Real.pi * Real.exp (51 / 160 : ℝ) =
      -(Real.pi * Real.exp (51 / 160 : ℝ) - (127 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (127 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (127 / 400 : ℝ)) := by
    have h := hpThetaJensenCell254_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (173796675921 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell254_endpointUpper :
    hpThetaJensenKernelEndpointUpper (127 / 800 : ℝ) (51 / 320 : ℝ) ≤ (3536153723 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 160 : ℝ)) (21604851774321543 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell254_product_upper
  have hD : (691227314987 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (127 / 400 : ℝ) - (51 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell254_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell254_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (127 / 400 : ℝ) - (51 / 640 : ℝ)) ≤
      (1 / (691227314987 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (691227314987 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 640 : ℝ) - Real.pi * Real.exp (127 / 400 : ℝ)) ≤
      (2 / (691227314987 / 10000000000 : ℝ) : ℝ) := by
    rw [show (51 / 640 : ℝ) - Real.pi * Real.exp (127 / 400 : ℝ) =
      -(Real.pi * Real.exp (127 / 400 : ℝ) - (51 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21604851774321543 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21604851774321543 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell254_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (127 / 800 : ℝ) (51 / 320 : ℝ)) :
    (2796554653 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3536153723 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell254_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell254_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell255_leftExp :
    (137540743 / 100000000 : ℝ) ≤ Real.exp (51 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 160 : ℝ) (101001071277 / 100000000000 : ℝ)
    (137540743 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell255_rightExp :
    Real.exp (8 / 25 : ℝ) ≤ (3442819411 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8 / 25 : ℝ) (202010033417 / 200000000000 : ℝ)
    (3442819411 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell255_denomUpper :
    Real.exp (10616718611861723 / 2500000000000000 : ℝ) ≤ (349367842523 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (10616718611861723 / 2500000000000000 : ℝ) (570958816063
    / 500000000000 : ℝ) (349367842523 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell255_denomLower :
    (138950278341 / 2000000000 : ℝ) ≤ Real.exp (53012112235357 / 12500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53012112235357 / 12500000000000 : ℝ) (285428396831 /
    250000000000 : ℝ) (138950278341 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell255_product_lower :
    (54012112235357 / 12500000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell255_leftExp
    (by norm_num : (0 : ℝ) ≤ (137540743 / 100000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell255_product_upper :
    Real.pi * Real.exp (8 / 25 : ℝ) ≤ (10815937361861723 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell255_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell255_endpointLower :
    (13955857367 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 320 : ℝ) (4 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (54012112235357 / 12500000000000 : ℝ) (Real.pi * Real.exp (51 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell255_product_lower
  have hD : Real.exp (Real.pi * Real.exp (8 / 25 : ℝ) - (51 / 640 : ℝ)) ≤
      (349367842523 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell255_denomUpper
    linarith [hpThetaJensenCell255_product_upper]
  have hi : (1 / (349367842523 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (8 / 25 : ℝ) - (51 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (349367842523 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (349367842523 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 640 : ℝ) - Real.pi * Real.exp (8 / 25 : ℝ)) := by
    rw [show (51 / 640 : ℝ) - Real.pi * Real.exp (8 / 25 : ℝ) =
      -(Real.pi * Real.exp (8 / 25 : ℝ) - (51 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 160 : ℝ)) := by
    have h := hpThetaJensenCell255_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (349367842523 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell255_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 320 : ℝ) (4 / 25 : ℝ) ≤ (14117464823 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (8 / 25 : ℝ)) (10815937361861723 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (4 / 25 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell255_product_upper
  have hD : (138950278341 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 160 : ℝ) - (2 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell255_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell255_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 160 : ℝ) - (2 / 25 : ℝ)) ≤
      (1 / (138950278341 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (138950278341 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((2 / 25 : ℝ) - Real.pi * Real.exp (51 / 160 : ℝ)) ≤
      (2 / (138950278341 / 2000000000 : ℝ) : ℝ) := by
    rw [show (2 / 25 : ℝ) - Real.pi * Real.exp (51 / 160 : ℝ) =
      -(Real.pi * Real.exp (51 / 160 : ℝ) - (2 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10815937361861723 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (10815937361861723 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell255_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 320 : ℝ) (4 / 25 : ℝ)) :
    (13955857367 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14117464823 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell255_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell255_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell256_leftExp :
    (13771277643 / 10000000000 : ℝ) ≤ Real.exp (8 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8 / 25 : ℝ) (252512541771 / 250000000000 : ℝ)
    (13771277643 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell256_rightExp :
    Real.exp (257 / 800 : ℝ) ≤ (1723562813 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (257 / 800 : ℝ) (50504481147 / 50000000000 : ℝ)
    (1723562813 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell256_denomUpper :
    Real.exp (5314732868381109 / 1250000000000000 : ℝ) ≤ (87788441487 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5314732868381109 / 1250000000000000 : ℝ) (1142099598707
    / 1000000000000 : ℝ) (87788441487 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell256_denomLower :
    (349149074899 / 5000000000 : ℝ) ≤ Real.exp (5307576334128457 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5307576334128457 / 1250000000000000 : ℝ) (1141895280111
    / 1000000000000 : ℝ) (349149074899 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell256_product_lower :
    (5407966959128457 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (8 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell256_leftExp
    (by norm_num : (0 : ℝ) ≤ (13771277643 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell256_product_upper :
    Real.pi * Real.exp (257 / 800 : ℝ) ≤ (5414732868381109 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell256_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell256_endpointLower :
    (6964440697 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (4 / 25 : ℝ) (257 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5407966959128457 / 1250000000000000 : ℝ) (Real.pi * Real.exp (8 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell256_product_lower
  have hD : Real.exp (Real.pi * Real.exp (257 / 800 : ℝ) - (2 / 25 : ℝ)) ≤
      (87788441487 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell256_denomUpper
    linarith [hpThetaJensenCell256_product_upper]
  have hi : (1 / (87788441487 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (257 / 800 : ℝ) - (2 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (87788441487 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (87788441487 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((2 / 25 : ℝ) - Real.pi * Real.exp (257 / 800 : ℝ)) := by
    rw [show (2 / 25 : ℝ) - Real.pi * Real.exp (257 / 800 : ℝ) =
      -(Real.pi * Real.exp (257 / 800 : ℝ) - (2 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (8 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (8 / 25 : ℝ)) := by
    have h := hpThetaJensenCell256_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (87788441487 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell256_endpointUpper :
    hpThetaJensenKernelEndpointUpper (4 / 25 : ℝ) (257 / 1600 : ℝ) ≤ (281805077 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (257 / 800 : ℝ)) (5414732868381109 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (257 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell256_product_upper
  have hD : (349149074899 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (8 / 25 : ℝ) - (257 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell256_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell256_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (8 / 25 : ℝ) - (257 / 3200 : ℝ)) ≤
      (1 / (349149074899 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (349149074899 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((257 / 3200 : ℝ) - Real.pi * Real.exp (8 / 25 : ℝ)) ≤
      (2 / (349149074899 / 5000000000 : ℝ) : ℝ) := by
    rw [show (257 / 3200 : ℝ) - Real.pi * Real.exp (8 / 25 : ℝ) =
      -(Real.pi * Real.exp (8 / 25 : ℝ) - (257 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5414732868381109 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (5414732868381109 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell256_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (4 / 25 : ℝ) (257 / 1600 : ℝ)) :
    (6964440697 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (281805077 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell256_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell256_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell257_leftExp :
    (13788502503 / 10000000000 : ℝ) ≤ Real.exp (257 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (257 / 800 : ℝ) (1010089622939 / 1000000000000 : ℝ)
    (13788502503 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell257_rightExp :
    Real.exp (129 / 400 : ℝ) ≤ (13805748909 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (129 / 400 : ℝ) (63133067521 / 62500000000 : ℝ)
    (13805748909 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell257_denomUpper :
    Real.exp (42568919132272037 / 10000000000000000 : ℝ) ≤ (705902415469 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42568919132272037 / 10000000000000000 : ℝ) (142785229487
    / 125000000000 : ℝ) (705902415469 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell257_denomLower :
    (350933879411 / 5000000000 : ℝ) ≤ Real.exp (5313949894425597 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5313949894425597 / 1250000000000000 : ℝ) (1142077243069
    / 1000000000000 : ℝ) (350933879411 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell257_product_lower :
    (5414731144425597 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (257 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell257_leftExp
    (by norm_num : (0 : ℝ) ≤ (13788502503 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell257_product_upper :
    Real.pi * Real.exp (129 / 400 : ℝ) ≤ (43372044132272037 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell257_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell257_endpointLower :
    (13901845821 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (257 / 1600 : ℝ) (129 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5414731144425597 / 1250000000000000 : ℝ) (Real.pi * Real.exp (257 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell257_product_lower
  have hD : Real.exp (Real.pi * Real.exp (129 / 400 : ℝ) - (257 / 3200 : ℝ)) ≤
      (705902415469 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell257_denomUpper
    linarith [hpThetaJensenCell257_product_upper]
  have hi : (1 / (705902415469 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (129 / 400 : ℝ) - (257 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (705902415469 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (705902415469 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((257 / 3200 : ℝ) - Real.pi * Real.exp (129 / 400 : ℝ)) := by
    rw [show (257 / 3200 : ℝ) - Real.pi * Real.exp (129 / 400 : ℝ) =
      -(Real.pi * Real.exp (129 / 400 : ℝ) - (257 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (257 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (257 / 800 : ℝ)) := by
    have h := hpThetaJensenCell257_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (705902415469 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell257_endpointUpper :
    hpThetaJensenKernelEndpointUpper (257 / 1600 : ℝ) (129 / 800 : ℝ) ≤ (14062982459 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (129 / 400 : ℝ)) (43372044132272037 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (129 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell257_product_upper
  have hD : (350933879411 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (257 / 800 : ℝ) - (129 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell257_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell257_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (257 / 800 : ℝ) - (129 / 1600 : ℝ)) ≤
      (1 / (350933879411 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (350933879411 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((129 / 1600 : ℝ) - Real.pi * Real.exp (257 / 800 : ℝ)) ≤
      (2 / (350933879411 / 5000000000 : ℝ) : ℝ) := by
    rw [show (129 / 1600 : ℝ) - Real.pi * Real.exp (257 / 800 : ℝ) =
      -(Real.pi * Real.exp (257 / 800 : ℝ) - (129 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43372044132272037 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (43372044132272037 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell257_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (257 / 1600 : ℝ) (129 / 800 : ℝ)) :
    (13901845821 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14062982459 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell257_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell257_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell258_leftExp :
    (3451437227 / 2500000000 : ℝ) ≤ Real.exp (129 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (129 / 400 : ℝ) (202025816067 / 200000000000 : ℝ)
    (3451437227 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell258_rightExp :
    Real.exp (259 / 800 : ℝ) ≤ (6911508443 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (259 / 800 : ℝ) (505084269637 / 500000000000 : ℝ)
    (6911508443 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell258_denomUpper :
    Real.exp (21310021543969699 / 5000000000000000 : ℝ) ≤ (709520508547 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21310021543969699 / 5000000000000000 : ℝ) (1142464344119
    / 1000000000000 : ℝ) (709520508547 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell258_denomLower :
    (705460390117 / 10000000000 : ℝ) ≤ Real.exp (1330082978855673 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1330082978855673 / 312500000000000 : ℝ) (1142259476629 /
    1000000000000 : ℝ) (705460390117 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell258_product_lower :
    (1355375947605673 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (129 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell258_leftExp
    (by norm_num : (0 : ℝ) ≤ (3451437227 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell258_product_upper :
    Real.pi * Real.exp (259 / 800 : ℝ) ≤ (21713146543969699 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell258_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell258_endpointLower :
    (13874751127 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (129 / 800 : ℝ) (259 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1355375947605673 / 312500000000000 : ℝ) (Real.pi * Real.exp (129 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell258_product_lower
  have hD : Real.exp (Real.pi * Real.exp (259 / 800 : ℝ) - (129 / 1600 : ℝ)) ≤
      (709520508547 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell258_denomUpper
    linarith [hpThetaJensenCell258_product_upper]
  have hi : (1 / (709520508547 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (259 / 800 : ℝ) - (129 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (709520508547 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (709520508547 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((129 / 1600 : ℝ) - Real.pi * Real.exp (259 / 800 : ℝ)) := by
    rw [show (129 / 1600 : ℝ) - Real.pi * Real.exp (259 / 800 : ℝ) =
      -(Real.pi * Real.exp (259 / 800 : ℝ) - (129 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (129 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (129 / 400 : ℝ)) := by
    have h := hpThetaJensenCell258_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (709520508547 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell258_endpointUpper :
    hpThetaJensenKernelEndpointUpper (129 / 800 : ℝ) (259 / 1600 : ℝ) ≤ (1754456391 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (259 / 800 : ℝ)) (21713146543969699 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (259 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell258_product_upper
  have hD : (705460390117 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (129 / 400 : ℝ) - (259 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell258_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell258_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (129 / 400 : ℝ) - (259 / 3200 : ℝ)) ≤
      (1 / (705460390117 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (705460390117 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((259 / 3200 : ℝ) - Real.pi * Real.exp (129 / 400 : ℝ)) ≤
      (2 / (705460390117 / 10000000000 : ℝ) : ℝ) := by
    rw [show (259 / 3200 : ℝ) - Real.pi * Real.exp (129 / 400 : ℝ) =
      -(Real.pi * Real.exp (129 / 400 : ℝ) - (259 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21713146543969699 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (21713146543969699 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell258_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (129 / 800 : ℝ) (259 / 1600 : ℝ)) :
    (13874751127 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1754456391 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell258_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell258_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell259_leftExp :
    (3455754221 / 2500000000 : ℝ) ≤ Real.exp (259 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (259 / 800 : ℝ) (1010168539273 / 1000000000000 : ℝ)
    (3455754221 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell259_rightExp :
    Real.exp (13 / 40 : ℝ) ≤ (13840306461 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 40 : ℝ) (505103999877 / 500000000000 : ℝ)
    (13840306461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell259_denomUpper :
    Real.exp (42671234895732373 / 10000000000000000 : ℝ) ≤ (142632397003 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (42671234895732373 / 10000000000000000 : ℝ) (228529424757
    / 200000000000 : ℝ) (142632397003 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell259_denomLower :
    (709076216139 / 10000000000 : ℝ) ≤ Real.exp (1331680601832479 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1331680601832479 / 312500000000000 : ℝ) (571220990603 /
    500000000000 : ℝ) (709076216139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell259_product_lower :
    (1357071226832479 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (259 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell259_leftExp
    (by norm_num : (0 : ℝ) ≤ (3455754221 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell259_product_upper :
    Real.pi * Real.exp (13 / 40 : ℝ) ≤ (43480609895732373 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell259_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell259_endpointLower :
    (6923798897 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (259 / 1600 : ℝ) (13 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1357071226832479 / 312500000000000 : ℝ) (Real.pi * Real.exp (259 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell259_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 40 : ℝ) - (259 / 3200 : ℝ)) ≤
      (142632397003 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell259_denomUpper
    linarith [hpThetaJensenCell259_product_upper]
  have hi : (1 / (142632397003 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 40 : ℝ) - (259 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (142632397003 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (142632397003 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((259 / 3200 : ℝ) - Real.pi * Real.exp (13 / 40 : ℝ)) := by
    rw [show (259 / 3200 : ℝ) - Real.pi * Real.exp (13 / 40 : ℝ) =
      -(Real.pi * Real.exp (13 / 40 : ℝ) - (259 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (259 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (259 / 800 : ℝ)) := by
    have h := hpThetaJensenCell259_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (142632397003 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell259_endpointUpper :
    hpThetaJensenKernelEndpointUpper (259 / 1600 : ℝ) (13 / 80 : ℝ) ≤ (14008260337 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 40 : ℝ)) (43480609895732373 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell259_product_upper
  have hD : (709076216139 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (259 / 800 : ℝ) - (13 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell259_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell259_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (259 / 800 : ℝ) - (13 / 160 : ℝ)) ≤
      (1 / (709076216139 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (709076216139 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 160 : ℝ) - Real.pi * Real.exp (259 / 800 : ℝ)) ≤
      (2 / (709076216139 / 10000000000 : ℝ) : ℝ) := by
    rw [show (13 / 160 : ℝ) - Real.pi * Real.exp (259 / 800 : ℝ) =
      -(Real.pi * Real.exp (259 / 800 : ℝ) - (13 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43480609895732373 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (43480609895732373 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell259_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (259 / 1600 : ℝ) (13 / 80 : ℝ)) :
    (6923798897 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14008260337 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell259_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell259_endpointUpper

def hpThetaJensenCellsBatch012Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (14353022537 / 10000000000 : ℝ)
  | 1 => (3581749347 / 2500000000 : ℝ)
  | 2 => (2860181111 / 2000000000 : ℝ)
  | 3 => (14274747513 / 10000000000 : ℝ)
  | 4 => (356213093 / 250000000 : ℝ)
  | 5 => (2844446931 / 2000000000 : ℝ)
  | 6 => (14195880777 / 10000000000 : ℝ)
  | 7 => (14169462567 / 10000000000 : ℝ)
  | 8 => (14142980489 / 10000000000 : ℝ)
  | 9 => (2823287003 / 2000000000 : ℝ)
  | 10 => (1761228327 / 1250000000 : ℝ)
  | 11 => (14063155767 / 10000000000 : ℝ)
  | 12 => (2807284589 / 2000000000 : ℝ)
  | 13 => (700481431 / 500000000 : ℝ)
  | 14 => (2796554653 / 2000000000 : ℝ)
  | 15 => (13955857367 / 10000000000 : ℝ)
  | 16 => (6964440697 / 5000000000 : ℝ)
  | 17 => (13901845821 / 10000000000 : ℝ)
  | 18 => (13874751127 / 10000000000 : ℝ)
  | 19 => (6923798897 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch012Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3629513379 / 2500000000 : ℝ)
  | 1 => (14491806169 / 10000000000 : ℝ)
  | 2 => (2893098253 / 2000000000 : ℝ)
  | 3 => (14439109269 / 10000000000 : ℝ)
  | 4 => (14412660661 / 10000000000 : ℝ)
  | 5 => (899134119 / 625000000 : ℝ)
  | 6 => (14359565481 / 10000000000 : ℝ)
  | 7 => (2866583971 / 2000000000 : ℝ)
  | 8 => (2861241901 / 2000000000 : ℝ)
  | 9 => (1427943491 / 1000000000 : ℝ)
  | 10 => (14252596543 / 10000000000 : ℝ)
  | 11 => (14225694881 / 10000000000 : ℝ)
  | 12 => (7099365199 / 5000000000 : ℝ)
  | 13 => (7085851787 / 5000000000 : ℝ)
  | 14 => (3536153723 / 2500000000 : ℝ)
  | 15 => (14117464823 / 10000000000 : ℝ)
  | 16 => (281805077 / 200000000 : ℝ)
  | 17 => (14062982459 / 10000000000 : ℝ)
  | 18 => (1754456391 / 1250000000 : ℝ)
  | 19 => (14008260337 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch012_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch012Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch012Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell240_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell241_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell242_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell243_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell244_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell245_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell246_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell247_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell248_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell249_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell250_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell251_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell252_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell253_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell254_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell255_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell256_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell257_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell258_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell259_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper] at h ⊢
    exact h

end HodgeProofHP
