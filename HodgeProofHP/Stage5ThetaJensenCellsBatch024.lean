import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell480_leftExp :
    (18221188003 / 10000000000 : ℝ) ≤ Real.exp (3 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3 / 5 : ℝ) (254731721263 / 250000000000 : ℝ)
    (18221188003 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell480_rightExp :
    Real.exp (481 / 800 : ℝ) ≤ (18243978731 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (481 / 800 : ℝ) (1018966687661 / 1000000000000 : ℝ)
    (18243978731 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell480_denomUpper :
    Real.exp (55815155873458483 / 10000000000000000 : ℝ) ≤ (2654736495507 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55815155873458483 / 10000000000000000 : ℝ) (297639576589
    / 250000000000 : ℝ) (2654736495507 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell480_denomLower :
    (20585690019 / 78125000 : ℝ) ≤ Real.exp (6967551682590097 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6967551682590097 / 1250000000000000 : ℝ) (1190280260077
    / 1000000000000 : ℝ) (20585690019 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell480_product_lower :
    (7155442307590097 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (3 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell480_leftExp
    (by norm_num : (0 : ℝ) ≤ (18221188003 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell480_product_upper :
    Real.pi * Real.exp (481 / 800 : ℝ) ≤ (57315155873458483 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell480_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell480_endpointLower :
    (455444377 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 10 : ℝ) (481 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7155442307590097 / 1250000000000000 : ℝ) (Real.pi * Real.exp (3 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell480_product_lower
  have hD : Real.exp (Real.pi * Real.exp (481 / 800 : ℝ) - (3 / 20 : ℝ)) ≤
      (2654736495507 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell480_denomUpper
    linarith [hpThetaJensenCell480_product_upper]
  have hi : (1 / (2654736495507 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (481 / 800 : ℝ) - (3 / 20 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2654736495507 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2654736495507 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 20 : ℝ) - Real.pi * Real.exp (481 / 800 : ℝ)) := by
    rw [show (3 / 20 : ℝ) - Real.pi * Real.exp (481 / 800 : ℝ) =
      -(Real.pi * Real.exp (481 / 800 : ℝ) - (3 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (3 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (3 / 5 : ℝ)) := by
    have h := hpThetaJensenCell480_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2654736495507 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell480_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 10 : ℝ) (481 / 1600 : ℝ) ≤ (7382819229 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (481 / 800 : ℝ)) (57315155873458483 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (481 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell480_product_upper
  have hD : (20585690019 / 78125000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (3 / 5 : ℝ) - (481 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell480_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell480_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (3 / 5 : ℝ) - (481 / 3200 : ℝ)) ≤
      (1 / (20585690019 / 78125000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (20585690019 / 78125000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((481 / 3200 : ℝ) - Real.pi * Real.exp (3 / 5 : ℝ)) ≤
      (2 / (20585690019 / 78125000 : ℝ) : ℝ) := by
    rw [show (481 / 3200 : ℝ) - Real.pi * Real.exp (3 / 5 : ℝ) =
      -(Real.pi * Real.exp (3 / 5 : ℝ) - (481 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57315155873458483 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (57315155873458483 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell480_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 10 : ℝ) (481 / 1600 : ℝ)) :
    (455444377 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7382819229 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell480_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell480_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell481_leftExp :
    (18243978729 / 10000000000 : ℝ) ≤ Real.exp (481 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (481 / 800 : ℝ) (50948334383 / 50000000000 : ℝ)
    (18243978729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell481_rightExp :
    Real.exp (241 / 400 : ℝ) ≤ (18266797963 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (241 / 400 : ℝ) (40760259673 / 40000000000 : ℝ)
    (18266797963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell481_denomUpper :
    Real.exp (55883719612975059 / 10000000000000000 : ℝ) ≤ (668250225979 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (55883719612975059 / 10000000000000000 : ℝ) (297703356179
    / 250000000000 : ℝ) (668250225979 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell481_denomLower :
    (1326536480777 / 5000000000 : ℝ) ≤ Real.exp (6976110952899571 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6976110952899571 / 1250000000000000 : ℝ) (1190534985591
    / 1000000000000 : ℝ) (1326536480777 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell481_product_lower :
    (7164392202899571 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (481 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell481_leftExp
    (by norm_num : (0 : ℝ) ≤ (18243978729 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell481_product_upper :
    Real.pi * Real.exp (241 / 400 : ℝ) ≤ (57386844612975059 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell481_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell481_endpointLower :
    (145173041 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (481 / 1600 : ℝ) (241 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7164392202899571 / 1250000000000000 : ℝ) (Real.pi * Real.exp (481 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell481_product_lower
  have hD : Real.exp (Real.pi * Real.exp (241 / 400 : ℝ) - (481 / 3200 : ℝ)) ≤
      (668250225979 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell481_denomUpper
    linarith [hpThetaJensenCell481_product_upper]
  have hi : (1 / (668250225979 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (241 / 400 : ℝ) - (481 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (668250225979 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (668250225979 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((481 / 3200 : ℝ) - Real.pi * Real.exp (241 / 400 : ℝ)) := by
    rw [show (481 / 3200 : ℝ) - Real.pi * Real.exp (241 / 400 : ℝ) =
      -(Real.pi * Real.exp (241 / 400 : ℝ) - (481 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (481 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (481 / 800 : ℝ)) := by
    have h := hpThetaJensenCell481_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (668250225979 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell481_endpointUpper :
    hpThetaJensenKernelEndpointUpper (481 / 1600 : ℝ) (241 / 800 : ℝ) ≤ (1838511959 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (241 / 400 : ℝ)) (57386844612975059 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (241 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell481_product_upper
  have hD : (1326536480777 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (481 / 800 : ℝ) - (241 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell481_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell481_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (481 / 800 : ℝ) - (241 / 1600 : ℝ)) ≤
      (1 / (1326536480777 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1326536480777 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((241 / 1600 : ℝ) - Real.pi * Real.exp (481 / 800 : ℝ)) ≤
      (2 / (1326536480777 / 5000000000 : ℝ) : ℝ) := by
    rw [show (241 / 1600 : ℝ) - Real.pi * Real.exp (481 / 800 : ℝ) =
      -(Real.pi * Real.exp (481 / 800 : ℝ) - (241 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57386844612975059 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (57386844612975059 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell481_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (481 / 1600 : ℝ) (241 / 800 : ℝ)) :
    (145173041 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1838511959 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell481_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell481_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell482_leftExp :
    (9133398981 / 5000000000 : ℝ) ≤ Real.exp (241 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (241 / 400 : ℝ) (63687905739 / 62500000000 : ℝ)
    (9133398981 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell482_rightExp :
    Real.exp (483 / 800 : ℝ) ≤ (9144822869 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (483 / 800 : ℝ) (127380787193 / 125000000000 : ℝ)
    (9144822869 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell482_denomUpper :
    Real.exp (27976186511490317 / 5000000000000000 : ℝ) ≤ (2691415104199 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27976186511490317 / 5000000000000000 : ℝ) (595534465753
    / 500000000000 : ℝ) (2691415104199 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell482_denomLower :
    (133566295987 / 500000000 : ℝ) ≤ Real.exp (3492340708939719 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3492340708939719 / 625000000000000 : ℝ) (1190790098881 /
    1000000000000 : ℝ) (133566295987 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell482_product_lower :
    (3586676646439719 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (241 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell482_leftExp
    (by norm_num : (0 : ℝ) ≤ (9133398981 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell482_product_upper :
    Real.pi * Real.exp (483 / 800 : ℝ) ≤ (28729311511490317 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell482_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell482_endpointLower :
    (3615117473 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (241 / 800 : ℝ) (483 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3586676646439719 / 625000000000000 : ℝ) (Real.pi * Real.exp (241 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell482_product_lower
  have hD : Real.exp (Real.pi * Real.exp (483 / 800 : ℝ) - (241 / 1600 : ℝ)) ≤
      (2691415104199 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell482_denomUpper
    linarith [hpThetaJensenCell482_product_upper]
  have hi : (1 / (2691415104199 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (483 / 800 : ℝ) - (241 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2691415104199 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2691415104199 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((241 / 1600 : ℝ) - Real.pi * Real.exp (483 / 800 : ℝ)) := by
    rw [show (241 / 1600 : ℝ) - Real.pi * Real.exp (483 / 800 : ℝ) =
      -(Real.pi * Real.exp (483 / 800 : ℝ) - (241 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (241 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (241 / 400 : ℝ)) := by
    have h := hpThetaJensenCell482_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2691415104199 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell482_endpointUpper :
    hpThetaJensenKernelEndpointUpper (241 / 800 : ℝ) (483 / 1600 : ℝ) ≤ (7325317479 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (483 / 800 : ℝ)) (28729311511490317 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (483 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell482_product_upper
  have hD : (133566295987 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (241 / 400 : ℝ) - (483 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell482_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell482_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (241 / 400 : ℝ) - (483 / 3200 : ℝ)) ≤
      (1 / (133566295987 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (133566295987 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((483 / 3200 : ℝ) - Real.pi * Real.exp (241 / 400 : ℝ)) ≤
      (2 / (133566295987 / 500000000 : ℝ) : ℝ) := by
    rw [show (483 / 3200 : ℝ) - Real.pi * Real.exp (241 / 400 : ℝ) =
      -(Real.pi * Real.exp (241 / 400 : ℝ) - (483 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28729311511490317 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (28729311511490317 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell482_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (241 / 800 : ℝ) (483 / 1600 : ℝ)) :
    (3615117473 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7325317479 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell482_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell482_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell483_leftExp :
    (2286205717 / 1250000000 : ℝ) ≤ Real.exp (483 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (483 / 800 : ℝ) (1019046297543 / 1000000000000 : ℝ)
    (2286205717 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell483_rightExp :
    Real.exp (121 / 200 : ℝ) ≤ (1831252209 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (121 / 200 : ℝ) (1019086104817 / 1000000000000 : ℝ)
    (1831252209 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell483_denomUpper :
    Real.exp (5602111621028937 / 1000000000000000 : ℝ) ≤ (1354990244253 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5602111621028937 / 1000000000000000 : ℝ) (1191324827349
    / 1000000000000 : ℝ) (1354990244253 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell483_denomLower :
    (1344864287053 / 5000000000 : ℝ) ≤ Real.exp (874157886360183 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (874157886360183 / 156250000000000 : ℝ) (1191045600569 /
    1000000000000 : ℝ) (1344864287053 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell483_product_lower :
    (897790698860183 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (483 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell483_leftExp
    (by norm_num : (0 : ℝ) ≤ (2286205717 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell483_product_upper :
    Real.pi * Real.exp (121 / 200 : ℝ) ≤ (5753049121028937 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell483_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell483_endpointLower :
    (7201859043 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (483 / 1600 : ℝ) (121 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (897790698860183 / 156250000000000 : ℝ) (Real.pi * Real.exp (483 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell483_product_lower
  have hD : Real.exp (Real.pi * Real.exp (121 / 200 : ℝ) - (483 / 3200 : ℝ)) ≤
      (1354990244253 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell483_denomUpper
    linarith [hpThetaJensenCell483_product_upper]
  have hi : (1 / (1354990244253 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (121 / 200 : ℝ) - (483 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1354990244253 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1354990244253 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((483 / 3200 : ℝ) - Real.pi * Real.exp (121 / 200 : ℝ)) := by
    rw [show (483 / 3200 : ℝ) - Real.pi * Real.exp (121 / 200 : ℝ) =
      -(Real.pi * Real.exp (121 / 200 : ℝ) - (483 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (483 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (483 / 800 : ℝ)) := by
    have h := hpThetaJensenCell483_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1354990244253 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell483_endpointUpper :
    hpThetaJensenKernelEndpointUpper (483 / 1600 : ℝ) (121 / 400 : ℝ) ≤ (7296628489 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (121 / 200 : ℝ)) (5753049121028937 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (121 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell483_product_upper
  have hD : (1344864287053 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (483 / 800 : ℝ) - (121 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell483_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell483_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (483 / 800 : ℝ) - (121 / 800 : ℝ)) ≤
      (1 / (1344864287053 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1344864287053 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((121 / 800 : ℝ) - Real.pi * Real.exp (483 / 800 : ℝ)) ≤
      (2 / (1344864287053 / 5000000000 : ℝ) : ℝ) := by
    rw [show (121 / 800 : ℝ) - Real.pi * Real.exp (483 / 800 : ℝ) =
      -(Real.pi * Real.exp (483 / 800 : ℝ) - (121 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5753049121028937 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5753049121028937 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell483_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (483 / 1600 : ℝ) (121 / 400 : ℝ)) :
    (7201859043 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7296628489 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell483_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell483_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell484_leftExp :
    (2289065261 / 1250000000 : ℝ) ≤ Real.exp (121 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (121 / 200 : ℝ) (63692881551 / 62500000000 : ℝ)
    (2289065261 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell484_rightExp :
    Real.exp (97 / 160 : ℝ) ≤ (3667085411 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97 / 160 : ℝ) (509562956823 / 500000000000 : ℝ)
    (3667085411 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell484_denomUpper :
    Real.exp (11217989857599723 / 2000000000000000 : ℝ) ≤ (272869846519 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11217989857599723 / 2000000000000000 : ℝ) (238316222579
    / 200000000000 : ℝ) (272869846519 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell484_denomLower :
    (2708282318583 / 10000000000 : ℝ) ≤ Real.exp (875231998304439 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (875231998304439 / 156250000000000 : ℝ) (238260298263 /
    200000000000 : ℝ) (2708282318583 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell484_product_lower :
    (898913638929439 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (121 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell484_leftExp
    (by norm_num : (0 : ℝ) ≤ (2289065261 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell484_product_upper :
    Real.pi * Real.exp (97 / 160 : ℝ) ≤ (11520489857599723 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell484_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell484_endpointLower :
    (896690583 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (121 / 400 : ℝ) (97 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (898913638929439 / 156250000000000 : ℝ) (Real.pi * Real.exp (121 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell484_product_lower
  have hD : Real.exp (Real.pi * Real.exp (97 / 160 : ℝ) - (121 / 800 : ℝ)) ≤
      (272869846519 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell484_denomUpper
    linarith [hpThetaJensenCell484_product_upper]
  have hi : (1 / (272869846519 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (97 / 160 : ℝ) - (121 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (272869846519 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (272869846519 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((121 / 800 : ℝ) - Real.pi * Real.exp (97 / 160 : ℝ)) := by
    rw [show (121 / 800 : ℝ) - Real.pi * Real.exp (97 / 160 : ℝ) =
      -(Real.pi * Real.exp (97 / 160 : ℝ) - (121 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (121 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (121 / 200 : ℝ)) := by
    have h := hpThetaJensenCell484_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (272869846519 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell484_endpointUpper :
    hpThetaJensenKernelEndpointUpper (121 / 400 : ℝ) (97 / 320 : ℝ) ≤ (3633990593 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (97 / 160 : ℝ)) (11520489857599723 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (97 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell484_product_upper
  have hD : (2708282318583 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (121 / 200 : ℝ) - (97 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell484_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell484_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (121 / 200 : ℝ) - (97 / 640 : ℝ)) ≤
      (1 / (2708282318583 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2708282318583 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((97 / 640 : ℝ) - Real.pi * Real.exp (121 / 200 : ℝ)) ≤
      (2 / (2708282318583 / 10000000000 : ℝ) : ℝ) := by
    rw [show (97 / 640 : ℝ) - Real.pi * Real.exp (121 / 200 : ℝ) =
      -(Real.pi * Real.exp (121 / 200 : ℝ) - (97 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11520489857599723 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (11520489857599723 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell484_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (121 / 400 : ℝ) (97 / 320 : ℝ)) :
    (896690583 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3633990593 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell484_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell484_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell485_leftExp :
    (9167713527 / 5000000000 : ℝ) ≤ Real.exp (97 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (97 / 160 : ℝ) (203825182729 / 200000000000 : ℝ)
    (9167713527 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell485_rightExp :
    Real.exp (243 / 400 : ℝ) ≤ (18358360669 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (243 / 400 : ℝ) (1019165724029 / 1000000000000 : ℝ)
    (18358360669 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell485_denomUpper :
    Real.exp (56158872369205717 / 10000000000000000 : ℝ) ≤ (1373785228407 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56158872369205717 / 10000000000000000 : ℝ)
    (1191837788791 / 1000000000000 : ℝ) (1373785228407 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell485_denomLower :
    (2726988560441 / 10000000000 : ℝ) ≤ Real.exp (3505230059339373 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3505230059339373 / 625000000000000 : ℝ) (595778885883 /
    500000000000 : ℝ) (2726988560441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell485_product_lower :
    (3600151934339373 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (97 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell485_leftExp
    (by norm_num : (0 : ℝ) ≤ (9167713527 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell485_product_upper :
    Real.pi * Real.exp (243 / 400 : ℝ) ≤ (57674497369205717 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell485_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell485_endpointLower :
    (57161857 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 320 : ℝ) (243 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3600151934339373 / 625000000000000 : ℝ) (Real.pi * Real.exp (97 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell485_product_lower
  have hD : Real.exp (Real.pi * Real.exp (243 / 400 : ℝ) - (97 / 640 : ℝ)) ≤
      (1373785228407 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell485_denomUpper
    linarith [hpThetaJensenCell485_product_upper]
  have hi : (1 / (1373785228407 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (243 / 400 : ℝ) - (97 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1373785228407 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1373785228407 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((97 / 640 : ℝ) - Real.pi * Real.exp (243 / 400 : ℝ)) := by
    rw [show (97 / 640 : ℝ) - Real.pi * Real.exp (243 / 400 : ℝ) =
      -(Real.pi * Real.exp (243 / 400 : ℝ) - (97 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (97 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (97 / 160 : ℝ)) := by
    have h := hpThetaJensenCell485_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1373785228407 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell485_endpointUpper :
    hpThetaJensenKernelEndpointUpper (97 / 320 : ℝ) (243 / 800 : ℝ) ≤ (1809843973 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (243 / 400 : ℝ)) (57674497369205717 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (243 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell485_product_upper
  have hD : (2726988560441 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (97 / 160 : ℝ) - (243 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell485_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell485_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (97 / 160 : ℝ) - (243 / 1600 : ℝ)) ≤
      (1 / (2726988560441 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2726988560441 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((243 / 1600 : ℝ) - Real.pi * Real.exp (97 / 160 : ℝ)) ≤
      (2 / (2726988560441 / 10000000000 : ℝ) : ℝ) := by
    rw [show (243 / 1600 : ℝ) - Real.pi * Real.exp (97 / 160 : ℝ) =
      -(Real.pi * Real.exp (97 / 160 : ℝ) - (243 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57674497369205717 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (57674497369205717 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell485_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (97 / 320 : ℝ) (243 / 800 : ℝ)) :
    (57161857 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1809843973 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell485_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell485_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell486_leftExp :
    (4589590167 / 2500000000 : ℝ) ≤ Real.exp (243 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (243 / 400 : ℝ) (254791431007 / 250000000000 : ℝ)
    (4589590167 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell486_rightExp :
    Real.exp (487 / 800 : ℝ) ≤ (18381322969 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (487 / 800 : ℝ) (31850172999 / 31250000000 : ℝ)
    (18381322969 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell486_denomUpper :
    Real.exp (56227885570149617 / 10000000000000000 : ℝ) ≤ (2766597901789 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56227885570149617 / 10000000000000000 : ℝ)
    (1192094855701 / 1000000000000 : ℝ) (2766597901789 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell486_denomLower :
    (686462179991 / 2500000000 : ℝ) ≤ Real.exp (1754768875240733 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1754768875240733 / 312500000000000 : ℝ) (23836288851 /
    20000000000 : ℝ) (686462179991 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell486_product_lower :
    (1802327468990733 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (243 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell486_leftExp
    (by norm_num : (0 : ℝ) ≤ (4589590167 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell486_product_upper :
    Real.pi * Real.exp (487 / 800 : ℝ) ≤ (57746635570149617 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell486_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell486_endpointLower :
    (355849087 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (243 / 800 : ℝ) (487 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1802327468990733 / 312500000000000 : ℝ) (Real.pi * Real.exp (243 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell486_product_lower
  have hD : Real.exp (Real.pi * Real.exp (487 / 800 : ℝ) - (243 / 1600 : ℝ)) ≤
      (2766597901789 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell486_denomUpper
    linarith [hpThetaJensenCell486_product_upper]
  have hi : (1 / (2766597901789 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (487 / 800 : ℝ) - (243 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2766597901789 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2766597901789 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((243 / 1600 : ℝ) - Real.pi * Real.exp (487 / 800 : ℝ)) := by
    rw [show (243 / 1600 : ℝ) - Real.pi * Real.exp (487 / 800 : ℝ) =
      -(Real.pi * Real.exp (487 / 800 : ℝ) - (243 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (243 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (243 / 400 : ℝ)) := by
    have h := hpThetaJensenCell486_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2766597901789 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell486_endpointUpper :
    hpThetaJensenKernelEndpointUpper (243 / 800 : ℝ) (487 / 1600 : ℝ) ≤ (3605406467 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (487 / 800 : ℝ)) (57746635570149617 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (487 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell486_product_upper
  have hD : (686462179991 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (243 / 400 : ℝ) - (487 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell486_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell486_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (243 / 400 : ℝ) - (487 / 3200 : ℝ)) ≤
      (1 / (686462179991 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (686462179991 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((487 / 3200 : ℝ) - Real.pi * Real.exp (243 / 400 : ℝ)) ≤
      (2 / (686462179991 / 2500000000 : ℝ) : ℝ) := by
    rw [show (487 / 3200 : ℝ) - Real.pi * Real.exp (243 / 400 : ℝ) =
      -(Real.pi * Real.exp (243 / 400 : ℝ) - (487 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57746635570149617 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (57746635570149617 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell486_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (243 / 800 : ℝ) (487 / 1600 : ℝ)) :
    (355849087 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3605406467 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell486_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell486_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell487_leftExp :
    (18381322967 / 10000000000 : ℝ) ≤ Real.exp (487 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (487 / 800 : ℝ) (1019205535967 / 1000000000000 : ℝ)
    (18381322967 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell487_rightExp :
    Real.exp (61 / 100 : ℝ) ≤ (18404313989 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 100 : ℝ) (509622674731 / 500000000000 : ℝ)
    (18404313989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell487_denomUpper :
    Real.exp (56296988997644477 / 10000000000000000 : ℝ) ≤ (696445562599 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56296988997644477 / 10000000000000000 : ℝ) (4769409257 /
    4000000000 : ℝ) (696445562599 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell487_denomLower :
    (1382432117139 / 5000000000 : ℝ) ≤ Real.exp (7027702147817933 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7027702147817933 / 1250000000000000 : ℝ) (596035752163 /
    500000000000 : ℝ) (1382432117139 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell487_product_lower :
    (7218327147817933 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (487 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell487_leftExp
    (by norm_num : (0 : ℝ) ≤ (18381322967 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell487_product_upper :
    Real.pi * Real.exp (61 / 100 : ℝ) ≤ (57818863997644477 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell487_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell487_endpointLower :
    (7088773827 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (487 / 1600 : ℝ) (61 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7218327147817933 / 1250000000000000 : ℝ) (Real.pi * Real.exp (487 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell487_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 100 : ℝ) - (487 / 3200 : ℝ)) ≤
      (696445562599 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell487_denomUpper
    linarith [hpThetaJensenCell487_product_upper]
  have hi : (1 / (696445562599 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 100 : ℝ) - (487 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (696445562599 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (696445562599 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((487 / 3200 : ℝ) - Real.pi * Real.exp (61 / 100 : ℝ)) := by
    rw [show (487 / 3200 : ℝ) - Real.pi * Real.exp (61 / 100 : ℝ) =
      -(Real.pi * Real.exp (61 / 100 : ℝ) - (487 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (487 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (487 / 800 : ℝ)) := by
    have h := hpThetaJensenCell487_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (696445562599 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell487_endpointUpper :
    hpThetaJensenKernelEndpointUpper (487 / 1600 : ℝ) (61 / 200 : ℝ) ≤ (57458341 / 80000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 100 : ℝ)) (57818863997644477 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell487_product_upper
  have hD : (1382432117139 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (487 / 800 : ℝ) - (61 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell487_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell487_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (487 / 800 : ℝ) - (61 / 400 : ℝ)) ≤
      (1 / (1382432117139 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1382432117139 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 400 : ℝ) - Real.pi * Real.exp (487 / 800 : ℝ)) ≤
      (2 / (1382432117139 / 5000000000 : ℝ) : ℝ) := by
    rw [show (61 / 400 : ℝ) - Real.pi * Real.exp (487 / 800 : ℝ) =
      -(Real.pi * Real.exp (487 / 800 : ℝ) - (61 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (57818863997644477 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (57818863997644477 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell487_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (487 / 1600 : ℝ) (61 / 200 : ℝ)) :
    (7088773827 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (57458341 / 80000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell487_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell487_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell488_leftExp :
    (18404313987 / 10000000000 : ℝ) ≤ Real.exp (61 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 100 : ℝ) (1019245349461 / 1000000000000 : ℝ)
    (18404313987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell488_rightExp :
    Real.exp (489 / 800 : ℝ) ≤ (9213666883 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (489 / 800 : ℝ) (1019285164511 / 1000000000000 : ℝ)
    (9213666883 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell488_denomUpper :
    Real.exp (28183091383964619 / 5000000000000000 : ℝ) ≤ (1402562485359 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28183091383964619 / 5000000000000000 : ℝ) (596305082551
    / 500000000000 : ℝ) (1402562485359 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell488_denomLower :
    (111361462193 / 400000000 : ℝ) ≤ Real.exp (7036340073380913 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7036340073380913 / 1250000000000000 : ℝ) (1192328957747
    / 1000000000000 : ℝ) (111361462193 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell488_product_lower :
    (7227355698380913 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell488_leftExp
    (by norm_num : (0 : ℝ) ≤ (18404313987 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell488_product_upper :
    Real.pi * Real.exp (489 / 800 : ℝ) ≤ (28945591383964619 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell488_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell488_endpointLower :
    (3530304349 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 200 : ℝ) (489 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7227355698380913 / 1250000000000000 : ℝ) (Real.pi * Real.exp (61 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell488_product_lower
  have hD : Real.exp (Real.pi * Real.exp (489 / 800 : ℝ) - (61 / 400 : ℝ)) ≤
      (1402562485359 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell488_denomUpper
    linarith [hpThetaJensenCell488_product_upper]
  have hi : (1 / (1402562485359 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (489 / 800 : ℝ) - (61 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1402562485359 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1402562485359 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 400 : ℝ) - Real.pi * Real.exp (489 / 800 : ℝ)) := by
    rw [show (61 / 400 : ℝ) - Real.pi * Real.exp (489 / 800 : ℝ) =
      -(Real.pi * Real.exp (489 / 800 : ℝ) - (61 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 100 : ℝ)) := by
    have h := hpThetaJensenCell488_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1402562485359 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell488_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 200 : ℝ) (489 / 1600 : ℝ) ≤ (1788453821 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (489 / 800 : ℝ)) (28945591383964619 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (489 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell488_product_upper
  have hD : (111361462193 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 100 : ℝ) - (489 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell488_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell488_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 100 : ℝ) - (489 / 3200 : ℝ)) ≤
      (1 / (111361462193 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (111361462193 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((489 / 3200 : ℝ) - Real.pi * Real.exp (61 / 100 : ℝ)) ≤
      (2 / (111361462193 / 400000000 : ℝ) : ℝ) := by
    rw [show (489 / 3200 : ℝ) - Real.pi * Real.exp (61 / 100 : ℝ) =
      -(Real.pi * Real.exp (61 / 100 : ℝ) - (489 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (28945591383964619 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (28945591383964619 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell488_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 200 : ℝ) (489 / 1600 : ℝ)) :
    (3530304349 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1788453821 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell488_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell488_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell489_leftExp :
    (4606833441 / 2500000000 : ℝ) ≤ Real.exp (489 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (489 / 800 : ℝ) (101928516451 / 100000000000 : ℝ)
    (4606833441 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell489_rightExp :
    Real.exp (49 / 80 : ℝ) ≤ (3690076467 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 80 : ℝ) (203864996223 / 200000000000 : ℝ)
    (3690076467 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell489_denomUpper :
    Real.exp (11287093398191931 / 2000000000000000 : ℝ) ≤ (706156886033 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11287093398191931 / 2000000000000000 : ℝ) (1192868408897
    / 1000000000000 : ℝ) (706156886033 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell489_denomLower :
    (2803367147661 / 10000000000 : ℝ) ≤ Real.exp (1761247322947259 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1761247322947259 / 312500000000000 : ℝ) (596293401731 /
    500000000000 : ℝ) (2803367147661 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell489_product_lower :
    (1809098885447259 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (489 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell489_leftExp
    (by norm_num : (0 : ℝ) ≤ (4606833441 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell489_product_upper :
    Real.pi * Real.exp (49 / 80 : ℝ) ≤ (11592718398191931 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell489_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell489_endpointLower :
    (7032486667 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (489 / 1600 : ℝ) (49 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1809098885447259 / 312500000000000 : ℝ) (Real.pi * Real.exp (489 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell489_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 80 : ℝ) - (489 / 3200 : ℝ)) ≤
      (706156886033 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell489_denomUpper
    linarith [hpThetaJensenCell489_product_upper]
  have hi : (1 / (706156886033 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 80 : ℝ) - (489 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (706156886033 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (706156886033 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((489 / 3200 : ℝ) - Real.pi * Real.exp (49 / 80 : ℝ)) := by
    rw [show (489 / 3200 : ℝ) - Real.pi * Real.exp (49 / 80 : ℝ) =
      -(Real.pi * Real.exp (49 / 80 : ℝ) - (489 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (489 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (489 / 800 : ℝ)) := by
    have h := hpThetaJensenCell489_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (706156886033 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell489_endpointUpper :
    hpThetaJensenKernelEndpointUpper (489 / 1600 : ℝ) (49 / 160 : ℝ) ≤ (3562690613 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 80 : ℝ)) (11592718398191931 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell489_product_upper
  have hD : (2803367147661 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (489 / 800 : ℝ) - (49 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell489_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell489_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (489 / 800 : ℝ) - (49 / 320 : ℝ)) ≤
      (1 / (2803367147661 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2803367147661 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 320 : ℝ) - Real.pi * Real.exp (489 / 800 : ℝ)) ≤
      (2 / (2803367147661 / 10000000000 : ℝ) : ℝ) := by
    rw [show (49 / 320 : ℝ) - Real.pi * Real.exp (489 / 800 : ℝ) =
      -(Real.pi * Real.exp (489 / 800 : ℝ) - (49 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11592718398191931 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (11592718398191931 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell489_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (489 / 1600 : ℝ) (49 / 160 : ℝ)) :
    (7032486667 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3562690613 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell489_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell489_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell490_leftExp :
    (18450382333 / 10000000000 : ℝ) ≤ Real.exp (49 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (49 / 80 : ℝ) (509662490557 / 500000000000 : ℝ)
    (18450382333 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell490_rightExp :
    Real.exp (491 / 800 : ℝ) ≤ (18473459733 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (491 / 800 : ℝ) (40774591971 / 40000000000 : ℝ)
    (18473459733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell490_denomUpper :
    Real.exp (56504841782974669 / 10000000000000000 : ℝ) ≤ (1422145734577 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56504841782974669 / 10000000000000000 : ℝ) (11931270463
    / 10000000000 : ℝ) (1422145734577 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell490_denomLower :
    (2822857493383 / 10000000000 : ℝ) ≤ Real.exp (7053649816786767 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7053649816786767 / 1250000000000000 : ℝ) (1192845042113
    / 1000000000000 : ℝ) (2822857493383 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell490_product_lower :
    (7245446691786767 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (49 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell490_leftExp
    (by norm_num : (0 : ℝ) ≤ (18450382333 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell490_product_upper :
    Real.pi * Real.exp (491 / 800 : ℝ) ≤ (58036091782974669 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell490_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell490_endpointLower :
    (3502204019 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 160 : ℝ) (491 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7245446691786767 / 1250000000000000 : ℝ) (Real.pi * Real.exp (49 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell490_product_lower
  have hD : Real.exp (Real.pi * Real.exp (491 / 800 : ℝ) - (49 / 320 : ℝ)) ≤
      (1422145734577 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell490_denomUpper
    linarith [hpThetaJensenCell490_product_upper]
  have hi : (1 / (1422145734577 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (491 / 800 : ℝ) - (49 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1422145734577 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1422145734577 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((49 / 320 : ℝ) - Real.pi * Real.exp (491 / 800 : ℝ)) := by
    rw [show (49 / 320 : ℝ) - Real.pi * Real.exp (491 / 800 : ℝ) =
      -(Real.pi * Real.exp (491 / 800 : ℝ) - (49 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (49 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (49 / 80 : ℝ)) := by
    have h := hpThetaJensenCell490_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1422145734577 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell490_endpointUpper :
    hpThetaJensenKernelEndpointUpper (49 / 160 : ℝ) (491 / 1600 : ℝ) ≤ (1419398153 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (491 / 800 : ℝ)) (58036091782974669 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (491 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell490_product_upper
  have hD : (2822857493383 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (49 / 80 : ℝ) - (491 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell490_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell490_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (49 / 80 : ℝ) - (491 / 3200 : ℝ)) ≤
      (1 / (2822857493383 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2822857493383 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((491 / 3200 : ℝ) - Real.pi * Real.exp (49 / 80 : ℝ)) ≤
      (2 / (2822857493383 / 10000000000 : ℝ) : ℝ) := by
    rw [show (491 / 3200 : ℝ) - Real.pi * Real.exp (49 / 80 : ℝ) =
      -(Real.pi * Real.exp (49 / 80 : ℝ) - (491 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58036091782974669 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (58036091782974669 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell490_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (49 / 160 : ℝ) (491 / 1600 : ℝ)) :
    (3502204019 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1419398153 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell490_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell490_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell491_leftExp :
    (4618364933 / 2500000000 : ℝ) ≤ Real.exp (491 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (491 / 800 : ℝ) (509682399637 / 500000000000 : ℝ)
    (4618364933 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell491_rightExp :
    Real.exp (123 / 200 : ℝ) ≤ (4624141499 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (123 / 200 : ℝ) (101940461899 / 100000000000 : ℝ)
    (4624141499 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell491_denomUpper :
    Real.exp (14143576814267907 / 2500000000000000 : ℝ) ≤ (2864118258831 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (14143576814267907 / 2500000000000000 : ℝ) (298346519491
    / 250000000000 : ℝ) (2864118258831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell491_denomLower :
    (710627272583 / 2500000000 : ℝ) ≤ Real.exp (1765580415824167 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1765580415824167 / 312500000000000 : ℝ) (1908965879 /
    1600000000 : ℝ) (710627272583 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell491_product_lower :
    (1813627290824167 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (491 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell491_leftExp
    (by norm_num : (0 : ℝ) ≤ (4618364933 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell491_product_upper :
    Real.pi * Real.exp (123 / 200 : ℝ) ≤ (14527170564267907 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell491_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell491_endpointLower :
    (3488186561 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (491 / 1600 : ℝ) (123 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1813627290824167 / 312500000000000 : ℝ) (Real.pi * Real.exp (491 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell491_product_lower
  have hD : Real.exp (Real.pi * Real.exp (123 / 200 : ℝ) - (491 / 3200 : ℝ)) ≤
      (2864118258831 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell491_denomUpper
    linarith [hpThetaJensenCell491_product_upper]
  have hi : (1 / (2864118258831 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (123 / 200 : ℝ) - (491 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2864118258831 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2864118258831 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((491 / 3200 : ℝ) - Real.pi * Real.exp (123 / 200 : ℝ)) := by
    rw [show (491 / 3200 : ℝ) - Real.pi * Real.exp (123 / 200 : ℝ) =
      -(Real.pi * Real.exp (123 / 200 : ℝ) - (491 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (491 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (491 / 800 : ℝ)) := by
    have h := hpThetaJensenCell491_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2864118258831 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell491_endpointUpper :
    hpThetaJensenKernelEndpointUpper (491 / 1600 : ℝ) (123 / 400 : ℝ) ≤ (7068644211 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (123 / 200 : ℝ)) (14527170564267907 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (123 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell491_product_upper
  have hD : (710627272583 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (491 / 800 : ℝ) - (123 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell491_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell491_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (491 / 800 : ℝ) - (123 / 800 : ℝ)) ≤
      (1 / (710627272583 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (710627272583 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((123 / 800 : ℝ) - Real.pi * Real.exp (491 / 800 : ℝ)) ≤
      (2 / (710627272583 / 2500000000 : ℝ) : ℝ) := by
    rw [show (123 / 800 : ℝ) - Real.pi * Real.exp (491 / 800 : ℝ) =
      -(Real.pi * Real.exp (491 / 800 : ℝ) - (123 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14527170564267907 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (14527170564267907 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell491_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (491 / 1600 : ℝ) (123 / 400 : ℝ)) :
    (3488186561 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7068644211 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell491_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell491_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell492_leftExp :
    (3699313199 / 2000000000 : ℝ) ≤ Real.exp (123 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (123 / 200 : ℝ) (1019404618989 / 1000000000000 : ℝ)
    (3699313199 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell492_rightExp :
    Real.exp (493 / 800 : ℝ) ≤ (462992529 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (493 / 800 : ℝ) (1019444440261 / 1000000000000 : ℝ)
    (462992529 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell492_denomUpper :
    Real.exp (1416096588158697 / 250000000000000 : ℝ) ≤ (576821888377 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1416096588158697 / 250000000000000 : ℝ) (1193645504543 /
    1000000000000 : ℝ) (576821888377 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell492_denomLower :
    (1431161724429 / 5000000000 : ℝ) ≤ Real.exp (1414200968934101 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1414200968934101 / 250000000000000 : ℝ) (596681350439 /
    500000000000 : ℝ) (1431161724429 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell492_product_lower :
    (1452716593934101 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (123 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell492_leftExp
    (by norm_num : (0 : ℝ) ≤ (3699313199 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell492_product_upper :
    Real.pi * Real.exp (493 / 800 : ℝ) ≤ (1454534088158697 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell492_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell492_endpointLower :
    (434273889 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (123 / 400 : ℝ) (493 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1452716593934101 / 250000000000000 : ℝ) (Real.pi * Real.exp (123 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell492_product_lower
  have hD : Real.exp (Real.pi * Real.exp (493 / 800 : ℝ) - (123 / 800 : ℝ)) ≤
      (576821888377 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell492_denomUpper
    linarith [hpThetaJensenCell492_product_upper]
  have hi : (1 / (576821888377 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (493 / 800 : ℝ) - (123 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (576821888377 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (576821888377 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((123 / 800 : ℝ) - Real.pi * Real.exp (493 / 800 : ℝ)) := by
    rw [show (123 / 800 : ℝ) - Real.pi * Real.exp (493 / 800 : ℝ) =
      -(Real.pi * Real.exp (493 / 800 : ℝ) - (123 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (123 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (123 / 200 : ℝ)) := by
    have h := hpThetaJensenCell492_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (576821888377 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell492_endpointUpper :
    hpThetaJensenKernelEndpointUpper (123 / 400 : ℝ) (493 / 1600 : ℝ) ≤ (1760085469 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (493 / 800 : ℝ)) (1454534088158697 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (493 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell492_product_upper
  have hD : (1431161724429 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (123 / 200 : ℝ) - (493 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell492_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell492_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (123 / 200 : ℝ) - (493 / 3200 : ℝ)) ≤
      (1 / (1431161724429 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1431161724429 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((493 / 3200 : ℝ) - Real.pi * Real.exp (123 / 200 : ℝ)) ≤
      (2 / (1431161724429 / 5000000000 : ℝ) : ℝ) := by
    rw [show (493 / 3200 : ℝ) - Real.pi * Real.exp (123 / 200 : ℝ) =
      -(Real.pi * Real.exp (123 / 200 : ℝ) - (493 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1454534088158697 / 250000000000000 : ℝ) ^ 2 - 6 *
      (1454534088158697 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell492_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (123 / 400 : ℝ) (493 / 1600 : ℝ)) :
    (434273889 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1760085469 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell492_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell492_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell493_leftExp :
    (18519701159 / 10000000000 : ℝ) ≤ Real.exp (493 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (493 / 800 : ℝ) (50972222013 / 50000000000 : ℝ)
    (18519701159 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell493_rightExp :
    Real.exp (247 / 400 : ℝ) ≤ (18542865261 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (247 / 400 : ℝ) (1019484263087 / 1000000000000 : ℝ)
    (18542865261 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell493_denomUpper :
    Real.exp (56713510703900773 / 10000000000000000 : ℝ) ≤ (726066640743 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56713510703900773 / 10000000000000000 : ℝ)
    (1193905326693 / 1000000000000 : ℝ) (726066640743 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell493_denomLower :
    (720575524447 / 2500000000 : ℝ) ≤ Real.exp (7079699375438141 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7079699375438141 / 1250000000000000 : ℝ) (119362212229 /
    100000000000 : ℝ) (720575524447 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell493_product_lower :
    (7272668125438141 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (493 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell493_leftExp
    (by norm_num : (0 : ℝ) ≤ (18519701159 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell493_product_upper :
    Real.pi * Real.exp (247 / 400 : ℝ) ≤ (58254135703900773 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell493_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell493_endpointLower :
    (6920435647 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (493 / 1600 : ℝ) (247 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7272668125438141 / 1250000000000000 : ℝ) (Real.pi * Real.exp (493 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell493_product_lower
  have hD : Real.exp (Real.pi * Real.exp (247 / 400 : ℝ) - (493 / 3200 : ℝ)) ≤
      (726066640743 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell493_denomUpper
    linarith [hpThetaJensenCell493_product_upper]
  have hi : (1 / (726066640743 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (247 / 400 : ℝ) - (493 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (726066640743 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (726066640743 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((493 / 3200 : ℝ) - Real.pi * Real.exp (247 / 400 : ℝ)) := by
    rw [show (493 / 3200 : ℝ) - Real.pi * Real.exp (247 / 400 : ℝ) =
      -(Real.pi * Real.exp (247 / 400 : ℝ) - (493 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (493 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (493 / 800 : ℝ)) := by
    have h := hpThetaJensenCell493_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (726066640743 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell493_endpointUpper :
    hpThetaJensenKernelEndpointUpper (493 / 1600 : ℝ) (247 / 800 : ℝ) ≤ (7012084067 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (247 / 400 : ℝ)) (58254135703900773 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (247 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell493_product_upper
  have hD : (720575524447 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (493 / 800 : ℝ) - (247 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell493_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell493_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (493 / 800 : ℝ) - (247 / 1600 : ℝ)) ≤
      (1 / (720575524447 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (720575524447 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((247 / 1600 : ℝ) - Real.pi * Real.exp (493 / 800 : ℝ)) ≤
      (2 / (720575524447 / 2500000000 : ℝ) : ℝ) := by
    rw [show (247 / 1600 : ℝ) - Real.pi * Real.exp (493 / 800 : ℝ) =
      -(Real.pi * Real.exp (493 / 800 : ℝ) - (247 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58254135703900773 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (58254135703900773 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell493_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (493 / 1600 : ℝ) (247 / 800 : ℝ)) :
    (6920435647 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7012084067 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell493_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell493_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell494_leftExp :
    (927143263 / 500000000 : ℝ) ≤ Real.exp (247 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (247 / 400 : ℝ) (509742131543 / 500000000000 : ℝ)
    (927143263 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell494_rightExp :
    Real.exp (99 / 160 : ℝ) ≤ (580189323 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (99 / 160 : ℝ) (1019524087469 / 1000000000000 : ℝ)
    (580189323 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell494_denomUpper :
    Real.exp (1774476528311539 / 312500000000000 : ℝ) ≤ (2924591183563 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1774476528311539 / 312500000000000 : ℝ) (1194165545081 /
    1000000000000 : ℝ) (2924591183563 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell494_denomLower :
    (1451223290289 / 5000000000 : ℝ) ≤ Real.exp (354420263486837 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (354420263486837 / 62500000000000 : ℝ) (18654405301 /
    15625000000 : ℝ) (1451223290289 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell494_product_lower :
    (364088232236837 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (247 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell494_leftExp
    (by norm_num : (0 : ℝ) ≤ (927143263 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell494_product_upper :
    Real.pi * Real.exp (99 / 160 : ℝ) ≤ (1822718715811539 / 312500000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell494_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell494_endpointLower :
    (6892533691 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (247 / 800 : ℝ) (99 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (364088232236837 / 62500000000000 : ℝ) (Real.pi * Real.exp (247 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell494_product_lower
  have hD : Real.exp (Real.pi * Real.exp (99 / 160 : ℝ) - (247 / 1600 : ℝ)) ≤
      (2924591183563 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell494_denomUpper
    linarith [hpThetaJensenCell494_product_upper]
  have hi : (1 / (2924591183563 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (99 / 160 : ℝ) - (247 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2924591183563 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2924591183563 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((247 / 1600 : ℝ) - Real.pi * Real.exp (99 / 160 : ℝ)) := by
    rw [show (247 / 1600 : ℝ) - Real.pi * Real.exp (99 / 160 : ℝ) =
      -(Real.pi * Real.exp (99 / 160 : ℝ) - (247 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (247 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (247 / 400 : ℝ)) := by
    have h := hpThetaJensenCell494_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2924591183563 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell494_endpointUpper :
    hpThetaJensenKernelEndpointUpper (247 / 800 : ℝ) (99 / 320 : ℝ) ≤ (6983871091 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (99 / 160 : ℝ)) (1822718715811539 / 312500000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (99 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell494_product_upper
  have hD : (1451223290289 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (247 / 400 : ℝ) - (99 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell494_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell494_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (247 / 400 : ℝ) - (99 / 640 : ℝ)) ≤
      (1 / (1451223290289 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1451223290289 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((99 / 640 : ℝ) - Real.pi * Real.exp (247 / 400 : ℝ)) ≤
      (2 / (1451223290289 / 5000000000 : ℝ) : ℝ) := by
    rw [show (99 / 640 : ℝ) - Real.pi * Real.exp (247 / 400 : ℝ) =
      -(Real.pi * Real.exp (247 / 400 : ℝ) - (99 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1822718715811539 / 312500000000000 : ℝ) ^ 2 - 6 *
      (1822718715811539 / 312500000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell494_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (247 / 800 : ℝ) (99 / 320 : ℝ)) :
    (6892533691 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6983871091 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell494_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell494_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell495_leftExp :
    (9283029167 / 5000000000 : ℝ) ≤ Real.exp (99 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (99 / 160 : ℝ) (254881021867 / 250000000000 : ℝ)
    (9283029167 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell495_rightExp :
    Real.exp (31 / 50 : ℝ) ≤ (18589280419 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31 / 50 : ℝ) (509781956703 / 500000000000 : ℝ)
    (18589280419 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell495_denomUpper :
    Real.exp (56853078239367467 / 10000000000000000 : ℝ) ≤ (1472542439343 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56853078239367467 / 10000000000000000 : ℝ)
    (1194426160341 / 1000000000000 : ℝ) (1472542439343 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell495_denomLower :
    (2922758456859 / 10000000000 : ℝ) ≤ Real.exp (3548561270851733 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3548561270851733 / 625000000000000 : ℝ) (149267769057 /
    125000000000 : ℝ) (2922758456859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell495_product_lower :
    (3645436270851733 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (99 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell495_leftExp
    (by norm_num : (0 : ℝ) ≤ (9283029167 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell495_product_upper :
    Real.pi * Real.exp (31 / 50 : ℝ) ≤ (58399953239367467 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell495_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell495_endpointLower :
    (6864676663 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 320 : ℝ) (31 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3645436270851733 / 625000000000000 : ℝ) (Real.pi * Real.exp (99 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell495_product_lower
  have hD : Real.exp (Real.pi * Real.exp (31 / 50 : ℝ) - (99 / 640 : ℝ)) ≤
      (1472542439343 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell495_denomUpper
    linarith [hpThetaJensenCell495_product_upper]
  have hi : (1 / (1472542439343 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (31 / 50 : ℝ) - (99 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1472542439343 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1472542439343 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((99 / 640 : ℝ) - Real.pi * Real.exp (31 / 50 : ℝ)) := by
    rw [show (99 / 640 : ℝ) - Real.pi * Real.exp (31 / 50 : ℝ) =
      -(Real.pi * Real.exp (31 / 50 : ℝ) - (99 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (99 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (99 / 160 : ℝ)) := by
    have h := hpThetaJensenCell495_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1472542439343 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell495_endpointUpper :
    hpThetaJensenKernelEndpointUpper (99 / 320 : ℝ) (31 / 100 : ℝ) ≤ (6955703251 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (31 / 50 : ℝ)) (58399953239367467 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (31 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell495_product_upper
  have hD : (2922758456859 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (99 / 160 : ℝ) - (31 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell495_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell495_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (99 / 160 : ℝ) - (31 / 200 : ℝ)) ≤
      (1 / (2922758456859 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2922758456859 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((31 / 200 : ℝ) - Real.pi * Real.exp (99 / 160 : ℝ)) ≤
      (2 / (2922758456859 / 10000000000 : ℝ) : ℝ) := by
    rw [show (31 / 200 : ℝ) - Real.pi * Real.exp (99 / 160 : ℝ) =
      -(Real.pi * Real.exp (99 / 160 : ℝ) - (31 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58399953239367467 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (58399953239367467 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell495_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (99 / 320 : ℝ) (31 / 100 : ℝ)) :
    (6864676663 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6955703251 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell495_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell495_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell496_leftExp :
    (18589280417 / 10000000000 : ℝ) ≤ Real.exp (31 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (31 / 50 : ℝ) (203912782681 / 200000000000 : ℝ)
    (18589280417 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell496_rightExp :
    Real.exp (497 / 800 : ℝ) ≤ (18612531549 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (497 / 800 : ℝ) (10196037409 / 10000000000 : ℝ)
    (18612531549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell496_denomUpper :
    Real.exp (56922998826617557 / 10000000000000000 : ℝ) ≤ (2965749244081 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (56922998826617557 / 10000000000000000 : ℝ)
    (1194687173163 / 1000000000000 : ℝ) (2965749244081 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell496_denomLower :
    (45988114101 / 156250000 : ℝ) ≤ Real.exp (7105851205475483 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7105851205475483 / 1250000000000000 : ℝ) (1194402762523
    / 1000000000000 : ℝ) (45988114101 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell496_product_lower :
    (7299991830475483 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (31 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell496_leftExp
    (by norm_num : (0 : ℝ) ≤ (18589280417 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell496_product_upper :
    Real.pi * Real.exp (497 / 800 : ℝ) ≤ (58472998826617557 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell496_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell496_endpointLower :
    (3418432427 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 100 : ℝ) (497 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7299991830475483 / 1250000000000000 : ℝ) (Real.pi * Real.exp (31 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell496_product_lower
  have hD : Real.exp (Real.pi * Real.exp (497 / 800 : ℝ) - (31 / 200 : ℝ)) ≤
      (2965749244081 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell496_denomUpper
    linarith [hpThetaJensenCell496_product_upper]
  have hi : (1 / (2965749244081 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (497 / 800 : ℝ) - (31 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2965749244081 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2965749244081 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((31 / 200 : ℝ) - Real.pi * Real.exp (497 / 800 : ℝ)) := by
    rw [show (31 / 200 : ℝ) - Real.pi * Real.exp (497 / 800 : ℝ) =
      -(Real.pi * Real.exp (497 / 800 : ℝ) - (31 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (31 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (31 / 50 : ℝ)) := by
    have h := hpThetaJensenCell496_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2965749244081 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell496_endpointUpper :
    hpThetaJensenKernelEndpointUpper (31 / 100 : ℝ) (497 / 1600 : ℝ) ≤ (6927580851 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (497 / 800 : ℝ)) (58472998826617557 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (497 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell496_product_upper
  have hD : (45988114101 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (31 / 50 : ℝ) - (497 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell496_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell496_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (31 / 50 : ℝ) - (497 / 3200 : ℝ)) ≤
      (1 / (45988114101 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (45988114101 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((497 / 3200 : ℝ) - Real.pi * Real.exp (31 / 50 : ℝ)) ≤
      (2 / (45988114101 / 156250000 : ℝ) : ℝ) := by
    rw [show (497 / 3200 : ℝ) - Real.pi * Real.exp (31 / 50 : ℝ) =
      -(Real.pi * Real.exp (31 / 50 : ℝ) - (497 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (58472998826617557 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (58472998826617557 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell496_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (31 / 100 : ℝ) (497 / 1600 : ℝ)) :
    (3418432427 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6927580851 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell496_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell496_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell497_leftExp :
    (18612531547 / 10000000000 : ℝ) ≤ Real.exp (497 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (497 / 800 : ℝ) (1019603740899 / 1000000000000 : ℝ)
    (18612531547 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell497_rightExp :
    Real.exp (249 / 400 : ℝ) ≤ (232947647 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (249 / 400 : ℝ) (1019643569949 / 1000000000000 : ℝ)
    (232947647 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell497_denomUpper :
    Real.exp (712412634681671 / 125000000000000 : ℝ) ≤ (2986585887901 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (712412634681671 / 125000000000000 : ℝ) (238989716837 /
    200000000000 : ℝ) (2986585887901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell497_denomLower :
    (740972677859 / 2500000000 : ℝ) ≤ Real.exp (7114591275975353 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7114591275975353 / 1250000000000000 : ℝ) (597331885073 /
    500000000000 : ℝ) (740972677859 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell497_product_lower :
    (7309122525975353 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (497 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell497_leftExp
    (by norm_num : (0 : ℝ) ≤ (18612531547 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell497_product_upper :
    Real.pi * Real.exp (249 / 400 : ℝ) ≤ (731826697181671 / 125000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell497_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell497_endpointLower :
    (6809098567 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (497 / 1600 : ℝ) (249 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7309122525975353 / 1250000000000000 : ℝ) (Real.pi * Real.exp (497 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell497_product_lower
  have hD : Real.exp (Real.pi * Real.exp (249 / 400 : ℝ) - (497 / 3200 : ℝ)) ≤
      (2986585887901 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell497_denomUpper
    linarith [hpThetaJensenCell497_product_upper]
  have hi : (1 / (2986585887901 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (249 / 400 : ℝ) - (497 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2986585887901 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2986585887901 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((497 / 3200 : ℝ) - Real.pi * Real.exp (249 / 400 : ℝ)) := by
    rw [show (497 / 3200 : ℝ) - Real.pi * Real.exp (249 / 400 : ℝ) =
      -(Real.pi * Real.exp (249 / 400 : ℝ) - (497 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (497 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (497 / 800 : ℝ)) := by
    have h := hpThetaJensenCell497_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2986585887901 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell497_endpointUpper :
    hpThetaJensenKernelEndpointUpper (497 / 1600 : ℝ) (249 / 800 : ℝ) ≤ (1724876047 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (249 / 400 : ℝ)) (731826697181671 / 125000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (249 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell497_product_upper
  have hD : (740972677859 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (497 / 800 : ℝ) - (249 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell497_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell497_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (497 / 800 : ℝ) - (249 / 1600 : ℝ)) ≤
      (1 / (740972677859 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (740972677859 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((249 / 1600 : ℝ) - Real.pi * Real.exp (497 / 800 : ℝ)) ≤
      (2 / (740972677859 / 2500000000 : ℝ) : ℝ) := by
    rw [show (249 / 1600 : ℝ) - Real.pi * Real.exp (497 / 800 : ℝ) =
      -(Real.pi * Real.exp (497 / 800 : ℝ) - (249 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (731826697181671 / 125000000000000 : ℝ) ^ 2 - 6 *
      (731826697181671 / 125000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell497_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (497 / 1600 : ℝ) (249 / 800 : ℝ)) :
    (6809098567 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1724876047 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell497_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell497_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell498_leftExp :
    (18635811759 / 10000000000 : ℝ) ≤ Real.exp (249 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (249 / 400 : ℝ) (254910892487 / 250000000000 : ℝ)
    (18635811759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell498_rightExp :
    Real.exp (499 / 800 : ℝ) ≤ (1865912109 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (499 / 800 : ℝ) (1019683400553 / 1000000000000 : ℝ)
    (1865912109 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell498_denomUpper :
    Real.exp (5706311420249637 / 1000000000000000 : ℝ) ≤ (751899109561 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5706311420249637 / 1000000000000000 : ℝ) (597605197043 /
    500000000000 : ℝ) (751899109561 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell498_denomLower :
    (596942858313 / 2000000000 : ℝ) ≤ Real.exp (7123342766947541 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7123342766947541 / 1250000000000000 : ℝ) (1194925175971
    / 1000000000000 : ℝ) (596942858313 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell498_product_lower :
    (7318264641947541 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (249 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell498_leftExp
    (by norm_num : (0 : ℝ) ≤ (18635811759 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell498_product_upper :
    Real.pi * Real.exp (499 / 800 : ℝ) ≤ (5861936420249637 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell498_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell498_endpointLower :
    (1695344523 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (249 / 800 : ℝ) (499 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (7318264641947541 / 1250000000000000 : ℝ) (Real.pi * Real.exp (249 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell498_product_lower
  have hD : Real.exp (Real.pi * Real.exp (499 / 800 : ℝ) - (249 / 1600 : ℝ)) ≤
      (751899109561 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell498_denomUpper
    linarith [hpThetaJensenCell498_product_upper]
  have hi : (1 / (751899109561 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (499 / 800 : ℝ) - (249 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (751899109561 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (751899109561 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((249 / 1600 : ℝ) - Real.pi * Real.exp (499 / 800 : ℝ)) := by
    rw [show (249 / 1600 : ℝ) - Real.pi * Real.exp (499 / 800 : ℝ) =
      -(Real.pi * Real.exp (499 / 800 : ℝ) - (249 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (249 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (249 / 400 : ℝ)) := by
    have h := hpThetaJensenCell498_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (751899109561 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell498_endpointUpper :
    hpThetaJensenKernelEndpointUpper (249 / 800 : ℝ) (499 / 1600 : ℝ) ≤ (6871473563 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (499 / 800 : ℝ)) (5861936420249637 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (499 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell498_product_upper
  have hD : (596942858313 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (249 / 400 : ℝ) - (499 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell498_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell498_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (249 / 400 : ℝ) - (499 / 3200 : ℝ)) ≤
      (1 / (596942858313 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (596942858313 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((499 / 3200 : ℝ) - Real.pi * Real.exp (249 / 400 : ℝ)) ≤
      (2 / (596942858313 / 2000000000 : ℝ) : ℝ) := by
    rw [show (499 / 3200 : ℝ) - Real.pi * Real.exp (249 / 400 : ℝ) =
      -(Real.pi * Real.exp (249 / 400 : ℝ) - (499 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5861936420249637 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5861936420249637 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell498_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (249 / 800 : ℝ) (499 / 1600 : ℝ)) :
    (1695344523 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6871473563 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell498_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell498_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell499_leftExp :
    (291548767 / 156250000 : ℝ) ≤ Real.exp (499 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (499 / 800 : ℝ) (127460425069 / 125000000000 : ℝ)
    (291548767 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell499_rightExp :
    Real.exp (5 / 8 : ℝ) ≤ (747298383 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5 / 8 : ℝ) (509861616357 / 500000000000 : ℝ)
    (747298383 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell499_denomUpper :
    Real.exp (2285332368944119 / 400000000000000 : ℝ) ≤ (1514391269373 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2285332368944119 / 400000000000000 : ℝ) (149434075441 /
    125000000000 : ℝ) (1514391269373 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell499_denomLower :
    (1502855833723 / 5000000000 : ℝ) ≤ Real.exp (111439151439633 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (111439151439633 / 19531250000000 : ℝ) (597593490323 /
    500000000000 : ℝ) (1502855833723 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell499_product_lower :
    (114490909252133 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (499 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell499_leftExp
    (by norm_num : (0 : ℝ) ≤ (291548767 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell499_product_upper :
    Real.pi * Real.exp (5 / 8 : ℝ) ≤ (2347707368944119 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell499_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell499_endpointLower :
    (3376851861 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (499 / 1600 : ℝ) (5 / 16 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (114490909252133 / 19531250000000 : ℝ) (Real.pi * Real.exp (499 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell499_product_lower
  have hD : Real.exp (Real.pi * Real.exp (5 / 8 : ℝ) - (499 / 3200 : ℝ)) ≤
      (1514391269373 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell499_denomUpper
    linarith [hpThetaJensenCell499_product_upper]
  have hi : (1 / (1514391269373 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (5 / 8 : ℝ) - (499 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1514391269373 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1514391269373 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((499 / 3200 : ℝ) - Real.pi * Real.exp (5 / 8 : ℝ)) := by
    rw [show (499 / 3200 : ℝ) - Real.pi * Real.exp (5 / 8 : ℝ) =
      -(Real.pi * Real.exp (5 / 8 : ℝ) - (499 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (499 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (499 / 800 : ℝ)) := by
    have h := hpThetaJensenCell499_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1514391269373 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell499_endpointUpper :
    hpThetaJensenKernelEndpointUpper (499 / 1600 : ℝ) (5 / 16 : ℝ) ≤ (1710872319 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (5 / 8 : ℝ)) (2347707368944119 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (5 / 16 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell499_product_upper
  have hD : (1502855833723 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (499 / 800 : ℝ) - (5 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell499_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell499_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (499 / 800 : ℝ) - (5 / 32 : ℝ)) ≤
      (1 / (1502855833723 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1502855833723 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((5 / 32 : ℝ) - Real.pi * Real.exp (499 / 800 : ℝ)) ≤
      (2 / (1502855833723 / 5000000000 : ℝ) : ℝ) := by
    rw [show (5 / 32 : ℝ) - Real.pi * Real.exp (499 / 800 : ℝ) =
      -(Real.pi * Real.exp (499 / 800 : ℝ) - (5 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2347707368944119 / 400000000000000 : ℝ) ^ 2 - 6 *
      (2347707368944119 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell499_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (499 / 1600 : ℝ) (5 / 16 : ℝ)) :
    (3376851861 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1710872319 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell499_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell499_endpointUpper

def hpThetaJensenCellsBatch024Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (455444377 / 625000000 : ℝ)
  | 1 => (145173041 / 200000000 : ℝ)
  | 2 => (3615117473 / 5000000000 : ℝ)
  | 3 => (7201859043 / 10000000000 : ℝ)
  | 4 => (896690583 / 1250000000 : ℝ)
  | 5 => (57161857 / 80000000 : ℝ)
  | 6 => (355849087 / 500000000 : ℝ)
  | 7 => (7088773827 / 10000000000 : ℝ)
  | 8 => (3530304349 / 5000000000 : ℝ)
  | 9 => (7032486667 / 10000000000 : ℝ)
  | 10 => (3502204019 / 5000000000 : ℝ)
  | 11 => (3488186561 / 5000000000 : ℝ)
  | 12 => (434273889 / 625000000 : ℝ)
  | 13 => (6920435647 / 10000000000 : ℝ)
  | 14 => (6892533691 / 10000000000 : ℝ)
  | 15 => (6864676663 / 10000000000 : ℝ)
  | 16 => (3418432427 / 5000000000 : ℝ)
  | 17 => (6809098567 / 10000000000 : ℝ)
  | 18 => (1695344523 / 2500000000 : ℝ)
  | 19 => (3376851861 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch024Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7382819229 / 10000000000 : ℝ)
  | 1 => (1838511959 / 2500000000 : ℝ)
  | 2 => (7325317479 / 10000000000 : ℝ)
  | 3 => (7296628489 / 10000000000 : ℝ)
  | 4 => (3633990593 / 5000000000 : ℝ)
  | 5 => (1809843973 / 2500000000 : ℝ)
  | 6 => (3605406467 / 5000000000 : ℝ)
  | 7 => (57458341 / 80000000 : ℝ)
  | 8 => (1788453821 / 2500000000 : ℝ)
  | 9 => (3562690613 / 5000000000 : ℝ)
  | 10 => (1419398153 / 2000000000 : ℝ)
  | 11 => (7068644211 / 10000000000 : ℝ)
  | 12 => (1760085469 / 2500000000 : ℝ)
  | 13 => (7012084067 / 10000000000 : ℝ)
  | 14 => (6983871091 / 10000000000 : ℝ)
  | 15 => (6955703251 / 10000000000 : ℝ)
  | 16 => (6927580851 / 10000000000 : ℝ)
  | 17 => (1724876047 / 2500000000 : ℝ)
  | 18 => (6871473563 / 10000000000 : ℝ)
  | 19 => (1710872319 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch024_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch024Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch024Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell480_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell481_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell482_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell483_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell484_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell485_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell486_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell487_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell488_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell489_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell490_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell491_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell492_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell493_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell494_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell495_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell496_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell497_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell498_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell499_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper] at h ⊢
    exact h

end HodgeProofHP
