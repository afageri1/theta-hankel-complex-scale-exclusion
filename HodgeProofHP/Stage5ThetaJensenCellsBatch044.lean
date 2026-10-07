import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell880_leftExp :
    (15020830119 / 5000000000 : ℝ) ≤ Real.exp (11 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 10 : ℝ) (258743162177 / 250000000000 : ℝ)
    (15020830119 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell880_rightExp :
    Real.exp (881 / 800 : ℝ) ≤ (6015847159 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (881 / 800 : ℝ) (517506539059 / 500000000000 : ℝ)
    (6015847159 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell880_denomUpper :
    Real.exp (18349343323784287 / 2000000000000000 : ℝ) ≤ (96495992204141 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18349343323784287 / 2000000000000000 : ℝ) (333008963587
    / 250000000000 : ℝ) (96495992204141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell880_denomLower :
    (95333499106991 / 10000000000 : ℝ) ≤ Real.exp (5726594654401181 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5726594654401181 / 625000000000000 : ℝ) (332882858089 /
    250000000000 : ℝ) (95333499106991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell880_product_lower :
    (5898664966901181 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell880_leftExp
    (by norm_num : (0 : ℝ) ≤ (15020830119 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell880_product_upper :
    Real.pi * Real.exp (881 / 800 : ℝ) ≤ (18899343323784287 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell880_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell880_endpointLower :
    (310547529 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 20 : ℝ) (881 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5898664966901181 / 625000000000000 : ℝ) (Real.pi * Real.exp (11 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell880_product_lower
  have hD : Real.exp (Real.pi * Real.exp (881 / 800 : ℝ) - (11 / 40 : ℝ)) ≤
      (96495992204141 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell880_denomUpper
    linarith [hpThetaJensenCell880_product_upper]
  have hi : (1 / (96495992204141 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (881 / 800 : ℝ) - (11 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (96495992204141 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (96495992204141 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 40 : ℝ) - Real.pi * Real.exp (881 / 800 : ℝ)) := by
    rw [show (11 / 40 : ℝ) - Real.pi * Real.exp (881 / 800 : ℝ) =
      -(Real.pi * Real.exp (881 / 800 : ℝ) - (11 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 10 : ℝ)) := by
    have h := hpThetaJensenCell880_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (96495992204141 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell880_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 20 : ℝ) (881 / 1600 : ℝ) ≤ (632051677 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (881 / 800 : ℝ)) (18899343323784287 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (881 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell880_product_upper
  have hD : (95333499106991 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 10 : ℝ) - (881 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell880_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell880_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 10 : ℝ) - (881 / 3200 : ℝ)) ≤
      (1 / (95333499106991 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (95333499106991 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((881 / 3200 : ℝ) - Real.pi * Real.exp (11 / 10 : ℝ)) ≤
      (2 / (95333499106991 / 10000000000 : ℝ) : ℝ) := by
    rw [show (881 / 3200 : ℝ) - Real.pi * Real.exp (11 / 10 : ℝ) =
      -(Real.pi * Real.exp (11 / 10 : ℝ) - (881 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18899343323784287 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (18899343323784287 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell880_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 20 : ℝ) (881 / 1600 : ℝ)) :
    (310547529 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (632051677 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell880_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell880_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell881_leftExp :
    (30079235793 / 10000000000 : ℝ) ≤ Real.exp (881 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (881 / 800 : ℝ) (1035013078117 / 1000000000000 : ℝ)
    (30079235793 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell881_rightExp :
    Real.exp (441 / 400 : ℝ) ≤ (30116858349 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (441 / 400 : ℝ) (517526754553 / 500000000000 : ℝ)
    (30116858349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell881_denomUpper :
    Real.exp (91861786371209957 / 10000000000000000 : ℝ) ≤ (97612782311187 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (91861786371209957 / 10000000000000000 : ℝ) (83282183201
    / 62500000000 : ℝ) (97612782311187 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell881_denomLower :
    (48217705459259 / 5000000000 : ℝ) ≤ Real.exp (11467554566675307 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11467554566675307 / 1250000000000000 : ℝ) (333002428261
    / 250000000000 : ℝ) (48217705459259 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell881_product_lower :
    (11812085816675307 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (881 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell881_leftExp
    (by norm_num : (0 : ℝ) ≤ (30079235793 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell881_product_upper :
    Real.pi * Real.exp (441 / 400 : ℝ) ≤ (94614911371209957 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell881_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell881_endpointLower :
    (615671291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (881 / 1600 : ℝ) (441 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11812085816675307 / 1250000000000000 : ℝ) (Real.pi * Real.exp (881 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell881_product_lower
  have hD : Real.exp (Real.pi * Real.exp (441 / 400 : ℝ) - (881 / 3200 : ℝ)) ≤
      (97612782311187 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell881_denomUpper
    linarith [hpThetaJensenCell881_product_upper]
  have hi : (1 / (97612782311187 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (441 / 400 : ℝ) - (881 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (97612782311187 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (97612782311187 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((881 / 3200 : ℝ) - Real.pi * Real.exp (441 / 400 : ℝ)) := by
    rw [show (881 / 3200 : ℝ) - Real.pi * Real.exp (441 / 400 : ℝ) =
      -(Real.pi * Real.exp (441 / 400 : ℝ) - (881 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (881 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (881 / 800 : ℝ)) := by
    have h := hpThetaJensenCell881_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (97612782311187 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell881_endpointUpper :
    hpThetaJensenKernelEndpointUpper (881 / 1600 : ℝ) (441 / 800 : ℝ) ≤ (626541263 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (441 / 400 : ℝ)) (94614911371209957 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (441 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell881_product_upper
  have hD : (48217705459259 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (881 / 800 : ℝ) - (441 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell881_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell881_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (881 / 800 : ℝ) - (441 / 1600 : ℝ)) ≤
      (1 / (48217705459259 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (48217705459259 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((441 / 1600 : ℝ) - Real.pi * Real.exp (881 / 800 : ℝ)) ≤
      (2 / (48217705459259 / 5000000000 : ℝ) : ℝ) := by
    rw [show (441 / 1600 : ℝ) - Real.pi * Real.exp (881 / 800 : ℝ) =
      -(Real.pi * Real.exp (881 / 800 : ℝ) - (441 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (94614911371209957 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (94614911371209957 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell881_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (881 / 1600 : ℝ) (441 / 800 : ℝ)) :
    (615671291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (626541263 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell881_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell881_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell882_leftExp :
    (30116858347 / 10000000000 : ℝ) ≤ Real.exp (441 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (441 / 400 : ℝ) (207010701821 / 200000000000 : ℝ)
    (30116858347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell882_rightExp :
    Real.exp (883 / 800 : ℝ) ≤ (30154527961 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (883 / 800 : ℝ) (517546970837 / 500000000000 : ℝ)
    (30154527961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell882_denomUpper :
    Real.exp (91977003960581873 / 10000000000000000 : ℝ) ≤ (3949758292291 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91977003960581873 / 10000000000000000 : ℝ)
    (1332994796219 / 1000000000000 : ℝ) (3949758292291 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell882_denomLower :
    (9755149952399 / 1000000000 : ℝ) ≤ Real.exp (11481938281008553 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11481938281008553 / 1250000000000000 : ℝ) (1332488780353
    / 1000000000000 : ℝ) (9755149952399 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell882_product_lower :
    (11826860156008553 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (441 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell882_leftExp
    (by norm_num : (0 : ℝ) ≤ (30116858347 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell882_product_upper :
    Real.pi * Real.exp (883 / 800 : ℝ) ≤ (94733253960581873 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell882_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell882_endpointLower :
    (610285651 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (441 / 800 : ℝ) (883 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11826860156008553 / 1250000000000000 : ℝ) (Real.pi * Real.exp (441 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell882_product_lower
  have hD : Real.exp (Real.pi * Real.exp (883 / 800 : ℝ) - (441 / 1600 : ℝ)) ≤
      (3949758292291 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell882_denomUpper
    linarith [hpThetaJensenCell882_product_upper]
  have hi : (1 / (3949758292291 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (883 / 800 : ℝ) - (441 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3949758292291 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3949758292291 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((441 / 1600 : ℝ) - Real.pi * Real.exp (883 / 800 : ℝ)) := by
    rw [show (441 / 1600 : ℝ) - Real.pi * Real.exp (883 / 800 : ℝ) =
      -(Real.pi * Real.exp (883 / 800 : ℝ) - (441 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (441 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (441 / 400 : ℝ)) := by
    have h := hpThetaJensenCell882_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3949758292291 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell882_endpointUpper :
    hpThetaJensenKernelEndpointUpper (441 / 800 : ℝ) (883 / 1600 : ℝ) ≤ (621069503 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (883 / 800 : ℝ)) (94733253960581873 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (883 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell882_product_upper
  have hD : (9755149952399 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (441 / 400 : ℝ) - (883 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell882_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell882_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (441 / 400 : ℝ) - (883 / 3200 : ℝ)) ≤
      (1 / (9755149952399 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9755149952399 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((883 / 3200 : ℝ) - Real.pi * Real.exp (441 / 400 : ℝ)) ≤
      (2 / (9755149952399 / 1000000000 : ℝ) : ℝ) := by
    rw [show (883 / 3200 : ℝ) - Real.pi * Real.exp (441 / 400 : ℝ) =
      -(Real.pi * Real.exp (441 / 400 : ℝ) - (883 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (94733253960581873 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (94733253960581873 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell882_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (441 / 800 : ℝ) (883 / 1600 : ℝ)) :
    (610285651 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (621069503 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell882_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell882_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell883_leftExp :
    (30154527959 / 10000000000 : ℝ) ≤ Real.exp (883 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (883 / 800 : ℝ) (1035093941673 / 1000000000000 : ℝ)
    (30154527959 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell883_rightExp :
    Real.exp (221 / 200 : ℝ) ≤ (30192244689 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (221 / 200 : ℝ) (51756718791 / 50000000000 : ℝ)
    (30192244689 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell883_denomUpper :
    Real.exp (92092369569249577 / 10000000000000000 : ℝ) ≤ (99889719348779 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (92092369569249577 / 10000000000000000 : ℝ)
    (1333475450843 / 1000000000000 : ℝ) (99889719348779 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell883_denomLower :
    (98681963980351 / 10000000000 : ℝ) ≤ Real.exp (11496340474971341 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11496340474971341 / 1250000000000000 : ℝ) (666484317891
    / 500000000000 : ℝ) (98681963980351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell883_product_lower :
    (11841652974971341 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (883 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell883_leftExp
    (by norm_num : (0 : ℝ) ≤ (30154527959 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell883_product_upper :
    Real.pi * Real.exp (221 / 200 : ℝ) ≤ (94851744569249577 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell883_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell883_endpointLower :
    (151234489 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (883 / 1600 : ℝ) (221 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11841652974971341 / 1250000000000000 : ℝ) (Real.pi * Real.exp (883 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell883_product_lower
  have hD : Real.exp (Real.pi * Real.exp (221 / 200 : ℝ) - (883 / 3200 : ℝ)) ≤
      (99889719348779 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell883_denomUpper
    linarith [hpThetaJensenCell883_product_upper]
  have hi : (1 / (99889719348779 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (221 / 200 : ℝ) - (883 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (99889719348779 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (99889719348779 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((883 / 3200 : ℝ) - Real.pi * Real.exp (221 / 200 : ℝ)) := by
    rw [show (883 / 3200 : ℝ) - Real.pi * Real.exp (221 / 200 : ℝ) =
      -(Real.pi * Real.exp (221 / 200 : ℝ) - (883 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (883 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (883 / 800 : ℝ)) := by
    have h := hpThetaJensenCell883_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (99889719348779 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell883_endpointUpper :
    hpThetaJensenKernelEndpointUpper (883 / 1600 : ℝ) (221 / 400 : ℝ) ≤ (307818107 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (221 / 200 : ℝ)) (94851744569249577 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (221 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell883_product_upper
  have hD : (98681963980351 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (883 / 800 : ℝ) - (221 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell883_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell883_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (883 / 800 : ℝ) - (221 / 800 : ℝ)) ≤
      (1 / (98681963980351 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (98681963980351 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((221 / 800 : ℝ) - Real.pi * Real.exp (883 / 800 : ℝ)) ≤
      (2 / (98681963980351 / 10000000000 : ℝ) : ℝ) := by
    rw [show (221 / 800 : ℝ) - Real.pi * Real.exp (883 / 800 : ℝ) =
      -(Real.pi * Real.exp (883 / 800 : ℝ) - (221 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (94851744569249577 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (94851744569249577 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell883_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (883 / 1600 : ℝ) (221 / 400 : ℝ)) :
    (151234489 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (307818107 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell883_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell883_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell884_leftExp :
    (30192244687 / 10000000000 : ℝ) ≤ Real.exp (221 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (221 / 200 : ℝ) (1035134375819 / 1000000000000 : ℝ)
    (30192244687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell884_rightExp :
    Real.exp (177 / 160 : ℝ) ≤ (30230008593 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (177 / 160 : ℝ) (1035174811547 / 1000000000000 : ℝ)
    (30230008593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell884_denomUpper :
    Real.exp (92207883385708649 / 10000000000000000 : ℝ) ≤ (25262568429879 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (92207883385708649 / 10000000000000000 : ℝ) (266791379321
    / 200000000000 : ℝ) (25262568429879 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell884_denomLower :
    (99827006314617 / 10000000000 : ℝ) ≤ Real.exp (11510761171340213 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11510761171340213 / 1250000000000000 : ℝ) (83340580051 /
    62500000000 : ℝ) (99827006314617 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell884_product_lower :
    (11856464296340213 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (221 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell884_leftExp
    (by norm_num : (0 : ℝ) ≤ (30192244687 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell884_product_upper :
    Real.pi * Real.exp (177 / 160 : ℝ) ≤ (94970383385708649 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell884_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell884_endpointLower :
    (74953503 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (221 / 400 : ℝ) (177 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11856464296340213 / 1250000000000000 : ℝ) (Real.pi * Real.exp (221 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell884_product_lower
  have hD : Real.exp (Real.pi * Real.exp (177 / 160 : ℝ) - (221 / 800 : ℝ)) ≤
      (25262568429879 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell884_denomUpper
    linarith [hpThetaJensenCell884_product_upper]
  have hi : (1 / (25262568429879 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (177 / 160 : ℝ) - (221 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (25262568429879 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (25262568429879 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((221 / 800 : ℝ) - Real.pi * Real.exp (177 / 160 : ℝ)) := by
    rw [show (221 / 800 : ℝ) - Real.pi * Real.exp (177 / 160 : ℝ) =
      -(Real.pi * Real.exp (177 / 160 : ℝ) - (221 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (221 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (221 / 200 : ℝ)) := by
    have h := hpThetaJensenCell884_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (25262568429879 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell884_endpointUpper :
    hpThetaJensenKernelEndpointUpper (221 / 400 : ℝ) (177 / 320 : ℝ) ≤ (61024121 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (177 / 160 : ℝ)) (94970383385708649 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (177 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell884_product_upper
  have hD : (99827006314617 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (221 / 200 : ℝ) - (177 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell884_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell884_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (221 / 200 : ℝ) - (177 / 640 : ℝ)) ≤
      (1 / (99827006314617 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (99827006314617 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((177 / 640 : ℝ) - Real.pi * Real.exp (221 / 200 : ℝ)) ≤
      (2 / (99827006314617 / 10000000000 : ℝ) : ℝ) := by
    rw [show (177 / 640 : ℝ) - Real.pi * Real.exp (221 / 200 : ℝ) =
      -(Real.pi * Real.exp (221 / 200 : ℝ) - (177 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (94970383385708649 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (94970383385708649 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell884_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (221 / 400 : ℝ) (177 / 320 : ℝ)) :
    (74953503 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (61024121 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell884_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell884_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell885_leftExp :
    (30230008591 / 10000000000 : ℝ) ≤ Real.exp (177 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (177 / 160 : ℝ) (517587405773 / 500000000000 : ℝ)
    (30230008591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell885_rightExp :
    Real.exp (443 / 400 : ℝ) ≤ (30267819731 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (443 / 400 : ℝ) (1035215248853 / 1000000000000 : ℝ)
    (30267819731 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell885_denomUpper :
    Real.exp (92323545592171483 / 10000000000000000 : ℝ) ≤ (4089033149573 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (92323545592171483 / 10000000000000000 : ℝ) (667219567497
    / 500000000000 : ℝ) (4089033149573 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell885_denomLower :
    (50493415840799 / 5000000000 : ℝ) ≤ Real.exp (11525200393677109 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11525200393677109 / 1250000000000000 : ℝ) (333482679243
    / 250000000000 : ℝ) (50493415840799 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell885_product_lower :
    (11871294143677109 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (177 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell885_leftExp
    (by norm_num : (0 : ℝ) ≤ (30230008591 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell885_product_upper :
    Real.pi * Real.exp (443 / 400 : ℝ) ≤ (95089170592171483 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell885_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell885_endpointLower :
    (297177837 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (177 / 320 : ℝ) (443 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11871294143677109 / 1250000000000000 : ℝ) (Real.pi * Real.exp (177 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell885_product_lower
  have hD : Real.exp (Real.pi * Real.exp (443 / 400 : ℝ) - (177 / 640 : ℝ)) ≤
      (4089033149573 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell885_denomUpper
    linarith [hpThetaJensenCell885_product_upper]
  have hi : (1 / (4089033149573 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (443 / 400 : ℝ) - (177 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4089033149573 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4089033149573 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((177 / 640 : ℝ) - Real.pi * Real.exp (443 / 400 : ℝ)) := by
    rw [show (177 / 640 : ℝ) - Real.pi * Real.exp (443 / 400 : ℝ) =
      -(Real.pi * Real.exp (443 / 400 : ℝ) - (177 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (177 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (177 / 160 : ℝ)) := by
    have h := hpThetaJensenCell885_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4089033149573 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell885_endpointUpper :
    hpThetaJensenKernelEndpointUpper (177 / 320 : ℝ) (443 / 800 : ℝ) ≤ (604884309 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (443 / 400 : ℝ)) (95089170592171483 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (443 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell885_product_upper
  have hD : (50493415840799 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (177 / 160 : ℝ) - (443 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell885_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell885_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (177 / 160 : ℝ) - (443 / 1600 : ℝ)) ≤
      (1 / (50493415840799 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (50493415840799 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((443 / 1600 : ℝ) - Real.pi * Real.exp (177 / 160 : ℝ)) ≤
      (2 / (50493415840799 / 5000000000 : ℝ) : ℝ) := by
    rw [show (443 / 1600 : ℝ) - Real.pi * Real.exp (177 / 160 : ℝ) =
      -(Real.pi * Real.exp (177 / 160 : ℝ) - (443 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95089170592171483 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (95089170592171483 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell885_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (177 / 320 : ℝ) (443 / 800 : ℝ)) :
    (297177837 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (604884309 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell885_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell885_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell886_leftExp :
    (30267819729 / 10000000000 : ℝ) ≤ Real.exp (443 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (443 / 400 : ℝ) (258803812213 / 250000000000 : ℝ)
    (30267819729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell886_rightExp :
    Real.exp (887 / 800 : ℝ) ≤ (30305678161 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (887 / 800 : ℝ) (517627843869 / 500000000000 : ℝ)
    (30305678161 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell886_denomUpper :
    Real.exp (92439356370850473 / 10000000000000000 : ℝ) ≤ (103416595896879 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (92439356370850473 / 10000000000000000 : ℝ) (667461083753
    / 500000000000 : ℝ) (103416595896879 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell886_denomLower :
    (102161648270221 / 10000000000 : ℝ) ≤ Real.exp (11539658164758571 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11539658164758571 / 1250000000000000 : ℝ) (1334412945739
    / 1000000000000 : ℝ) (102161648270221 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell886_product_lower :
    (11886142539758571 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (443 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell886_leftExp
    (by norm_num : (0 : ℝ) ≤ (30267819729 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell886_product_upper :
    Real.pi * Real.exp (887 / 800 : ℝ) ≤ (95208106370850473 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell886_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell886_endpointLower :
    (23564829 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (443 / 800 : ℝ) (887 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11886142539758571 / 1250000000000000 : ℝ) (Real.pi * Real.exp (443 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell886_product_lower
  have hD : Real.exp (Real.pi * Real.exp (887 / 800 : ℝ) - (443 / 1600 : ℝ)) ≤
      (103416595896879 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell886_denomUpper
    linarith [hpThetaJensenCell886_product_upper]
  have hi : (1 / (103416595896879 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (887 / 800 : ℝ) - (443 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (103416595896879 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (103416595896879 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((443 / 1600 : ℝ) - Real.pi * Real.exp (887 / 800 : ℝ)) := by
    rw [show (443 / 1600 : ℝ) - Real.pi * Real.exp (887 / 800 : ℝ) =
      -(Real.pi * Real.exp (887 / 800 : ℝ) - (443 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (443 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (443 / 400 : ℝ)) := by
    have h := hpThetaJensenCell886_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (103416595896879 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell886_endpointUpper :
    hpThetaJensenKernelEndpointUpper (443 / 800 : ℝ) (887 / 1600 : ℝ) ≤ (37472833 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (887 / 800 : ℝ)) (95208106370850473 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (887 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell886_product_upper
  have hD : (102161648270221 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (443 / 400 : ℝ) - (887 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell886_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell886_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (443 / 400 : ℝ) - (887 / 3200 : ℝ)) ≤
      (1 / (102161648270221 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (102161648270221 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((887 / 3200 : ℝ) - Real.pi * Real.exp (443 / 400 : ℝ)) ≤
      (2 / (102161648270221 / 10000000000 : ℝ) : ℝ) := by
    rw [show (887 / 3200 : ℝ) - Real.pi * Real.exp (443 / 400 : ℝ) =
      -(Real.pi * Real.exp (443 / 400 : ℝ) - (887 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95208106370850473 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (95208106370850473 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell886_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (443 / 800 : ℝ) (887 / 1600 : ℝ)) :
    (23564829 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (37472833 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell886_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell886_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell887_leftExp :
    (30305678159 / 10000000000 : ℝ) ≤ Real.exp (887 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (887 / 800 : ℝ) (1035255687737 / 1000000000000 : ℝ)
    (30305678159 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell887_rightExp :
    Real.exp (111 / 100 : ℝ) ≤ (6068716789 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (111 / 100 : ℝ) (1035296128203 / 1000000000000 : ℝ)
    (6068716789 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell887_denomUpper :
    Real.exp (18511063183304877 / 2000000000000000 : ℝ) ≤ (20924558003329 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18511063183304877 / 2000000000000000 : ℝ) (133540599569
    / 100000000000 : ℝ) (20924558003329 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell887_denomLower :
    (10335166743873 / 1000000000 : ℝ) ≤ Real.exp (11554134507361141 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11554134507361141 / 1250000000000000 : ℝ) (667447984307
    / 500000000000 : ℝ) (10335166743873 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell887_product_lower :
    (11901009507361141 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (887 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell887_leftExp
    (by norm_num : (0 : ℝ) ≤ (30305678159 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell887_product_upper :
    Real.pi * Real.exp (111 / 100 : ℝ) ≤ (19065438183304877 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell887_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell887_endpointLower :
    (291961497 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (887 / 1600 : ℝ) (111 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11901009507361141 / 1250000000000000 : ℝ) (Real.pi * Real.exp (887 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell887_product_lower
  have hD : Real.exp (Real.pi * Real.exp (111 / 100 : ℝ) - (887 / 3200 : ℝ)) ≤
      (20924558003329 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell887_denomUpper
    linarith [hpThetaJensenCell887_product_upper]
  have hi : (1 / (20924558003329 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (111 / 100 : ℝ) - (887 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (20924558003329 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (20924558003329 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((887 / 3200 : ℝ) - Real.pi * Real.exp (111 / 100 : ℝ)) := by
    rw [show (887 / 3200 : ℝ) - Real.pi * Real.exp (111 / 100 : ℝ) =
      -(Real.pi * Real.exp (111 / 100 : ℝ) - (887 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (887 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (887 / 800 : ℝ)) := by
    have h := hpThetaJensenCell887_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (20924558003329 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell887_endpointUpper :
    hpThetaJensenKernelEndpointUpper (887 / 1600 : ℝ) (111 / 200 : ℝ) ≤ (594284083 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (111 / 100 : ℝ)) (19065438183304877 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (111 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell887_product_upper
  have hD : (10335166743873 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (887 / 800 : ℝ) - (111 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell887_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell887_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (887 / 800 : ℝ) - (111 / 400 : ℝ)) ≤
      (1 / (10335166743873 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10335166743873 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((111 / 400 : ℝ) - Real.pi * Real.exp (887 / 800 : ℝ)) ≤
      (2 / (10335166743873 / 1000000000 : ℝ) : ℝ) := by
    rw [show (111 / 400 : ℝ) - Real.pi * Real.exp (887 / 800 : ℝ) =
      -(Real.pi * Real.exp (887 / 800 : ℝ) - (111 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19065438183304877 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (19065438183304877 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell887_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (887 / 1600 : ℝ) (111 / 200 : ℝ)) :
    (291961497 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (594284083 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell887_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell887_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell888_leftExp :
    (30343583943 / 10000000000 : ℝ) ≤ Real.exp (111 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (111 / 100 : ℝ) (517648064101 / 500000000000 : ℝ)
    (30343583943 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell888_rightExp :
    Real.exp (889 / 800 : ℝ) ≤ (30381537141 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (889 / 800 : ℝ) (129417071281 / 125000000000 : ℝ)
    (30381537141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell888_denomUpper :
    Real.exp (92671424411405613 / 10000000000000000 : ℝ) ≤ (105844629051729 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (92671424411405613 / 10000000000000000 : ℝ)
    (1335890621043 / 1000000000000 : ℝ) (105844629051729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell888_denomLower :
    (52278551934583 / 5000000000 : ℝ) ≤ Real.exp (11568629445832157 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11568629445832157 / 1250000000000000 : ℝ) (1335379787143
    / 1000000000000 : ℝ) (52278551934583 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell888_product_lower :
    (11915895070832157 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (111 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell888_leftExp
    (by norm_num : (0 : ℝ) ≤ (30343583943 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell888_product_upper :
    Real.pi * Real.exp (889 / 800 : ℝ) ≤ (95446424411405613 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell888_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell888_endpointLower :
    (578762301 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (111 / 200 : ℝ) (889 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11915895070832157 / 1250000000000000 : ℝ) (Real.pi * Real.exp (111 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell888_product_lower
  have hD : Real.exp (Real.pi * Real.exp (889 / 800 : ℝ) - (111 / 400 : ℝ)) ≤
      (105844629051729 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell888_denomUpper
    linarith [hpThetaJensenCell888_product_upper]
  have hi : (1 / (105844629051729 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (889 / 800 : ℝ) - (111 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (105844629051729 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (105844629051729 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((111 / 400 : ℝ) - Real.pi * Real.exp (889 / 800 : ℝ)) := by
    rw [show (111 / 400 : ℝ) - Real.pi * Real.exp (889 / 800 : ℝ) =
      -(Real.pi * Real.exp (889 / 800 : ℝ) - (111 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (111 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (111 / 100 : ℝ)) := by
    have h := hpThetaJensenCell888_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (105844629051729 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell888_endpointUpper :
    hpThetaJensenKernelEndpointUpper (111 / 200 : ℝ) (889 / 1600 : ℝ) ≤ (58904039 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (889 / 800 : ℝ)) (95446424411405613 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (889 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell888_product_upper
  have hD : (52278551934583 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (111 / 100 : ℝ) - (889 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell888_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell888_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (111 / 100 : ℝ) - (889 / 3200 : ℝ)) ≤
      (1 / (52278551934583 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (52278551934583 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((889 / 3200 : ℝ) - Real.pi * Real.exp (111 / 100 : ℝ)) ≤
      (2 / (52278551934583 / 5000000000 : ℝ) : ℝ) := by
    rw [show (889 / 3200 : ℝ) - Real.pi * Real.exp (111 / 100 : ℝ) =
      -(Real.pi * Real.exp (111 / 100 : ℝ) - (889 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95446424411405613 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (95446424411405613 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell888_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (111 / 200 : ℝ) (889 / 1600 : ℝ)) :
    (578762301 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (58904039 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell888_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell888_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell889_leftExp :
    (30381537139 / 10000000000 : ℝ) ≤ Real.exp (889 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (889 / 800 : ℝ) (1035336570247 / 1000000000000 : ℝ)
    (30381537139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell889_rightExp :
    Real.exp (89 / 80 : ℝ) ≤ (1901221113 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89 / 80 : ℝ) (1035377013873 / 1000000000000 : ℝ)
    (1901221113 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell889_denomUpper :
    Real.exp (5799230127553009 / 625000000000000 : ℝ) ≤ (3346322947221 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (5799230127553009 / 625000000000000 : ℝ) (1336376045081 /
    1000000000000 : ℝ) (3346322947221 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell889_denomLower :
    (105778175387639 / 10000000000 : ℝ) ≤ Real.exp (11583143002948161 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11583143002948161 / 1250000000000000 : ℝ) (1335864402827
    / 1000000000000 : ℝ) (105778175387639 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell889_product_lower :
    (11930799252948161 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (889 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell889_leftExp
    (by norm_num : (0 : ℝ) ≤ (30381537139 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell889_product_upper :
    Real.pi * Real.exp (89 / 80 : ℝ) ≤ (5972862940053009 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell889_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell889_endpointLower :
    (573638463 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (889 / 1600 : ℝ) (89 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11930799252948161 / 1250000000000000 : ℝ) (Real.pi * Real.exp (889 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell889_product_lower
  have hD : Real.exp (Real.pi * Real.exp (89 / 80 : ℝ) - (889 / 3200 : ℝ)) ≤
      (3346322947221 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell889_denomUpper
    linarith [hpThetaJensenCell889_product_upper]
  have hi : (1 / (3346322947221 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (89 / 80 : ℝ) - (889 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3346322947221 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3346322947221 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((889 / 3200 : ℝ) - Real.pi * Real.exp (89 / 80 : ℝ)) := by
    rw [show (889 / 3200 : ℝ) - Real.pi * Real.exp (89 / 80 : ℝ) =
      -(Real.pi * Real.exp (89 / 80 : ℝ) - (889 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (889 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (889 / 800 : ℝ)) := by
    have h := hpThetaJensenCell889_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3346322947221 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell889_endpointUpper :
    hpThetaJensenKernelEndpointUpper (889 / 1600 : ℝ) (89 / 160 : ℝ) ≤ (583834067 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (89 / 80 : ℝ)) (5972862940053009 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (89 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell889_product_upper
  have hD : (105778175387639 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (889 / 800 : ℝ) - (89 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell889_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell889_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (889 / 800 : ℝ) - (89 / 320 : ℝ)) ≤
      (1 / (105778175387639 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (105778175387639 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((89 / 320 : ℝ) - Real.pi * Real.exp (889 / 800 : ℝ)) ≤
      (2 / (105778175387639 / 10000000000 : ℝ) : ℝ) := by
    rw [show (89 / 320 : ℝ) - Real.pi * Real.exp (889 / 800 : ℝ) =
      -(Real.pi * Real.exp (889 / 800 : ℝ) - (89 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5972862940053009 / 625000000000000 : ℝ) ^ 2 - 6 *
      (5972862940053009 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell889_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (889 / 1600 : ℝ) (89 / 160 : ℝ)) :
    (573638463 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (583834067 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell889_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell889_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell890_leftExp :
    (15209768903 / 5000000000 : ℝ) ≤ Real.exp (89 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (89 / 80 : ℝ) (64711063367 / 62500000000 : ℝ)
    (15209768903 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell890_rightExp :
    Real.exp (891 / 800 : ℝ) ≤ (6091517201 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (891 / 800 : ℝ) (1035417459077 / 1000000000000 : ℝ)
    (6091517201 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell890_denomUpper :
    Real.exp (18580817798041193 / 2000000000000000 : ℝ) ≤ (27084032617213 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18580817798041193 / 2000000000000000 : ℝ) (1336862269321
    / 1000000000000 : ℝ) (27084032617213 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell890_denomLower :
    (53507551578251 / 5000000000 : ℝ) ≤ Real.exp (5798837600939197 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5798837600939197 / 625000000000000 : ℝ) (1336349817179 /
    1000000000000 : ℝ) (53507551578251 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell890_product_lower :
    (5972861038439197 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (89 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell890_leftExp
    (by norm_num : (0 : ℝ) ≤ (15209768903 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell890_product_upper :
    Real.pi * Real.exp (891 / 800 : ℝ) ≤ (19137067798041193 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell890_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell890_endpointLower :
    (284275651 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 160 : ℝ) (891 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5972861038439197 / 625000000000000 : ℝ) (Real.pi * Real.exp (89 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell890_product_lower
  have hD : Real.exp (Real.pi * Real.exp (891 / 800 : ℝ) - (89 / 320 : ℝ)) ≤
      (27084032617213 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell890_denomUpper
    linarith [hpThetaJensenCell890_product_upper]
  have hi : (1 / (27084032617213 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (891 / 800 : ℝ) - (89 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27084032617213 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27084032617213 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((89 / 320 : ℝ) - Real.pi * Real.exp (891 / 800 : ℝ)) := by
    rw [show (89 / 320 : ℝ) - Real.pi * Real.exp (891 / 800 : ℝ) =
      -(Real.pi * Real.exp (891 / 800 : ℝ) - (89 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (89 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (89 / 80 : ℝ)) := by
    have h := hpThetaJensenCell890_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27084032617213 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell890_endpointUpper :
    hpThetaJensenKernelEndpointUpper (89 / 160 : ℝ) (891 / 1600 : ℝ) ≤ (144666233 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (891 / 800 : ℝ)) (19137067798041193 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (891 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell890_product_upper
  have hD : (53507551578251 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (89 / 80 : ℝ) - (891 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell890_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell890_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (89 / 80 : ℝ) - (891 / 3200 : ℝ)) ≤
      (1 / (53507551578251 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (53507551578251 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((891 / 3200 : ℝ) - Real.pi * Real.exp (89 / 80 : ℝ)) ≤
      (2 / (53507551578251 / 5000000000 : ℝ) : ℝ) := by
    rw [show (891 / 3200 : ℝ) - Real.pi * Real.exp (89 / 80 : ℝ) =
      -(Real.pi * Real.exp (89 / 80 : ℝ) - (891 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19137067798041193 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (19137067798041193 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell890_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (89 / 160 : ℝ) (891 / 1600 : ℝ)) :
    (284275651 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (144666233 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell890_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell890_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell891_leftExp :
    (30457586003 / 10000000000 : ℝ) ≤ Real.exp (891 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (891 / 800 : ℝ) (258854364769 / 250000000000 : ℝ)
    (30457586003 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell891_rightExp :
    Real.exp (223 / 200 : ℝ) ≤ (30495681793 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (223 / 200 : ℝ) (517728952931 / 500000000000 : ℝ)
    (30495681793 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell891_denomUpper :
    Real.exp (93020645451116249 / 10000000000000000 : ℝ) ≤ (2192124913847 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93020645451116249 / 10000000000000000 : ℝ)
    (1337349295309 / 1000000000000 : ℝ) (2192124913847 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell891_denomLower :
    (108268111713847 / 10000000000 : ℝ) ≤ Real.exp (11612226065792097 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11612226065792097 / 1250000000000000 : ℝ) (668418015859
    / 500000000000 : ℝ) (108268111713847 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell891_product_lower :
    (11960663565792097 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (891 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell891_leftExp
    (by norm_num : (0 : ℝ) ≤ (30457586003 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell891_product_upper :
    Real.pi * Real.exp (223 / 200 : ℝ) ≤ (95805020451116249 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell891_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell891_endpointLower :
    (112700127 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (891 / 1600 : ℝ) (223 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11960663565792097 / 1250000000000000 : ℝ) (Real.pi * Real.exp (891 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell891_product_lower
  have hD : Real.exp (Real.pi * Real.exp (223 / 200 : ℝ) - (891 / 3200 : ℝ)) ≤
      (2192124913847 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell891_denomUpper
    linarith [hpThetaJensenCell891_product_upper]
  have hi : (1 / (2192124913847 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (223 / 200 : ℝ) - (891 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2192124913847 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2192124913847 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((891 / 3200 : ℝ) - Real.pi * Real.exp (223 / 200 : ℝ)) := by
    rw [show (891 / 3200 : ℝ) - Real.pi * Real.exp (223 / 200 : ℝ) =
      -(Real.pi * Real.exp (223 / 200 : ℝ) - (891 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (891 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (891 / 800 : ℝ)) := by
    have h := hpThetaJensenCell891_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2192124913847 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell891_endpointUpper :
    hpThetaJensenKernelEndpointUpper (891 / 1600 : ℝ) (223 / 400 : ℝ) ≤ (573532801 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (223 / 200 : ℝ)) (95805020451116249 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (223 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell891_product_upper
  have hD : (108268111713847 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (891 / 800 : ℝ) - (223 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell891_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell891_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (891 / 800 : ℝ) - (223 / 800 : ℝ)) ≤
      (1 / (108268111713847 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (108268111713847 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((223 / 800 : ℝ) - Real.pi * Real.exp (891 / 800 : ℝ)) ≤
      (2 / (108268111713847 / 10000000000 : ℝ) : ℝ) := by
    rw [show (223 / 800 : ℝ) - Real.pi * Real.exp (891 / 800 : ℝ) =
      -(Real.pi * Real.exp (891 / 800 : ℝ) - (223 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95805020451116249 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (95805020451116249 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell891_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (891 / 1600 : ℝ) (223 / 400 : ℝ)) :
    (112700127 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (573532801 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell891_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell891_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell892_leftExp :
    (30495681791 / 10000000000 : ℝ) ≤ Real.exp (223 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (223 / 200 : ℝ) (1035457905861 / 1000000000000 : ℝ)
    (30495681791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell892_rightExp :
    Real.exp (893 / 800 : ℝ) ≤ (30533825229 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (893 / 800 : ℝ) (517749177113 / 500000000000 : ℝ)
    (30533825229 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell892_denomUpper :
    Real.exp (93137351602649797 / 10000000000000000 : ℝ) ≤ (27723227872989 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93137351602649797 / 10000000000000000 : ℝ)
    (1337837124541 / 1000000000000 : ℝ) (27723227872989 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell892_denomLower :
    (27384357269607 / 2500000000 : ℝ) ≤ Real.exp (11626795618643909 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11626795618643909 / 1250000000000000 : ℝ) (334330761997
    / 250000000000 : ℝ) (27384357269607 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell892_product_lower :
    (11975623743643909 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (223 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell892_leftExp
    (by norm_num : (0 : ℝ) ≤ (30495681791 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell892_product_upper :
    Real.pi * Real.exp (893 / 800 : ℝ) ≤ (95924851602649797 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell892_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell892_endpointLower :
    (558486283 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (223 / 400 : ℝ) (893 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11975623743643909 / 1250000000000000 : ℝ) (Real.pi * Real.exp (223 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell892_product_lower
  have hD : Real.exp (Real.pi * Real.exp (893 / 800 : ℝ) - (223 / 800 : ℝ)) ≤
      (27723227872989 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell892_denomUpper
    linarith [hpThetaJensenCell892_product_upper]
  have hi : (1 / (27723227872989 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (893 / 800 : ℝ) - (223 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (27723227872989 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (27723227872989 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((223 / 800 : ℝ) - Real.pi * Real.exp (893 / 800 : ℝ)) := by
    rw [show (223 / 800 : ℝ) - Real.pi * Real.exp (893 / 800 : ℝ) =
      -(Real.pi * Real.exp (893 / 800 : ℝ) - (223 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (223 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (223 / 200 : ℝ)) := by
    have h := hpThetaJensenCell892_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (27723227872989 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell892_endpointUpper :
    hpThetaJensenKernelEndpointUpper (223 / 400 : ℝ) (893 / 1600 : ℝ) ≤ (142109373 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (893 / 800 : ℝ)) (95924851602649797 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (893 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell892_product_upper
  have hD : (27384357269607 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (223 / 200 : ℝ) - (893 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell892_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell892_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (223 / 200 : ℝ) - (893 / 3200 : ℝ)) ≤
      (1 / (27384357269607 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (27384357269607 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((893 / 3200 : ℝ) - Real.pi * Real.exp (223 / 200 : ℝ)) ≤
      (2 / (27384357269607 / 2500000000 : ℝ) : ℝ) := by
    rw [show (893 / 3200 : ℝ) - Real.pi * Real.exp (223 / 200 : ℝ) =
      -(Real.pi * Real.exp (223 / 200 : ℝ) - (893 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95924851602649797 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (95924851602649797 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell892_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (223 / 400 : ℝ) (893 / 1600 : ℝ)) :
    (558486283 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (142109373 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell892_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell892_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell893_leftExp :
    (7633456307 / 2500000000 : ℝ) ≤ Real.exp (893 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (893 / 800 : ℝ) (41419934169 / 40000000000 : ℝ)
    (7633456307 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell893_rightExp :
    Real.exp (447 / 400 : ℝ) ≤ (3821502047 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (447 / 400 : ℝ) (1035538804171 / 1000000000000 : ℝ)
    (3821502047 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell893_denomUpper :
    Real.exp (11656775955340871 / 1250000000000000 : ℝ) ≤ (28049090779657 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11656775955340871 / 1250000000000000 : ℝ) (1338325758593
    / 1000000000000 : ℝ) (28049090779657 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell893_denomLower :
    (110823286652181 / 10000000000 : ℝ) ≤ Real.exp (2910345970802593 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2910345970802593 / 312500000000000 : ℝ) (1337810867499 /
    1000000000000 : ℝ) (110823286652181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell893_product_lower :
    (2997650658302593 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (893 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell893_leftExp
    (by norm_num : (0 : ℝ) ≤ (7633456307 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell893_product_upper :
    Real.pi * Real.exp (447 / 400 : ℝ) ≤ (12005604080340871 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell893_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell893_endpointLower :
    (17297127 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (893 / 1600 : ℝ) (447 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2997650658302593 / 312500000000000 : ℝ) (Real.pi * Real.exp (893 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell893_product_lower
  have hD : Real.exp (Real.pi * Real.exp (447 / 400 : ℝ) - (893 / 3200 : ℝ)) ≤
      (28049090779657 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell893_denomUpper
    linarith [hpThetaJensenCell893_product_upper]
  have hi : (1 / (28049090779657 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (447 / 400 : ℝ) - (893 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (28049090779657 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (28049090779657 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((893 / 3200 : ℝ) - Real.pi * Real.exp (447 / 400 : ℝ)) := by
    rw [show (893 / 3200 : ℝ) - Real.pi * Real.exp (447 / 400 : ℝ) =
      -(Real.pi * Real.exp (447 / 400 : ℝ) - (893 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (893 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (893 / 800 : ℝ)) := by
    have h := hpThetaJensenCell893_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (28049090779657 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell893_endpointUpper :
    hpThetaJensenKernelEndpointUpper (893 / 1600 : ℝ) (447 / 800 : ℝ) ≤ (70422353 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (447 / 400 : ℝ)) (12005604080340871 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (447 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell893_product_upper
  have hD : (110823286652181 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (893 / 800 : ℝ) - (447 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell893_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell893_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (893 / 800 : ℝ) - (447 / 1600 : ℝ)) ≤
      (1 / (110823286652181 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (110823286652181 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((447 / 1600 : ℝ) - Real.pi * Real.exp (893 / 800 : ℝ)) ≤
      (2 / (110823286652181 / 10000000000 : ℝ) : ℝ) := by
    rw [show (447 / 1600 : ℝ) - Real.pi * Real.exp (893 / 800 : ℝ) =
      -(Real.pi * Real.exp (893 / 800 : ℝ) - (447 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12005604080340871 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (12005604080340871 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell893_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (893 / 1600 : ℝ) (447 / 800 : ℝ)) :
    (17297127 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (70422353 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell893_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell893_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell894_leftExp :
    (15286008187 / 5000000000 : ℝ) ≤ Real.exp (447 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (447 / 400 : ℝ) (103553880417 / 100000000000 : ℝ)
    (15286008187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell894_rightExp :
    Real.exp (179 / 160 : ℝ) ≤ (3061025529 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (179 / 160 : ℝ) (207115851139 / 200000000000 : ℝ)
    (3061025529 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell894_denomUpper :
    Real.exp (9337121374727697 / 1000000000000000 : ℝ) ≤ (113516839182769 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9337121374727697 / 1000000000000000 : ℝ) (267763039791 /
    200000000000 : ℝ) (113516839182769 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell894_denomLower :
    (112125919434859 / 10000000000 : ℝ) ≤ Real.exp (5827995441526713 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5827995441526713 / 625000000000000 : ℝ) (334574872947 /
    250000000000 : ℝ) (112125919434859 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell894_product_lower :
    (6002800129026713 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (447 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell894_leftExp
    (by norm_num : (0 : ℝ) ≤ (15286008187 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell894_product_upper :
    Real.pi * Real.exp (179 / 160 : ℝ) ≤ (9616496374727697 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell894_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell894_endpointLower :
    (2742829 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (447 / 800 : ℝ) (179 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6002800129026713 / 625000000000000 : ℝ) (Real.pi * Real.exp (447 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell894_product_lower
  have hD : Real.exp (Real.pi * Real.exp (179 / 160 : ℝ) - (447 / 1600 : ℝ)) ≤
      (113516839182769 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell894_denomUpper
    linarith [hpThetaJensenCell894_product_upper]
  have hi : (1 / (113516839182769 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (179 / 160 : ℝ) - (447 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (113516839182769 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (113516839182769 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((447 / 1600 : ℝ) - Real.pi * Real.exp (179 / 160 : ℝ)) := by
    rw [show (447 / 1600 : ℝ) - Real.pi * Real.exp (179 / 160 : ℝ) =
      -(Real.pi * Real.exp (179 / 160 : ℝ) - (447 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (447 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (447 / 400 : ℝ)) := by
    have h := hpThetaJensenCell894_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (113516839182769 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell894_endpointUpper :
    hpThetaJensenKernelEndpointUpper (447 / 800 : ℝ) (179 / 320 : ℝ) ≤ (279178307 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (179 / 160 : ℝ)) (9616496374727697 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (179 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell894_product_upper
  have hD : (112125919434859 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (447 / 400 : ℝ) - (179 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell894_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell894_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (447 / 400 : ℝ) - (179 / 640 : ℝ)) ≤
      (1 / (112125919434859 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (112125919434859 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((179 / 640 : ℝ) - Real.pi * Real.exp (447 / 400 : ℝ)) ≤
      (2 / (112125919434859 / 10000000000 : ℝ) : ℝ) := by
    rw [show (179 / 640 : ℝ) - Real.pi * Real.exp (447 / 400 : ℝ) =
      -(Real.pi * Real.exp (447 / 400 : ℝ) - (179 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9616496374727697 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9616496374727697 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell894_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (447 / 800 : ℝ) (179 / 320 : ℝ)) :
    (2742829 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (279178307 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell894_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell894_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell895_leftExp :
    (3826281911 / 1250000000 : ℝ) ≤ Real.exp (179 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (179 / 160 : ℝ) (517789627847 / 500000000000 : ℝ)
    (3826281911 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell895_rightExp :
    Real.exp (28 / 25 : ℝ) ≤ (15324271017 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28 / 25 : ℝ) (323631159 / 312500000 : ℝ)
    (15324271017 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell895_denomUpper :
    Real.exp (46744185057110081 / 5000000000000000 : ℝ) ≤ (1794602846597 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46744185057110081 / 5000000000000000 : ℝ) (1339305447207
    / 1000000000000 : ℝ) (1794602846597 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell895_denomLower :
    (56722782995157 / 5000000000 : ℝ) ≤ Real.exp (1458827080167789 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1458827080167789 / 156250000000000 : ℝ) (83674307649 /
    62500000000 : ℝ) (56722782995157 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell895_product_lower :
    (1502577080167789 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (179 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell895_leftExp
    (by norm_num : (0 : ℝ) ≤ (3826281911 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell895_product_upper :
    Real.pi * Real.exp (28 / 25 : ℝ) ≤ (48142622557110081 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell895_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell895_endpointLower :
    (54365931 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (179 / 320 : ℝ) (14 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1502577080167789 / 156250000000000 : ℝ) (Real.pi * Real.exp (179 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell895_product_lower
  have hD : Real.exp (Real.pi * Real.exp (28 / 25 : ℝ) - (179 / 640 : ℝ)) ≤
      (1794602846597 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell895_denomUpper
    linarith [hpThetaJensenCell895_product_upper]
  have hi : (1 / (1794602846597 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (28 / 25 : ℝ) - (179 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1794602846597 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1794602846597 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((179 / 640 : ℝ) - Real.pi * Real.exp (28 / 25 : ℝ)) := by
    rw [show (179 / 640 : ℝ) - Real.pi * Real.exp (28 / 25 : ℝ) =
      -(Real.pi * Real.exp (28 / 25 : ℝ) - (179 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (179 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (179 / 160 : ℝ)) := by
    have h := hpThetaJensenCell895_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1794602846597 / 156250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell895_endpointUpper :
    hpThetaJensenKernelEndpointUpper (179 / 320 : ℝ) (14 / 25 : ℝ) ≤ (13834267 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (28 / 25 : ℝ)) (48142622557110081 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (14 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell895_product_upper
  have hD : (56722782995157 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (179 / 160 : ℝ) - (7 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell895_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell895_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (179 / 160 : ℝ) - (7 / 25 : ℝ)) ≤
      (1 / (56722782995157 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (56722782995157 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 25 : ℝ) - Real.pi * Real.exp (179 / 160 : ℝ)) ≤
      (2 / (56722782995157 / 5000000000 : ℝ) : ℝ) := by
    rw [show (7 / 25 : ℝ) - Real.pi * Real.exp (179 / 160 : ℝ) =
      -(Real.pi * Real.exp (179 / 160 : ℝ) - (7 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48142622557110081 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (48142622557110081 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell895_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (179 / 320 : ℝ) (14 / 25 : ℝ)) :
    (54365931 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13834267 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell895_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell895_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell896_leftExp :
    (1915533877 / 625000000 : ℝ) ≤ Real.exp (28 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (28 / 25 : ℝ) (1035619708799 / 1000000000000 : ℝ)
    (1915533877 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell896_rightExp :
    Real.exp (897 / 800 : ℝ) ≤ (6137375333 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (897 / 800 : ℝ) (207132032697 / 200000000000 : ℝ)
    (6137375333 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell896_denomUpper :
    Real.exp (18721135384525469 / 2000000000000000 : ℝ) ≤ (29052459531413 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18721135384525469 / 2000000000000000 : ℝ) (1339796504857
    / 1000000000000 : ℝ) (29052459531413 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell896_denomLower :
    (57391234314771 / 5000000000 : ℝ) ≤ Real.exp (730328823901523 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (730328823901523 / 78125000000000 : ℝ) (669639580427 /
    500000000000 : ℝ) (57391234314771 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell896_product_lower :
    (752228237964023 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (28 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell896_leftExp
    (by norm_num : (0 : ℝ) ≤ (1915533877 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell896_product_upper :
    Real.pi * Real.exp (897 / 800 : ℝ) ≤ (19281135384525469 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell896_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell896_endpointLower :
    (269394207 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (14 / 25 : ℝ) (897 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (752228237964023 / 78125000000000 : ℝ) (Real.pi * Real.exp (28 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell896_product_lower
  have hD : Real.exp (Real.pi * Real.exp (897 / 800 : ℝ) - (7 / 25 : ℝ)) ≤
      (29052459531413 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell896_denomUpper
    linarith [hpThetaJensenCell896_product_upper]
  have hi : (1 / (29052459531413 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (897 / 800 : ℝ) - (7 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29052459531413 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29052459531413 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 25 : ℝ) - Real.pi * Real.exp (897 / 800 : ℝ)) := by
    rw [show (7 / 25 : ℝ) - Real.pi * Real.exp (897 / 800 : ℝ) =
      -(Real.pi * Real.exp (897 / 800 : ℝ) - (7 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (28 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (28 / 25 : ℝ)) := by
    have h := hpThetaJensenCell896_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29052459531413 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell896_endpointUpper :
    hpThetaJensenKernelEndpointUpper (14 / 25 : ℝ) (897 / 1600 : ℝ) ≤ (548420841 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (897 / 800 : ℝ)) (19281135384525469 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (897 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell896_product_upper
  have hD : (57391234314771 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (28 / 25 : ℝ) - (897 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell896_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell896_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (28 / 25 : ℝ) - (897 / 3200 : ℝ)) ≤
      (1 / (57391234314771 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57391234314771 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((897 / 3200 : ℝ) - Real.pi * Real.exp (28 / 25 : ℝ)) ≤
      (2 / (57391234314771 / 5000000000 : ℝ) : ℝ) := by
    rw [show (897 / 3200 : ℝ) - Real.pi * Real.exp (28 / 25 : ℝ) =
      -(Real.pi * Real.exp (28 / 25 : ℝ) - (897 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19281135384525469 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (19281135384525469 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell896_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (14 / 25 : ℝ) (897 / 1600 : ℝ)) :
    (269394207 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (548420841 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell896_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell896_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell897_leftExp :
    (3835859583 / 1250000000 : ℝ) ≤ Real.exp (897 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (897 / 800 : ℝ) (258915040871 / 250000000000 : ℝ)
    (3835859583 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell897_rightExp :
    Real.exp (449 / 400 : ℝ) ≤ (6145051849 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (449 / 400 : ℝ) (4142802479 / 4000000000 : ℝ)
    (6145051849 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell897_denomUpper :
    Real.exp (18744626873455457 / 2000000000000000 : ℝ) ≤ (58791428483103 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (18744626873455457 / 2000000000000000 : ℝ) (670144186739
    / 500000000000 : ℝ) (58791428483103 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell897_denomLower :
    (29034218310683 / 2500000000 : ℝ) ≤ Real.exp (1462490566134517 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1462490566134517 / 156250000000000 : ℝ) (1339770208719 /
    1000000000000 : ℝ) (29034218310683 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell897_product_lower :
    (1506338222384517 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (897 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell897_leftExp
    (by norm_num : (0 : ℝ) ≤ (3835859583 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell897_product_upper :
    Real.pi * Real.exp (449 / 400 : ℝ) ≤ (19305251873455457 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell897_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell897_endpointLower :
    (533952933 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (897 / 1600 : ℝ) (449 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1506338222384517 / 156250000000000 : ℝ) (Real.pi * Real.exp (897 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell897_product_lower
  have hD : Real.exp (Real.pi * Real.exp (449 / 400 : ℝ) - (897 / 3200 : ℝ)) ≤
      (58791428483103 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell897_denomUpper
    linarith [hpThetaJensenCell897_product_upper]
  have hi : (1 / (58791428483103 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (449 / 400 : ℝ) - (897 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (58791428483103 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (58791428483103 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((897 / 3200 : ℝ) - Real.pi * Real.exp (449 / 400 : ℝ)) := by
    rw [show (897 / 3200 : ℝ) - Real.pi * Real.exp (449 / 400 : ℝ) =
      -(Real.pi * Real.exp (449 / 400 : ℝ) - (897 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (897 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (897 / 800 : ℝ)) := by
    have h := hpThetaJensenCell897_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (58791428483103 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell897_endpointUpper :
    hpThetaJensenKernelEndpointUpper (897 / 1600 : ℝ) (449 / 800 : ℝ) ≤ (108701383 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (449 / 400 : ℝ)) (19305251873455457 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (449 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell897_product_upper
  have hD : (29034218310683 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (897 / 800 : ℝ) - (449 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell897_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell897_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (897 / 800 : ℝ) - (449 / 1600 : ℝ)) ≤
      (1 / (29034218310683 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29034218310683 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((449 / 1600 : ℝ) - Real.pi * Real.exp (897 / 800 : ℝ)) ≤
      (2 / (29034218310683 / 2500000000 : ℝ) : ℝ) := by
    rw [show (449 / 1600 : ℝ) - Real.pi * Real.exp (897 / 800 : ℝ) =
      -(Real.pi * Real.exp (897 / 800 : ℝ) - (449 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19305251873455457 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (19305251873455457 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell897_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (897 / 1600 : ℝ) (449 / 800 : ℝ)) :
    (533952933 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (108701383 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell897_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell897_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell898_leftExp :
    (30725259243 / 10000000000 : ℝ) ≤ Real.exp (449 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (449 / 400 : ℝ) (1035700619749 / 1000000000000 : ℝ)
    (30725259243 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell898_rightExp :
    Real.exp (899 / 800 : ℝ) ≤ (15381844917 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (899 / 800 : ℝ) (258935269399 / 250000000000 : ℝ)
    (15381844917 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell898_denomUpper :
    Real.exp (46920371318332781 / 5000000000000000 : ℝ) ≤ (59486946214357 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46920371318332781 / 5000000000000000 : ℝ) (670390527311
    / 500000000000 : ℝ) (59486946214357 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell898_denomLower :
    (29377257378737 / 2500000000 : ℝ) ≤ Real.exp (11714606704466857 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11714606704466857 / 1250000000000000 : ℝ) (167532758439
    / 125000000000 : ℝ) (29377257378737 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell898_product_lower :
    (12065778579466857 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (449 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell898_leftExp
    (by norm_num : (0 : ℝ) ≤ (30725259243 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell898_product_upper :
    Real.pi * Real.exp (899 / 800 : ℝ) ≤ (48323496318332781 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell898_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell898_endpointLower :
    (33072043 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (449 / 800 : ℝ) (899 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12065778579466857 / 1250000000000000 : ℝ) (Real.pi * Real.exp (449 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell898_product_lower
  have hD : Real.exp (Real.pi * Real.exp (899 / 800 : ℝ) - (449 / 1600 : ℝ)) ≤
      (59486946214357 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell898_denomUpper
    linarith [hpThetaJensenCell898_product_upper]
  have hi : (1 / (59486946214357 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (899 / 800 : ℝ) - (449 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (59486946214357 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (59486946214357 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((449 / 1600 : ℝ) - Real.pi * Real.exp (899 / 800 : ℝ)) := by
    rw [show (449 / 1600 : ℝ) - Real.pi * Real.exp (899 / 800 : ℝ) =
      -(Real.pi * Real.exp (899 / 800 : ℝ) - (449 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (449 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (449 / 400 : ℝ)) := by
    have h := hpThetaJensenCell898_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (59486946214357 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell898_endpointUpper :
    hpThetaJensenKernelEndpointUpper (449 / 800 : ℝ) (899 / 1600 : ℝ) ≤ (269314361 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (899 / 800 : ℝ)) (48323496318332781 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (899 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell898_product_upper
  have hD : (29377257378737 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (449 / 400 : ℝ) - (899 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell898_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell898_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (449 / 400 : ℝ) - (899 / 3200 : ℝ)) ≤
      (1 / (29377257378737 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (29377257378737 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((899 / 3200 : ℝ) - Real.pi * Real.exp (449 / 400 : ℝ)) ≤
      (2 / (29377257378737 / 2500000000 : ℝ) : ℝ) := by
    rw [show (899 / 3200 : ℝ) - Real.pi * Real.exp (449 / 400 : ℝ) =
      -(Real.pi * Real.exp (449 / 400 : ℝ) - (899 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48323496318332781 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (48323496318332781 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell898_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (449 / 800 : ℝ) (899 / 1600 : ℝ)) :
    (33072043 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (269314361 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell898_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell898_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell899_leftExp :
    (3845461229 / 1250000000 : ℝ) ≤ Real.exp (899 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (899 / 800 : ℝ) (207148215519 / 200000000000 : ℝ)
    (3845461229 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell899_rightExp :
    Real.exp (9 / 8 : ℝ) ≤ (3080216849 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 8 : ℝ) (517890768511 / 500000000000 : ℝ)
    (3080216849 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell899_denomUpper :
    Real.exp (9395850191300457 / 1000000000000000 : ℝ) ≤ (120383202054383 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9395850191300457 / 1000000000000000 : ℝ) (268254909963 /
    200000000000 : ℝ) (120383202054383 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell899_denomLower :
    (23779838224507 / 2000000000 : ℝ) ≤ Real.exp (1466163466667071 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1466163466667071 / 156250000000000 : ℝ) (53630189553 /
    40000000000 : ℝ) (23779838224507 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell899_product_lower :
    (1510108779167071 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (899 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell899_leftExp
    (by norm_num : (0 : ℝ) ≤ (3845461229 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell899_product_upper :
    Real.pi * Real.exp (9 / 8 : ℝ) ≤ (9676787691300457 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell899_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell899_endpointLower :
    (41951 / 800000 : ℝ) ≤ hpThetaTraceEndpointLower (899 / 1600 : ℝ) (9 / 16 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1510108779167071 / 156250000000000 : ℝ) (Real.pi * Real.exp (899 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell899_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 8 : ℝ) - (899 / 3200 : ℝ)) ≤
      (120383202054383 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell899_denomUpper
    linarith [hpThetaJensenCell899_product_upper]
  have hi : (1 / (120383202054383 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 8 : ℝ) - (899 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (120383202054383 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (120383202054383 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((899 / 3200 : ℝ) - Real.pi * Real.exp (9 / 8 : ℝ)) := by
    rw [show (899 / 3200 : ℝ) - Real.pi * Real.exp (9 / 8 : ℝ) =
      -(Real.pi * Real.exp (9 / 8 : ℝ) - (899 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (899 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (899 / 800 : ℝ)) := by
    have h := hpThetaJensenCell899_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (120383202054383 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell899_endpointUpper :
    hpThetaJensenKernelEndpointUpper (899 / 1600 : ℝ) (9 / 16 : ℝ) ≤ (533786081 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 8 : ℝ)) (9676787691300457 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 16 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell899_product_upper
  have hD : (23779838224507 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (899 / 800 : ℝ) - (9 / 32 : ℝ)) := by
    apply le_trans hpThetaJensenCell899_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell899_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (899 / 800 : ℝ) - (9 / 32 : ℝ)) ≤
      (1 / (23779838224507 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (23779838224507 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 32 : ℝ) - Real.pi * Real.exp (899 / 800 : ℝ)) ≤
      (2 / (23779838224507 / 2000000000 : ℝ) : ℝ) := by
    rw [show (9 / 32 : ℝ) - Real.pi * Real.exp (899 / 800 : ℝ) =
      -(Real.pi * Real.exp (899 / 800 : ℝ) - (9 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9676787691300457 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9676787691300457 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell899_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (899 / 1600 : ℝ) (9 / 16 : ℝ)) :
    (41951 / 800000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (533786081 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell899_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell899_endpointUpper

def hpThetaJensenCellsBatch044Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (310547529 / 5000000000 : ℝ)
  | 1 => (615671291 / 10000000000 : ℝ)
  | 2 => (610285651 / 10000000000 : ℝ)
  | 3 => (151234489 / 2500000000 : ℝ)
  | 4 => (74953503 / 1250000000 : ℝ)
  | 5 => (297177837 / 5000000000 : ℝ)
  | 6 => (23564829 / 400000000 : ℝ)
  | 7 => (291961497 / 5000000000 : ℝ)
  | 8 => (578762301 / 10000000000 : ℝ)
  | 9 => (573638463 / 10000000000 : ℝ)
  | 10 => (284275651 / 5000000000 : ℝ)
  | 11 => (112700127 / 2000000000 : ℝ)
  | 12 => (558486283 / 10000000000 : ℝ)
  | 13 => (17297127 / 312500000 : ℝ)
  | 14 => (2742829 / 50000000 : ℝ)
  | 15 => (54365931 / 1000000000 : ℝ)
  | 16 => (269394207 / 5000000000 : ℝ)
  | 17 => (533952933 / 10000000000 : ℝ)
  | 18 => (33072043 / 625000000 : ℝ)
  | 19 => (41951 / 800000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch044Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (632051677 / 10000000000 : ℝ)
  | 1 => (626541263 / 10000000000 : ℝ)
  | 2 => (621069503 / 10000000000 : ℝ)
  | 3 => (307818107 / 5000000000 : ℝ)
  | 4 => (61024121 / 1000000000 : ℝ)
  | 5 => (604884309 / 10000000000 : ℝ)
  | 6 => (37472833 / 625000000 : ℝ)
  | 7 => (594284083 / 10000000000 : ℝ)
  | 8 => (58904039 / 1000000000 : ℝ)
  | 9 => (583834067 / 10000000000 : ℝ)
  | 10 => (144666233 / 2500000000 : ℝ)
  | 11 => (573532801 / 10000000000 : ℝ)
  | 12 => (142109373 / 2500000000 : ℝ)
  | 13 => (70422353 / 1250000000 : ℝ)
  | 14 => (279178307 / 5000000000 : ℝ)
  | 15 => (13834267 / 250000000 : ℝ)
  | 16 => (548420841 / 10000000000 : ℝ)
  | 17 => (108701383 / 2000000000 : ℝ)
  | 18 => (269314361 / 5000000000 : ℝ)
  | 19 => (533786081 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch044_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch044Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch044Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell880_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell881_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell882_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell883_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell884_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell885_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell886_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell887_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell888_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell889_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell890_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell891_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell892_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell893_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell894_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell895_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell896_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell897_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell898_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell899_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper] at h ⊢
    exact h

end HodgeProofHP
