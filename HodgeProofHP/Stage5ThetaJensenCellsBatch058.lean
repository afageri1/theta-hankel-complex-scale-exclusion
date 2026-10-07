import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1160_leftExp :
    (852622903 / 200000000 : ℝ) ≤ Real.exp (29 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 20 : ℝ) (209270958939 / 200000000000 : ℝ)
    (852622903 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1160_rightExp :
    Real.exp (1161 / 800 : ℝ) ≤ (10671116851 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1161 / 800 : ℝ) (1046395668729 / 1000000000000 : ℝ)
    (10671116851 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1160_denomUpper :
    Real.exp (32618056001283643 / 2500000000000000 : ℝ) ≤ (4638063525839961 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (32618056001283643 / 2500000000000000 : ℝ) (1503394723459
    / 1000000000000 : ℝ) (4638063525839961 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1160_denomLower :
    (4559570773234487 / 10000000000 : ℝ) ≤ Real.exp (325753848885197 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (325753848885197 / 25000000000000 : ℝ) (187824130401 /
    125000000000 : ℝ) (4559570773234487 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1160_product_lower :
    (334824161385197 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1160_leftExp
    (by norm_num : (0 : ℝ) ≤ (852622903 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1160_product_upper :
    Real.pi * Real.exp (1161 / 800 : ℝ) ≤ (33524306001283643 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1160_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1160_endpointLower :
    (27473897 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 40 : ℝ) (1161 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (334824161385197 / 25000000000000 : ℝ) (Real.pi * Real.exp (29 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell1160_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1161 / 800 : ℝ) - (29 / 80 : ℝ)) ≤
      (4638063525839961 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1160_denomUpper
    linarith [hpThetaJensenCell1160_product_upper]
  have hi : (1 / (4638063525839961 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1161 / 800 : ℝ) - (29 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4638063525839961 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4638063525839961 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 80 : ℝ) - Real.pi * Real.exp (1161 / 800 : ℝ)) := by
    rw [show (29 / 80 : ℝ) - Real.pi * Real.exp (1161 / 800 : ℝ) =
      -(Real.pi * Real.exp (1161 / 800 : ℝ) - (29 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 20 : ℝ)) := by
    have h := hpThetaJensenCell1160_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4638063525839961 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1160_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 40 : ℝ) (1161 / 1600 : ℝ) ≤ (14047521 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1161 / 800 : ℝ)) (33524306001283643 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1161 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1160_product_upper
  have hD : (4559570773234487 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 20 : ℝ) - (1161 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1160_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1160_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 20 : ℝ) - (1161 / 3200 : ℝ)) ≤
      (1 / (4559570773234487 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4559570773234487 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1161 / 3200 : ℝ) - Real.pi * Real.exp (29 / 20 : ℝ)) ≤
      (2 / (4559570773234487 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1161 / 3200 : ℝ) - Real.pi * Real.exp (29 / 20 : ℝ) =
      -(Real.pi * Real.exp (29 / 20 : ℝ) - (1161 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33524306001283643 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (33524306001283643 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1160_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 40 : ℝ) (1161 / 1600 : ℝ)) :
    (27473897 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14047521 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1160_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1160_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1161_leftExp :
    (21342233701 / 5000000000 : ℝ) ≤ Real.exp (1161 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1161 / 800 : ℝ) (130799458591 / 125000000000 : ℝ)
    (21342233701 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1161_rightExp :
    Real.exp (581 / 400 : ℝ) ≤ (42737856349 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (581 / 400 : ℝ) (523218272179 / 500000000000 : ℝ)
    (42737856349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1161_denomUpper :
    Real.exp (130636825341023957 / 10000000000000000 : ℝ) ≤ (943007688373791 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (130636825341023957 / 10000000000000000 : ℝ)
    (1504168237319 / 1000000000000 : ℝ) (943007688373791 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1161_denomLower :
    (579393231740227 / 1250000000 : ℝ) ≤ Real.exp (8154120707148999 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8154120707148999 / 625000000000000 : ℝ) (300673032001 /
    200000000000 : ℝ) (579393231740227 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1161_product_lower :
    (8381073832148999 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1161 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1161_leftExp
    (by norm_num : (0 : ℝ) ≤ (21342233701 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1161_product_upper :
    Real.pi * Real.exp (581 / 400 : ℝ) ≤ (134264950341023957 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1161_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1161_endpointLower :
    (27097291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1161 / 1600 : ℝ) (581 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8381073832148999 / 625000000000000 : ℝ) (Real.pi * Real.exp (1161 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1161_product_lower
  have hD : Real.exp (Real.pi * Real.exp (581 / 400 : ℝ) - (1161 / 3200 : ℝ)) ≤
      (943007688373791 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1161_denomUpper
    linarith [hpThetaJensenCell1161_product_upper]
  have hi : (1 / (943007688373791 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (581 / 400 : ℝ) - (1161 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (943007688373791 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (943007688373791 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1161 / 3200 : ℝ) - Real.pi * Real.exp (581 / 400 : ℝ)) := by
    rw [show (1161 / 3200 : ℝ) - Real.pi * Real.exp (581 / 400 : ℝ) =
      -(Real.pi * Real.exp (581 / 400 : ℝ) - (1161 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1161 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1161 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1161_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (943007688373791 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1161_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1161 / 1600 : ℝ) (581 / 800 : ℝ) ≤ (865953 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (581 / 400 : ℝ)) (134264950341023957 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (581 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1161_product_upper
  have hD : (579393231740227 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1161 / 800 : ℝ) - (581 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1161_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1161_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1161 / 800 : ℝ) - (581 / 1600 : ℝ)) ≤
      (1 / (579393231740227 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (579393231740227 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((581 / 1600 : ℝ) - Real.pi * Real.exp (1161 / 800 : ℝ)) ≤
      (2 / (579393231740227 / 1250000000 : ℝ) : ℝ) := by
    rw [show (581 / 1600 : ℝ) - Real.pi * Real.exp (1161 / 800 : ℝ) =
      -(Real.pi * Real.exp (1161 / 800 : ℝ) - (581 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (134264950341023957 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (134264950341023957 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1161_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1161 / 1600 : ℝ) (581 / 800 : ℝ)) :
    (27097291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (865953 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1161_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1161_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1162_leftExp :
    (42737856347 / 10000000000 : ℝ) ≤ Real.exp (581 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (581 / 400 : ℝ) (1046436544357 / 1000000000000 : ℝ)
    (42737856347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1162_rightExp :
    Real.exp (1163 / 800 : ℝ) ≤ (42791312073 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1163 / 800 : ℝ) (65404838849 / 62500000000 : ℝ)
    (42791312073 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1162_denomUpper :
    Real.exp (130801636469352289 / 10000000000000000 : ℝ) ≤ (149793481904197 / 312500000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (130801636469352289 / 10000000000000000 : ℝ)
    (752471567901 / 500000000000 : ℝ) (149793481904197 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1162_denomLower :
    (94241446441279 / 200000000 : ℝ) ≤ Real.exp (16328816574610553 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16328816574610553 / 1250000000000000 : ℝ) (1504138658403
    / 1000000000000 : ℝ) (94241446441279 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1162_product_lower :
    (16783113449610553 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (581 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1162_leftExp
    (by norm_num : (0 : ℝ) ≤ (42737856347 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1162_product_upper :
    Real.pi * Real.exp (1163 / 800 : ℝ) ≤ (134432886469352289 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1162_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1162_endpointLower :
    (26725281 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (581 / 800 : ℝ) (1163 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16783113449610553 / 1250000000000000 : ℝ) (Real.pi * Real.exp (581 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1162_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1163 / 800 : ℝ) - (581 / 1600 : ℝ)) ≤
      (149793481904197 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1162_denomUpper
    linarith [hpThetaJensenCell1162_product_upper]
  have hi : (1 / (149793481904197 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1163 / 800 : ℝ) - (581 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (149793481904197 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (149793481904197 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((581 / 1600 : ℝ) - Real.pi * Real.exp (1163 / 800 : ℝ)) := by
    rw [show (581 / 1600 : ℝ) - Real.pi * Real.exp (1163 / 800 : ℝ) =
      -(Real.pi * Real.exp (1163 / 800 : ℝ) - (581 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (581 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (581 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1162_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (149793481904197 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1162_endpointUpper :
    hpThetaJensenKernelEndpointUpper (581 / 800 : ℝ) (1163 / 1600 : ℝ) ≤ (5466127 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1163 / 800 : ℝ)) (134432886469352289 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1163 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1162_product_upper
  have hD : (94241446441279 / 200000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (581 / 400 : ℝ) - (1163 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1162_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1162_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (581 / 400 : ℝ) - (1163 / 3200 : ℝ)) ≤
      (1 / (94241446441279 / 200000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (94241446441279 / 200000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1163 / 3200 : ℝ) - Real.pi * Real.exp (581 / 400 : ℝ)) ≤
      (2 / (94241446441279 / 200000000 : ℝ) : ℝ) := by
    rw [show (1163 / 3200 : ℝ) - Real.pi * Real.exp (581 / 400 : ℝ) =
      -(Real.pi * Real.exp (581 / 400 : ℝ) - (1163 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (134432886469352289 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (134432886469352289 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1162_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (581 / 800 : ℝ) (1163 / 1600 : ℝ)) :
    (26725281 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5466127 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1162_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1162_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1163_leftExp :
    (4279131207 / 1000000000 : ℝ) ≤ Real.exp (1163 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1163 / 800 : ℝ) (1046477421583 / 1000000000000 : ℝ)
    (4279131207 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1163_rightExp :
    Real.exp (291 / 200 : ℝ) ≤ (21422417329 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (291 / 200 : ℝ) (1046518300407 / 1000000000000 : ℝ)
    (21422417329 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1163_denomUpper :
    Real.exp (65483328823865097 / 5000000000000000 : ℝ) ≤ (4873148803927263 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (65483328823865097 / 5000000000000000 : ℝ) (376429855463
    / 250000000000 : ℝ) (4873148803927263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1163_denomLower :
    (479037598402727 / 1000000000 : ℝ) ≤ Real.exp (1634941795857693 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1634941795857693 / 125000000000000 : ℝ) (752456770691 /
    500000000000 : ℝ) (479037598402727 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1163_product_lower :
    (1680410545857693 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1163 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1163_leftExp
    (by norm_num : (0 : ℝ) ≤ (4279131207 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1163_product_upper :
    Real.pi * Real.exp (291 / 200 : ℝ) ≤ (67300516323865097 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1163_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1163_endpointLower :
    (26357819 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1163 / 1600 : ℝ) (291 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1680410545857693 / 125000000000000 : ℝ) (Real.pi * Real.exp (1163 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1163_product_lower
  have hD : Real.exp (Real.pi * Real.exp (291 / 200 : ℝ) - (1163 / 3200 : ℝ)) ≤
      (4873148803927263 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1163_denomUpper
    linarith [hpThetaJensenCell1163_product_upper]
  have hi : (1 / (4873148803927263 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (291 / 200 : ℝ) - (1163 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4873148803927263 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4873148803927263 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1163 / 3200 : ℝ) - Real.pi * Real.exp (291 / 200 : ℝ)) := by
    rw [show (1163 / 3200 : ℝ) - Real.pi * Real.exp (291 / 200 : ℝ) =
      -(Real.pi * Real.exp (291 / 200 : ℝ) - (1163 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1163 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1163 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1163_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4873148803927263 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1163_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1163 / 1600 : ℝ) (291 / 400 : ℝ) ≤ (2695541 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (291 / 200 : ℝ)) (67300516323865097 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (291 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1163_product_upper
  have hD : (479037598402727 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1163 / 800 : ℝ) - (291 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1163_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1163_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1163 / 800 : ℝ) - (291 / 800 : ℝ)) ≤
      (1 / (479037598402727 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (479037598402727 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((291 / 800 : ℝ) - Real.pi * Real.exp (1163 / 800 : ℝ)) ≤
      (2 / (479037598402727 / 1000000000 : ℝ) : ℝ) := by
    rw [show (291 / 800 : ℝ) - Real.pi * Real.exp (1163 / 800 : ℝ) =
      -(Real.pi * Real.exp (1163 / 800 : ℝ) - (291 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67300516323865097 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (67300516323865097 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1163_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1163 / 1600 : ℝ) (291 / 400 : ℝ)) :
    (26357819 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2695541 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1163_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1163_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1164_leftExp :
    (8568966931 / 2000000000 : ℝ) ≤ Real.exp (291 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (291 / 200 : ℝ) (523259150203 / 500000000000 : ℝ)
    (8568966931 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1164_rightExp :
    Real.exp (233 / 160 : ℝ) ≤ (42898424187 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (233 / 160 : ℝ) (523279590413 / 500000000000 : ℝ)
    (42898424187 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1164_denomUpper :
    Real.exp (131131889136909891 / 10000000000000000 : ℝ) ≤ (4954337466401977 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (131131889136909891 / 10000000000000000 : ℝ)
    (1506497098431 / 1000000000000 : ℝ) (4954337466401977 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1164_denomLower :
    (4870083167046393 / 10000000000 : ℝ) ≤ Real.exp (3274009119836769 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3274009119836769 / 250000000000000 : ℝ) (301137962383 /
    200000000000 : ℝ) (4870083167046393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1164_product_lower :
    (3365024744836769 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (291 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1164_leftExp
    (by norm_num : (0 : ℝ) ≤ (8568966931 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1164_product_upper :
    Real.pi * Real.exp (233 / 160 : ℝ) ≤ (134769389136909891 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1164_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1164_endpointLower :
    (3249357 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (291 / 400 : ℝ) (233 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3365024744836769 / 250000000000000 : ℝ) (Real.pi * Real.exp (291 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1164_product_lower
  have hD : Real.exp (Real.pi * Real.exp (233 / 160 : ℝ) - (291 / 800 : ℝ)) ≤
      (4954337466401977 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1164_denomUpper
    linarith [hpThetaJensenCell1164_product_upper]
  have hi : (1 / (4954337466401977 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (233 / 160 : ℝ) - (291 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4954337466401977 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4954337466401977 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((291 / 800 : ℝ) - Real.pi * Real.exp (233 / 160 : ℝ)) := by
    rw [show (291 / 800 : ℝ) - Real.pi * Real.exp (233 / 160 : ℝ) =
      -(Real.pi * Real.exp (233 / 160 : ℝ) - (291 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (291 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (291 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1164_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4954337466401977 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1164_endpointUpper :
    hpThetaJensenKernelEndpointUpper (291 / 400 : ℝ) (233 / 320 : ℝ) ≤ (6646193 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (233 / 160 : ℝ)) (134769389136909891 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (233 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1164_product_upper
  have hD : (4870083167046393 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (291 / 200 : ℝ) - (233 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1164_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1164_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (291 / 200 : ℝ) - (233 / 640 : ℝ)) ≤
      (1 / (4870083167046393 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4870083167046393 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((233 / 640 : ℝ) - Real.pi * Real.exp (291 / 200 : ℝ)) ≤
      (2 / (4870083167046393 / 10000000000 : ℝ) : ℝ) := by
    rw [show (233 / 640 : ℝ) - Real.pi * Real.exp (291 / 200 : ℝ) =
      -(Real.pi * Real.exp (291 / 200 : ℝ) - (233 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (134769389136909891 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (134769389136909891 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1164_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (291 / 400 : ℝ) (233 / 320 : ℝ)) :
    (3249357 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6646193 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1164_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1164_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1165_leftExp :
    (8579684837 / 2000000000 : ℝ) ≤ Real.exp (233 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (233 / 160 : ℝ) (41862367233 / 40000000000 : ℝ)
    (8579684837 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1165_rightExp :
    Real.exp (583 / 400 : ℝ) ≤ (21476040373 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (583 / 400 : ℝ) (1046600062843 / 1000000000000 : ℝ)
    (21476040373 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1165_denomUpper :
    Real.exp (65648665603534189 / 5000000000000000 : ℝ) ≤ (503698483357853 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (65648665603534189 / 5000000000000000 : ℝ) (188409521069
    / 125000000000 : ℝ) (503698483357853 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1165_denomLower :
    (4951220729718403 / 10000000000 : ℝ) ≤ Real.exp (3278139905805063 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3278139905805063 / 250000000000000 : ℝ) (1506467472963 /
    1000000000000 : ℝ) (4951220729718403 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1165_product_lower :
    (3369233655805063 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (233 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1165_leftExp
    (by norm_num : (0 : ℝ) ≤ (8579684837 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1165_product_upper :
    Real.pi * Real.exp (583 / 400 : ℝ) ≤ (67468978103534189 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1165_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1165_endpointLower :
    (25636347 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (233 / 320 : ℝ) (583 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3369233655805063 / 250000000000000 : ℝ) (Real.pi * Real.exp (233 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1165_product_lower
  have hD : Real.exp (Real.pi * Real.exp (583 / 400 : ℝ) - (233 / 640 : ℝ)) ≤
      (503698483357853 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1165_denomUpper
    linarith [hpThetaJensenCell1165_product_upper]
  have hi : (1 / (503698483357853 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (583 / 400 : ℝ) - (233 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (503698483357853 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (503698483357853 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((233 / 640 : ℝ) - Real.pi * Real.exp (583 / 400 : ℝ)) := by
    rw [show (233 / 640 : ℝ) - Real.pi * Real.exp (583 / 400 : ℝ) =
      -(Real.pi * Real.exp (583 / 400 : ℝ) - (233 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (233 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (233 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1165_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (503698483357853 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1165_endpointUpper :
    hpThetaJensenKernelEndpointUpper (233 / 320 : ℝ) (583 / 800 : ℝ) ≤ (26218673 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (583 / 400 : ℝ)) (67468978103534189 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (583 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1165_product_upper
  have hD : (4951220729718403 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (233 / 160 : ℝ) - (583 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1165_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1165_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (233 / 160 : ℝ) - (583 / 1600 : ℝ)) ≤
      (1 / (4951220729718403 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4951220729718403 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((583 / 1600 : ℝ) - Real.pi * Real.exp (233 / 160 : ℝ)) ≤
      (2 / (4951220729718403 / 10000000000 : ℝ) : ℝ) := by
    rw [show (583 / 1600 : ℝ) - Real.pi * Real.exp (233 / 160 : ℝ) =
      -(Real.pi * Real.exp (233 / 160 : ℝ) - (583 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67468978103534189 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (67468978103534189 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1165_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (233 / 320 : ℝ) (583 / 800 : ℝ)) :
    (25636347 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (26218673 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1165_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1165_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1166_leftExp :
    (5369010093 / 1250000000 : ℝ) ≤ Real.exp (583 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (583 / 400 : ℝ) (523300031421 / 500000000000 : ℝ)
    (5369010093 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1166_rightExp :
    Real.exp (1167 / 800 : ℝ) ≤ (43005804417 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1167 / 800 : ℝ) (130830118307 / 125000000000 : ℝ)
    (43005804417 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1166_denomUpper :
    Real.exp (131462984115816281 / 10000000000000000 : ℝ) ≤ (5121118880951817 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (131462984115816281 / 10000000000000000 : ℝ)
    (754028317587 / 500000000000 : ℝ) (5121118880951817 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1166_denomLower :
    (503381607696377 / 1000000000 : ℝ) ≤ Real.exp (2051422472636007 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2051422472636007 / 156250000000000 : ℝ) (150724652751 /
    100000000000 : ℝ) (503381607696377 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1166_product_lower :
    (2108404894511007 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (583 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1166_leftExp
    (by norm_num : (0 : ℝ) ≤ (5369010093 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1166_product_upper :
    Real.pi * Real.exp (1167 / 800 : ℝ) ≤ (135106734115816281 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1166_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1166_endpointLower :
    (25282243 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (583 / 800 : ℝ) (1167 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2108404894511007 / 156250000000000 : ℝ) (Real.pi * Real.exp (583 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1166_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1167 / 800 : ℝ) - (583 / 1600 : ℝ)) ≤
      (5121118880951817 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1166_denomUpper
    linarith [hpThetaJensenCell1166_product_upper]
  have hi : (1 / (5121118880951817 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1167 / 800 : ℝ) - (583 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5121118880951817 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5121118880951817 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((583 / 1600 : ℝ) - Real.pi * Real.exp (1167 / 800 : ℝ)) := by
    rw [show (583 / 1600 : ℝ) - Real.pi * Real.exp (1167 / 800 : ℝ) =
      -(Real.pi * Real.exp (1167 / 800 : ℝ) - (583 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (583 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (583 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1166_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5121118880951817 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1166_endpointUpper :
    hpThetaJensenKernelEndpointUpper (583 / 800 : ℝ) (1167 / 1600 : ℝ) ≤ (5171413 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1167 / 800 : ℝ)) (135106734115816281 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1167 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1166_product_upper
  have hD : (503381607696377 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (583 / 400 : ℝ) - (1167 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1166_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1166_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (583 / 400 : ℝ) - (1167 / 3200 : ℝ)) ≤
      (1 / (503381607696377 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (503381607696377 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1167 / 3200 : ℝ) - Real.pi * Real.exp (583 / 400 : ℝ)) ≤
      (2 / (503381607696377 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1167 / 3200 : ℝ) - Real.pi * Real.exp (583 / 400 : ℝ) =
      -(Real.pi * Real.exp (583 / 400 : ℝ) - (1167 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (135106734115816281 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (135106734115816281 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1166_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (583 / 800 : ℝ) (1167 / 1600 : ℝ)) :
    (25282243 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5171413 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1166_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1166_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1167_leftExp :
    (21502902207 / 5000000000 : ℝ) ≤ Real.exp (1167 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1167 / 800 : ℝ) (209328189291 / 200000000000 : ℝ)
    (21502902207 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1167_rightExp :
    Real.exp (73 / 50 : ℝ) ≤ (8611919057 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 50 : ℝ) (1046681831667 / 1000000000000 : ℝ)
    (8611919057 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1167_denomUpper :
    Real.exp (26325769626037801 / 2000000000000000 : ℝ) ≤ (52067681575929 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (26325769626037801 / 2000000000000000 : ℝ) (150883850131
    / 100000000000 : ℝ) (52067681575929 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1167_denomLower :
    (2558948583399899 / 5000000000 : ℝ) ≤ Real.exp (8216043193786693 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8216043193786693 / 625000000000000 : ℝ) (1508026978517 /
    1000000000000 : ℝ) (2558948583399899 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1167_product_lower :
    (8444168193786693 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1167 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1167_leftExp
    (by norm_num : (0 : ℝ) ≤ (21502902207 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1167_product_upper :
    Real.pi * Real.exp (73 / 50 : ℝ) ≤ (27055144626037801 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1167_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1167_endpointLower :
    (12466249 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1167 / 1600 : ℝ) (73 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8444168193786693 / 625000000000000 : ℝ) (Real.pi * Real.exp (1167 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1167_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 50 : ℝ) - (1167 / 3200 : ℝ)) ≤
      (52067681575929 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1167_denomUpper
    linarith [hpThetaJensenCell1167_product_upper]
  have hi : (1 / (52067681575929 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 50 : ℝ) - (1167 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (52067681575929 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (52067681575929 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1167 / 3200 : ℝ) - Real.pi * Real.exp (73 / 50 : ℝ)) := by
    rw [show (1167 / 3200 : ℝ) - Real.pi * Real.exp (73 / 50 : ℝ) =
      -(Real.pi * Real.exp (73 / 50 : ℝ) - (1167 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1167 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1167 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1167_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (52067681575929 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1167_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1167 / 1600 : ℝ) (73 / 100 : ℝ) ≤ (12749951 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 50 : ℝ)) (27055144626037801 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1167_product_upper
  have hD : (2558948583399899 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1167 / 800 : ℝ) - (73 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1167_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1167_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1167 / 800 : ℝ) - (73 / 200 : ℝ)) ≤
      (1 / (2558948583399899 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2558948583399899 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 200 : ℝ) - Real.pi * Real.exp (1167 / 800 : ℝ)) ≤
      (2 / (2558948583399899 / 5000000000 : ℝ) : ℝ) := by
    rw [show (73 / 200 : ℝ) - Real.pi * Real.exp (1167 / 800 : ℝ) =
      -(Real.pi * Real.exp (1167 / 800 : ℝ) - (73 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27055144626037801 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (27055144626037801 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1167_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1167 / 1600 : ℝ) (73 / 100 : ℝ)) :
    (12466249 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12749951 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1167_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1167_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1168_leftExp :
    (43059595283 / 10000000000 : ℝ) ≤ Real.exp (73 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 50 : ℝ) (523340915833 / 500000000000 : ℝ)
    (43059595283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1168_rightExp :
    Real.exp (1169 / 800 : ℝ) ≤ (43113453433 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1169 / 800 : ℝ) (523361359237 / 500000000000 : ℝ)
    (43113453433 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1168_denomUpper :
    Real.exp (131794923510938769 / 10000000000000000 : ℝ) ≤ (5293961789752813 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (131794923510938769 / 10000000000000000 : ℝ)
    (1509621769947 / 1000000000000 : ℝ) (5293961789752813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1168_denomLower :
    (1040698506954881 / 2000000000 : ℝ) ≤ Real.exp (16452819383038817 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16452819383038817 / 1250000000000000 : ℝ) (754404414519
    / 500000000000 : ℝ) (1040698506954881 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1168_product_lower :
    (16909460008038817 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1168_leftExp
    (by norm_num : (0 : ℝ) ≤ (43059595283 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1168_product_upper :
    Real.pi * Real.exp (1169 / 800 : ℝ) ≤ (135444923510938769 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1168_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1168_endpointLower :
    (24587067 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 100 : ℝ) (1169 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16909460008038817 / 1250000000000000 : ℝ) (Real.pi * Real.exp (73 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1168_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1169 / 800 : ℝ) - (73 / 200 : ℝ)) ≤
      (5293961789752813 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1168_denomUpper
    linarith [hpThetaJensenCell1168_product_upper]
  have hi : (1 / (5293961789752813 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1169 / 800 : ℝ) - (73 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5293961789752813 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5293961789752813 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 200 : ℝ) - Real.pi * Real.exp (1169 / 800 : ℝ)) := by
    rw [show (73 / 200 : ℝ) - Real.pi * Real.exp (1169 / 800 : ℝ) =
      -(Real.pi * Real.exp (1169 / 800 : ℝ) - (73 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1168_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5293961789752813 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1168_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 100 : ℝ) (1169 / 1600 : ℝ) ≤ (5029427 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1169 / 800 : ℝ)) (135444923510938769 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1169 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1168_product_upper
  have hD : (1040698506954881 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 50 : ℝ) - (1169 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1168_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1168_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 50 : ℝ) - (1169 / 3200 : ℝ)) ≤
      (1 / (1040698506954881 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1040698506954881 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1169 / 3200 : ℝ) - Real.pi * Real.exp (73 / 50 : ℝ)) ≤
      (2 / (1040698506954881 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1169 / 3200 : ℝ) - Real.pi * Real.exp (73 / 50 : ℝ) =
      -(Real.pi * Real.exp (73 / 50 : ℝ) - (1169 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (135444923510938769 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (135444923510938769 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1168_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 100 : ℝ) (1169 / 1600 : ℝ)) :
    (24587067 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5029427 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1168_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1168_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1169_leftExp :
    (43113453431 / 10000000000 : ℝ) ≤ Real.exp (1169 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1169 / 800 : ℝ) (1046722718473 / 1000000000000 : ℝ)
    (43113453431 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1169_rightExp :
    Real.exp (117 / 80 : ℝ) ≤ (21583689473 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (117 / 80 : ℝ) (1046763606879 / 1000000000000 : ℝ)
    (21583689473 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1169_denomUpper :
    Real.exp (65980605262550489 / 5000000000000000 : ℝ) ≤ (1345682375020023 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (65980605262550489 / 5000000000000000 : ℝ) (377601611027
    / 250000000000 : ℝ) (1345682375020023 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1169_denomLower :
    (2645315642117397 / 5000000000 : ℝ) ≤ Real.exp (16473578798900269 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16473578798900269 / 1250000000000000 : ℝ) (754796041009
    / 500000000000 : ℝ) (2645315642117397 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1169_product_lower :
    (16930610048900269 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1169 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1169_leftExp
    (by norm_num : (0 : ℝ) ≤ (43113453431 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1169_product_upper :
    Real.pi * Real.exp (117 / 80 : ℝ) ≤ (67807167762550489 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1169_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1169_endpointLower :
    (24245903 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1169 / 1600 : ℝ) (117 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16930610048900269 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1169 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1169_product_lower
  have hD : Real.exp (Real.pi * Real.exp (117 / 80 : ℝ) - (1169 / 3200 : ℝ)) ≤
      (1345682375020023 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1169_denomUpper
    linarith [hpThetaJensenCell1169_product_upper]
  have hi : (1 / (1345682375020023 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (117 / 80 : ℝ) - (1169 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1345682375020023 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1345682375020023 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1169 / 3200 : ℝ) - Real.pi * Real.exp (117 / 80 : ℝ)) := by
    rw [show (1169 / 3200 : ℝ) - Real.pi * Real.exp (117 / 80 : ℝ) =
      -(Real.pi * Real.exp (117 / 80 : ℝ) - (1169 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1169 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1169 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1169_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1345682375020023 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1169_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1169 / 1600 : ℝ) (117 / 160 : ℝ) ≤ (24798719 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (117 / 80 : ℝ)) (67807167762550489 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (117 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1169_product_upper
  have hD : (2645315642117397 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1169 / 800 : ℝ) - (117 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1169_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1169_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1169 / 800 : ℝ) - (117 / 320 : ℝ)) ≤
      (1 / (2645315642117397 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2645315642117397 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((117 / 320 : ℝ) - Real.pi * Real.exp (1169 / 800 : ℝ)) ≤
      (2 / (2645315642117397 / 5000000000 : ℝ) : ℝ) := by
    rw [show (117 / 320 : ℝ) - Real.pi * Real.exp (1169 / 800 : ℝ) =
      -(Real.pi * Real.exp (1169 / 800 : ℝ) - (117 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (67807167762550489 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (67807167762550489 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1169_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1169 / 1600 : ℝ) (117 / 160 : ℝ)) :
    (24245903 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (24798719 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1169_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1169_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1170_leftExp :
    (84311287 / 19531250 : ℝ) ≤ Real.exp (117 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (117 / 80 : ℝ) (523381803439 / 500000000000 : ℝ)
    (84311287 / 19531250 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1170_rightExp :
    Real.exp (1171 / 800 : ℝ) ≤ (43221371909 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1171 / 800 : ℝ) (1046804496881 / 1000000000000 : ℝ)
    (43221371909 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1170_denomUpper :
    Real.exp (132127709439711037 / 10000000000000000 : ℝ) ≤ (5473101617361307 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (132127709439711037 / 10000000000000000 : ℝ)
    (188899065853 / 125000000000 : ℝ) (5473101617361307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1170_denomLower :
    (5379343120517981 / 10000000000 : ℝ) ≤ Real.exp (257724447952029 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (257724447952029 / 19531250000000 : ℝ) (1510376740493 /
    1000000000000 : ℝ) (5379343120517981 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1170_product_lower :
    (33108958093613 / 2441406250000 : ℝ) ≤ Real.pi * Real.exp (117 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1170_leftExp
    (by norm_num : (0 : ℝ) ≤ (84311287 / 19531250 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1170_product_upper :
    Real.pi * Real.exp (1171 / 800 : ℝ) ≤ (135783959439711037 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1170_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1170_endpointLower :
    (23908961 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (117 / 160 : ℝ) (1171 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (33108958093613 / 2441406250000 : ℝ) (Real.pi * Real.exp (117 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1170_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1171 / 800 : ℝ) - (117 / 320 : ℝ)) ≤
      (5473101617361307 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1170_denomUpper
    linarith [hpThetaJensenCell1170_product_upper]
  have hi : (1 / (5473101617361307 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1171 / 800 : ℝ) - (117 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (5473101617361307 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (5473101617361307 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((117 / 320 : ℝ) - Real.pi * Real.exp (1171 / 800 : ℝ)) := by
    rw [show (117 / 320 : ℝ) - Real.pi * Real.exp (1171 / 800 : ℝ) =
      -(Real.pi * Real.exp (1171 / 800 : ℝ) - (117 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (117 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (117 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1170_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (5473101617361307 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1170_endpointUpper :
    hpThetaJensenKernelEndpointUpper (117 / 160 : ℝ) (1171 / 1600 : ℝ) ≤ (1528413 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1171 / 800 : ℝ)) (135783959439711037 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1171 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1170_product_upper
  have hD : (5379343120517981 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (117 / 80 : ℝ) - (1171 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1170_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1170_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (117 / 80 : ℝ) - (1171 / 3200 : ℝ)) ≤
      (1 / (5379343120517981 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5379343120517981 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1171 / 3200 : ℝ) - Real.pi * Real.exp (117 / 80 : ℝ)) ≤
      (2 / (5379343120517981 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1171 / 3200 : ℝ) - Real.pi * Real.exp (117 / 80 : ℝ) =
      -(Real.pi * Real.exp (117 / 80 : ℝ) - (1171 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (135783959439711037 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (135783959439711037 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1170_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (117 / 160 : ℝ) (1171 / 1600 : ℝ)) :
    (23908961 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1528413 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1170_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1170_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1171_leftExp :
    (21610685953 / 5000000000 : ℝ) ≤ Real.exp (1171 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1171 / 800 : ℝ) (13085056211 / 12500000000 : ℝ)
    (21610685953 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1171_rightExp :
    Real.exp (293 / 200 : ℝ) ≤ (10818858101 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (293 / 200 : ℝ) (3271391839 / 3125000000 : ℝ)
    (10818858101 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1171_denomUpper :
    Real.exp (33073605128094893 / 2500000000000000 : ℝ) ≤ (278255454182663 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33073605128094893 / 2500000000000000 : ℝ) (377995005271
    / 250000000000 : ℝ) (278255454182663 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1171_denomLower :
    (1093931670313623 / 2000000000 : ℝ) ≤ Real.exp (8257588513057147 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8257588513057147 / 625000000000000 : ℝ) (1511162807479 /
    1000000000000 : ℝ) (1093931670313623 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1171_product_lower :
    (8486494763057147 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1171 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1171_leftExp
    (by norm_num : (0 : ℝ) ≤ (21610685953 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1171_product_upper :
    Real.pi * Real.exp (293 / 200 : ℝ) ≤ (33988448878094893 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1171_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1171_endpointLower :
    (5894049 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1171 / 1600 : ℝ) (293 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8486494763057147 / 625000000000000 : ℝ) (Real.pi * Real.exp (1171 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1171_product_lower
  have hD : Real.exp (Real.pi * Real.exp (293 / 200 : ℝ) - (1171 / 3200 : ℝ)) ≤
      (278255454182663 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1171_denomUpper
    linarith [hpThetaJensenCell1171_product_upper]
  have hi : (1 / (278255454182663 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (293 / 200 : ℝ) - (1171 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (278255454182663 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (278255454182663 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1171 / 3200 : ℝ) - Real.pi * Real.exp (293 / 200 : ℝ)) := by
    rw [show (1171 / 3200 : ℝ) - Real.pi * Real.exp (293 / 200 : ℝ) =
      -(Real.pi * Real.exp (293 / 200 : ℝ) - (1171 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1171 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1171 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1171_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (278255454182663 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1171_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1171 / 1600 : ℝ) (293 / 400 : ℝ) ≤ (4822951 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (293 / 200 : ℝ)) (33988448878094893 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (293 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1171_product_upper
  have hD : (1093931670313623 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1171 / 800 : ℝ) - (293 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1171_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1171_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1171 / 800 : ℝ) - (293 / 800 : ℝ)) ≤
      (1 / (1093931670313623 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1093931670313623 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((293 / 800 : ℝ) - Real.pi * Real.exp (1171 / 800 : ℝ)) ≤
      (2 / (1093931670313623 / 2000000000 : ℝ) : ℝ) := by
    rw [show (293 / 800 : ℝ) - Real.pi * Real.exp (1171 / 800 : ℝ) =
      -(Real.pi * Real.exp (1171 / 800 : ℝ) - (293 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33988448878094893 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (33988448878094893 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1171_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1171 / 1600 : ℝ) (293 / 400 : ℝ)) :
    (5894049 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4822951 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1171_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1171_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1172_leftExp :
    (43275432401 / 10000000000 : ℝ) ≤ Real.exp (293 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (293 / 200 : ℝ) (1046845388479 / 1000000000000 : ℝ)
    (43275432401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1172_rightExp :
    Real.exp (1173 / 800 : ℝ) ≤ (21664780259 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1173 / 800 : ℝ) (1046886281677 / 1000000000000 : ℝ)
    (21664780259 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1172_denomUpper :
    Real.exp (66230672008212587 / 5000000000000000 : ℝ) ≤ (1414695870609827 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (66230672008212587 / 5000000000000000 : ℝ) (1512768929963
    / 1000000000000 : ℝ) (1414695870609827 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1172_denomLower :
    (1390401975937543 / 2500000000 : ℝ) ≤ Real.exp (16536015903440299 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16536015903440299 / 1250000000000000 : ℝ) (755975142999
    / 500000000000 : ℝ) (1390401975937543 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1172_product_lower :
    (16994219028440299 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (293 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1172_leftExp
    (by norm_num : (0 : ℝ) ≤ (43275432401 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1172_product_upper :
    Real.pi * Real.exp (1173 / 800 : ℝ) ≤ (68061922008212587 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1172_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1172_endpointLower :
    (5811891 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (293 / 400 : ℝ) (1173 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16994219028440299 / 1250000000000000 : ℝ) (Real.pi * Real.exp (293 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1172_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1173 / 800 : ℝ) - (293 / 800 : ℝ)) ≤
      (1414695870609827 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1172_denomUpper
    linarith [hpThetaJensenCell1172_product_upper]
  have hi : (1 / (1414695870609827 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1173 / 800 : ℝ) - (293 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1414695870609827 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1414695870609827 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((293 / 800 : ℝ) - Real.pi * Real.exp (1173 / 800 : ℝ)) := by
    rw [show (293 / 800 : ℝ) - Real.pi * Real.exp (1173 / 800 : ℝ) =
      -(Real.pi * Real.exp (1173 / 800 : ℝ) - (293 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (293 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (293 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1172_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1414695870609827 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1172_endpointUpper :
    hpThetaJensenKernelEndpointUpper (293 / 400 : ℝ) (1173 / 1600 : ℝ) ≤ (5944779 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1173 / 800 : ℝ)) (68061922008212587 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1173 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1172_product_upper
  have hD : (1390401975937543 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (293 / 200 : ℝ) - (1173 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1172_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1172_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (293 / 200 : ℝ) - (1173 / 3200 : ℝ)) ≤
      (1 / (1390401975937543 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1390401975937543 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1173 / 3200 : ℝ) - Real.pi * Real.exp (293 / 200 : ℝ)) ≤
      (2 / (1390401975937543 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1173 / 3200 : ℝ) - Real.pi * Real.exp (293 / 200 : ℝ) =
      -(Real.pi * Real.exp (293 / 200 : ℝ) - (1173 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68061922008212587 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (68061922008212587 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1172_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (293 / 400 : ℝ) (1173 / 1600 : ℝ)) :
    (5811891 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5944779 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1172_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1172_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1173_leftExp :
    (8665912103 / 2000000000 : ℝ) ≤ Real.exp (1173 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1173 / 800 : ℝ) (261721570419 / 250000000000 : ℝ)
    (8665912103 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1173_rightExp :
    Real.exp (587 / 400 : ℝ) ≤ (21691878167 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (587 / 400 : ℝ) (1046927176471 / 1000000000000 : ℝ)
    (21691878167 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1173_denomUpper :
    Real.exp (66314240106300031 / 5000000000000000 : ℝ) ≤ (719269629449047 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (66314240106300031 / 5000000000000000 : ℝ) (1513559256479
    / 1000000000000 : ℝ) (719269629449047 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1173_denomLower :
    (2827611669240769 / 5000000000 : ℝ) ≤ Real.exp (3311376266935997 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3311376266935997 / 250000000000000 : ℝ) (756369589553 /
    500000000000 : ℝ) (2827611669240769 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1173_product_lower :
    (3403095016935997 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1173 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1173_leftExp
    (by norm_num : (0 : ℝ) ≤ (8665912103 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1173_product_upper :
    Real.pi * Real.exp (587 / 400 : ℝ) ≤ (68147052606300031 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1173_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1173_endpointLower :
    (22923019 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1173 / 1600 : ℝ) (587 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3403095016935997 / 250000000000000 : ℝ) (Real.pi * Real.exp (1173 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1173_product_lower
  have hD : Real.exp (Real.pi * Real.exp (587 / 400 : ℝ) - (1173 / 3200 : ℝ)) ≤
      (719269629449047 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1173_denomUpper
    linarith [hpThetaJensenCell1173_product_upper]
  have hi : (1 / (719269629449047 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (587 / 400 : ℝ) - (1173 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (719269629449047 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (719269629449047 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1173 / 3200 : ℝ) - Real.pi * Real.exp (587 / 400 : ℝ)) := by
    rw [show (1173 / 3200 : ℝ) - Real.pi * Real.exp (587 / 400 : ℝ) =
      -(Real.pi * Real.exp (587 / 400 : ℝ) - (1173 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1173 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1173 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1173_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (719269629449047 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1173_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1173 / 1600 : ℝ) (587 / 800 : ℝ) ≤ (4689529 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (587 / 400 : ℝ)) (68147052606300031 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (587 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1173_product_upper
  have hD : (2827611669240769 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1173 / 800 : ℝ) - (587 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1173_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1173_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1173 / 800 : ℝ) - (587 / 1600 : ℝ)) ≤
      (1 / (2827611669240769 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2827611669240769 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((587 / 1600 : ℝ) - Real.pi * Real.exp (1173 / 800 : ℝ)) ≤
      (2 / (2827611669240769 / 5000000000 : ℝ) : ℝ) := by
    rw [show (587 / 1600 : ℝ) - Real.pi * Real.exp (1173 / 800 : ℝ) =
      -(Real.pi * Real.exp (1173 / 800 : ℝ) - (587 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68147052606300031 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (68147052606300031 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1173_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1173 / 1600 : ℝ) (587 / 800 : ℝ)) :
    (22923019 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4689529 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1173_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1173_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1174_leftExp :
    (43383756331 / 10000000000 : ℝ) ≤ Real.exp (587 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (587 / 400 : ℝ) (104692717647 / 100000000000 : ℝ)
    (43383756331 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1174_rightExp :
    Real.exp (47 / 32 : ℝ) ≤ (43438019937 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 32 : ℝ) (1046968072863 / 1000000000000 : ℝ)
    (43438019937 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1174_denomUpper :
    Real.exp (132795829367939641 / 10000000000000000 : ℝ) ≤ (365703914259927 / 625000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (132795829367939641 / 10000000000000000 : ℝ)
    (757175501843 / 500000000000 : ℝ) (365703914259927 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1174_denomLower :
    (575053685745383 / 1000000000 : ℝ) ≤ Real.exp (16577773352427369 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16577773352427369 / 1250000000000000 : ℝ) (756764744911
    / 500000000000 : ℝ) (575053685745383 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1174_product_lower :
    (17036757727427369 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (587 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1174_leftExp
    (by norm_num : (0 : ℝ) ≤ (43383756331 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1174_product_upper :
    Real.pi * Real.exp (47 / 32 : ℝ) ≤ (136464579367939641 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1174_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1174_endpointLower :
    (565063 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (587 / 800 : ℝ) (47 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17036757727427369 / 1250000000000000 : ℝ) (Real.pi * Real.exp (587 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1174_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 32 : ℝ) - (587 / 1600 : ℝ)) ≤
      (365703914259927 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1174_denomUpper
    linarith [hpThetaJensenCell1174_product_upper]
  have hi : (1 / (365703914259927 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 32 : ℝ) - (587 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (365703914259927 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (365703914259927 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((587 / 1600 : ℝ) - Real.pi * Real.exp (47 / 32 : ℝ)) := by
    rw [show (587 / 1600 : ℝ) - Real.pi * Real.exp (47 / 32 : ℝ) =
      -(Real.pi * Real.exp (47 / 32 : ℝ) - (587 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (587 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (587 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1174_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (365703914259927 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1174_endpointUpper :
    hpThetaJensenKernelEndpointUpper (587 / 800 : ℝ) (47 / 64 : ℝ) ≤ (11560149 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 32 : ℝ)) (136464579367939641 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1174_product_upper
  have hD : (575053685745383 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (587 / 400 : ℝ) - (47 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1174_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1174_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (587 / 400 : ℝ) - (47 / 128 : ℝ)) ≤
      (1 / (575053685745383 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (575053685745383 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 128 : ℝ) - Real.pi * Real.exp (587 / 400 : ℝ)) ≤
      (2 / (575053685745383 / 1000000000 : ℝ) : ℝ) := by
    rw [show (47 / 128 : ℝ) - Real.pi * Real.exp (587 / 400 : ℝ) =
      -(Real.pi * Real.exp (587 / 400 : ℝ) - (47 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (136464579367939641 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (136464579367939641 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1174_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (587 / 800 : ℝ) (47 / 64 : ℝ)) :
    (565063 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11560149 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1174_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1174_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1175_leftExp :
    (8687603987 / 2000000000 : ℝ) ≤ Real.exp (47 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 32 : ℝ) (523484036431 / 500000000000 : ℝ)
    (8687603987 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1175_rightExp :
    Real.exp (147 / 100 : ℝ) ≤ (10873087853 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (147 / 100 : ℝ) (261752242713 / 250000000000 : ℝ)
    (10873087853 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1175_denomUpper :
    Real.exp (33240847937369829 / 2500000000000000 : ℝ) ≤ (595013381959757 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33240847937369829 / 2500000000000000 : ℝ) (189393021831
    / 125000000000 : ℝ) (595013381959757 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1175_denomLower :
    (5847581327099393 / 10000000000 : ℝ) ≤ Real.exp (3319738398090913 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3319738398090913 / 250000000000000 : ℝ) (1514321221217 /
    1000000000000 : ℝ) (5847581327099393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1175_product_lower :
    (3411613398090913 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1175_leftExp
    (by norm_num : (0 : ℝ) ≤ (8687603987 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1175_product_upper :
    Real.pi * Real.exp (147 / 100 : ℝ) ≤ (34158816687369829 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1175_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1175_endpointLower :
    (22286021 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 64 : ℝ) (147 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3411613398090913 / 250000000000000 : ℝ) (Real.pi * Real.exp (47 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1175_product_lower
  have hD : Real.exp (Real.pi * Real.exp (147 / 100 : ℝ) - (47 / 128 : ℝ)) ≤
      (595013381959757 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1175_denomUpper
    linarith [hpThetaJensenCell1175_product_upper]
  have hi : (1 / (595013381959757 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (147 / 100 : ℝ) - (47 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (595013381959757 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (595013381959757 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 128 : ℝ) - Real.pi * Real.exp (147 / 100 : ℝ)) := by
    rw [show (47 / 128 : ℝ) - Real.pi * Real.exp (147 / 100 : ℝ) =
      -(Real.pi * Real.exp (147 / 100 : ℝ) - (47 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1175_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (595013381959757 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1175_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 64 : ℝ) (147 / 200 : ℝ) ≤ (2279703 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (147 / 100 : ℝ)) (34158816687369829 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (147 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1175_product_upper
  have hD : (5847581327099393 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 32 : ℝ) - (147 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1175_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1175_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 32 : ℝ) - (147 / 400 : ℝ)) ≤
      (1 / (5847581327099393 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5847581327099393 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((147 / 400 : ℝ) - Real.pi * Real.exp (47 / 32 : ℝ)) ≤
      (2 / (5847581327099393 / 10000000000 : ℝ) : ℝ) := by
    rw [show (147 / 400 : ℝ) - Real.pi * Real.exp (47 / 32 : ℝ) =
      -(Real.pi * Real.exp (47 / 32 : ℝ) - (147 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34158816687369829 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (34158816687369829 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1175_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 64 : ℝ) (147 / 200 : ℝ)) :
    (22286021 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2279703 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1175_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1175_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1176_leftExp :
    (4349235141 / 1000000000 : ℝ) ≤ Real.exp (147 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (147 / 100 : ℝ) (1047008970851 / 1000000000000 : ℝ)
    (4349235141 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1176_rightExp :
    Real.exp (1177 / 800 : ℝ) ≤ (10886687711 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1177 / 800 : ℝ) (1047049870439 / 1000000000000 : ℝ)
    (10886687711 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1176_denomUpper :
    Real.exp (33282791906063623 / 2500000000000000 : ℝ) ≤ (3025402428666667 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (33282791906063623 / 2500000000000000 : ℝ) (1515938772431
    / 1000000000000 : ℝ) (3025402428666667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1176_denomLower :
    (5946390281696389 / 10000000000 : ℝ) ≤ Real.exp (1661963728135559 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1661963728135559 / 125000000000000 : ℝ) (757557188161 /
    500000000000 : ℝ) (5946390281696389 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1176_product_lower :
    (1707940290635559 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (147 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1176_leftExp
    (by norm_num : (0 : ℝ) ≤ (4349235141 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1176_product_upper :
    Real.pi * Real.exp (1177 / 800 : ℝ) ≤ (34201541906063623 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1176_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1176_endpointLower :
    (21973481 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (147 / 200 : ℝ) (1177 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1707940290635559 / 125000000000000 : ℝ) (Real.pi * Real.exp (147 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1176_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1177 / 800 : ℝ) - (147 / 400 : ℝ)) ≤
      (3025402428666667 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1176_denomUpper
    linarith [hpThetaJensenCell1176_product_upper]
  have hi : (1 / (3025402428666667 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1177 / 800 : ℝ) - (147 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3025402428666667 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3025402428666667 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((147 / 400 : ℝ) - Real.pi * Real.exp (1177 / 800 : ℝ)) := by
    rw [show (147 / 400 : ℝ) - Real.pi * Real.exp (1177 / 800 : ℝ) =
      -(Real.pi * Real.exp (1177 / 800 : ℝ) - (147 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (147 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (147 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1176_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3025402428666667 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1176_endpointUpper :
    hpThetaJensenKernelEndpointUpper (147 / 200 : ℝ) (1177 / 1600 : ℝ) ≤ (11238899 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1177 / 800 : ℝ)) (34201541906063623 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1177 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1176_product_upper
  have hD : (5946390281696389 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (147 / 100 : ℝ) - (1177 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1176_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1176_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (147 / 100 : ℝ) - (1177 / 3200 : ℝ)) ≤
      (1 / (5946390281696389 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5946390281696389 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1177 / 3200 : ℝ) - Real.pi * Real.exp (147 / 100 : ℝ)) ≤
      (2 / (5946390281696389 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1177 / 3200 : ℝ) - Real.pi * Real.exp (147 / 100 : ℝ) =
      -(Real.pi * Real.exp (147 / 100 : ℝ) - (1177 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34201541906063623 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (34201541906063623 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1176_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (147 / 200 : ℝ) (1177 / 1600 : ℝ)) :
    (21973481 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11238899 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1176_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1176_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1177_leftExp :
    (21773375421 / 5000000000 : ℝ) ≤ Real.exp (1177 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1177 / 800 : ℝ) (523524935219 / 500000000000 : ℝ)
    (21773375421 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1177_rightExp :
    Real.exp (589 / 400 : ℝ) ≤ (43601218317 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (589 / 400 : ℝ) (1047090771623 / 1000000000000 : ℝ)
    (43601218317 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1177_denomUpper :
    Real.exp (133299157256158981 / 10000000000000000 : ℝ) ≤ (3076655345334831 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (133299157256158981 / 10000000000000000 : ℝ) (47397962503
    / 31250000000 : ℝ) (3076655345334831 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1177_denomLower :
    (604699794917003 / 1000000000 : ℝ) ≤ Real.exp (8320304629451279 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8320304629451279 / 625000000000000 : ℝ) (75795447911 /
    50000000000 : ℝ) (604699794917003 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1177_product_lower :
    (8550382754451279 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1177 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1177_leftExp
    (by norm_num : (0 : ℝ) ≤ (21773375421 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1177_product_upper :
    Real.pi * Real.exp (589 / 400 : ℝ) ≤ (136977282256158981 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1177_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1177_endpointLower :
    (4332971 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1177 / 1600 : ℝ) (589 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8550382754451279 / 625000000000000 : ℝ) (Real.pi * Real.exp (1177 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1177_product_lower
  have hD : Real.exp (Real.pi * Real.exp (589 / 400 : ℝ) - (1177 / 3200 : ℝ)) ≤
      (3076655345334831 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1177_denomUpper
    linarith [hpThetaJensenCell1177_product_upper]
  have hi : (1 / (3076655345334831 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (589 / 400 : ℝ) - (1177 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3076655345334831 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3076655345334831 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1177 / 3200 : ℝ) - Real.pi * Real.exp (589 / 400 : ℝ)) := by
    rw [show (1177 / 3200 : ℝ) - Real.pi * Real.exp (589 / 400 : ℝ) =
      -(Real.pi * Real.exp (589 / 400 : ℝ) - (1177 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1177 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1177 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1177_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3076655345334831 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1177_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1177 / 1600 : ℝ) (589 / 800 : ℝ) ≤ (22162559 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (589 / 400 : ℝ)) (136977282256158981 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (589 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1177_product_upper
  have hD : (604699794917003 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1177 / 800 : ℝ) - (589 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1177_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1177_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1177 / 800 : ℝ) - (589 / 1600 : ℝ)) ≤
      (1 / (604699794917003 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (604699794917003 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((589 / 1600 : ℝ) - Real.pi * Real.exp (1177 / 800 : ℝ)) ≤
      (2 / (604699794917003 / 1000000000 : ℝ) : ℝ) := by
    rw [show (589 / 1600 : ℝ) - Real.pi * Real.exp (1177 / 800 : ℝ) =
      -(Real.pi * Real.exp (1177 / 800 : ℝ) - (589 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (136977282256158981 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (136977282256158981 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1177_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1177 / 1600 : ℝ) (589 / 800 : ℝ)) :
    (4332971 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22162559 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1177_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1177_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1178_leftExp :
    (8720243663 / 2000000000 : ℝ) ≤ Real.exp (589 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (589 / 400 : ℝ) (523545385811 / 500000000000 : ℝ)
    (8720243663 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1178_rightExp :
    Real.exp (1179 / 800 : ℝ) ≤ (21827876959 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1179 / 800 : ℝ) (209426334881 / 200000000000 : ℝ)
    (21827876959 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1178_denomUpper :
    Real.exp (66733680459255687 / 5000000000000000 : ℝ) ≤ (6257686992995297 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (66733680459255687 / 5000000000000000 : ℝ) (1517532260753
    / 1000000000000 : ℝ) (6257686992995297 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1178_denomLower :
    (6149439256685913 / 10000000000 : ℝ) ≤ Real.exp (3332321591216437 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3332321591216437 / 250000000000000 : ℝ) (1516704969971 /
    1000000000000 : ℝ) (6149439256685913 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1178_product_lower :
    (3424430966216437 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (589 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1178_leftExp
    (by norm_num : (0 : ℝ) ≤ (8720243663 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1178_product_upper :
    Real.pi * Real.exp (1179 / 800 : ℝ) ≤ (68574305459255687 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1178_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1178_endpointLower :
    (21360103 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (589 / 800 : ℝ) (1179 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3424430966216437 / 250000000000000 : ℝ) (Real.pi * Real.exp (589 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1178_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1179 / 800 : ℝ) - (589 / 1600 : ℝ)) ≤
      (6257686992995297 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1178_denomUpper
    linarith [hpThetaJensenCell1178_product_upper]
  have hi : (1 / (6257686992995297 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1179 / 800 : ℝ) - (589 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6257686992995297 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6257686992995297 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((589 / 1600 : ℝ) - Real.pi * Real.exp (1179 / 800 : ℝ)) := by
    rw [show (589 / 1600 : ℝ) - Real.pi * Real.exp (1179 / 800 : ℝ) =
      -(Real.pi * Real.exp (1179 / 800 : ℝ) - (589 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (589 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (589 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1178_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6257686992995297 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1178_endpointUpper :
    hpThetaJensenKernelEndpointUpper (589 / 800 : ℝ) (1179 / 1600 : ℝ) ≤ (5462817 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1179 / 800 : ℝ)) (68574305459255687 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1179 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1178_product_upper
  have hD : (6149439256685913 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (589 / 400 : ℝ) - (1179 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1178_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1178_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (589 / 400 : ℝ) - (1179 / 3200 : ℝ)) ≤
      (1 / (6149439256685913 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6149439256685913 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1179 / 3200 : ℝ) - Real.pi * Real.exp (589 / 400 : ℝ)) ≤
      (2 / (6149439256685913 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1179 / 3200 : ℝ) - Real.pi * Real.exp (589 / 400 : ℝ) =
      -(Real.pi * Real.exp (589 / 400 : ℝ) - (1179 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68574305459255687 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (68574305459255687 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1178_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (589 / 800 : ℝ) (1179 / 1600 : ℝ)) :
    (21360103 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5462817 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1178_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1178_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1179_leftExp :
    (8731150783 / 2000000000 : ℝ) ≤ Real.exp (1179 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1179 / 800 : ℝ) (261782918601 / 250000000000 : ℝ)
    (8731150783 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1179_rightExp :
    Real.exp (59 / 40 : ℝ) ≤ (4371035773 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 40 : ℝ) (209434515757 / 200000000000 : ℝ)
    (4371035773 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1179_denomUpper :
    Real.exp (13363577887206389 / 1000000000000000 : ℝ) ≤ (6363970164242023 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (13363577887206389 / 1000000000000000 : ℝ) (75916557873 /
    50000000000 : ℝ) (6363970164242023 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1179_denomLower :
    (6253749853184457 / 10000000000 : ℝ) ≤ Real.exp (3336526681333317 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3336526681333317 / 250000000000000 : ℝ) (151750241467 /
    100000000000 : ℝ) (6253749853184457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1179_product_lower :
    (3428714181333317 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1179 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1179_leftExp
    (by norm_num : (0 : ℝ) ≤ (8731150783 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1179_product_upper :
    Real.pi * Real.exp (59 / 40 : ℝ) ≤ (13732015387206389 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1179_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1179_endpointLower :
    (10529591 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1179 / 1600 : ℝ) (59 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3428714181333317 / 250000000000000 : ℝ) (Real.pi * Real.exp (1179 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1179_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 40 : ℝ) - (1179 / 3200 : ℝ)) ≤
      (6363970164242023 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1179_denomUpper
    linarith [hpThetaJensenCell1179_product_upper]
  have hi : (1 / (6363970164242023 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 40 : ℝ) - (1179 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6363970164242023 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6363970164242023 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1179 / 3200 : ℝ) - Real.pi * Real.exp (59 / 40 : ℝ)) := by
    rw [show (1179 / 3200 : ℝ) - Real.pi * Real.exp (59 / 40 : ℝ) =
      -(Real.pi * Real.exp (59 / 40 : ℝ) - (1179 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1179 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1179 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1179_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6363970164242023 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1179_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1179 / 1600 : ℝ) (59 / 80 : ℝ) ≤ (4308777 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 40 : ℝ)) (13732015387206389 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1179_product_upper
  have hD : (6253749853184457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1179 / 800 : ℝ) - (59 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1179_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1179_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1179 / 800 : ℝ) - (59 / 160 : ℝ)) ≤
      (1 / (6253749853184457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6253749853184457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 160 : ℝ) - Real.pi * Real.exp (1179 / 800 : ℝ)) ≤
      (2 / (6253749853184457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (59 / 160 : ℝ) - Real.pi * Real.exp (1179 / 800 : ℝ) =
      -(Real.pi * Real.exp (1179 / 800 : ℝ) - (59 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13732015387206389 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (13732015387206389 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1179_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1179 / 1600 : ℝ) (59 / 80 : ℝ)) :
    (10529591 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4308777 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1179_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1179_endpointUpper

def hpThetaJensenCellsBatch058Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (27473897 / 10000000000 : ℝ)
  | 1 => (27097291 / 10000000000 : ℝ)
  | 2 => (26725281 / 10000000000 : ℝ)
  | 3 => (26357819 / 10000000000 : ℝ)
  | 4 => (3249357 / 1250000000 : ℝ)
  | 5 => (25636347 / 10000000000 : ℝ)
  | 6 => (25282243 / 10000000000 : ℝ)
  | 7 => (12466249 / 5000000000 : ℝ)
  | 8 => (24587067 / 10000000000 : ℝ)
  | 9 => (24245903 / 10000000000 : ℝ)
  | 10 => (23908961 / 10000000000 : ℝ)
  | 11 => (5894049 / 2500000000 : ℝ)
  | 12 => (5811891 / 2500000000 : ℝ)
  | 13 => (22923019 / 10000000000 : ℝ)
  | 14 => (565063 / 250000000 : ℝ)
  | 15 => (22286021 / 10000000000 : ℝ)
  | 16 => (21973481 / 10000000000 : ℝ)
  | 17 => (4332971 / 2000000000 : ℝ)
  | 18 => (21360103 / 10000000000 : ℝ)
  | 19 => (10529591 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch058Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (14047521 / 5000000000 : ℝ)
  | 1 => (865953 / 312500000 : ℝ)
  | 2 => (5466127 / 2000000000 : ℝ)
  | 3 => (2695541 / 1000000000 : ℝ)
  | 4 => (6646193 / 2500000000 : ℝ)
  | 5 => (26218673 / 10000000000 : ℝ)
  | 6 => (5171413 / 2000000000 : ℝ)
  | 7 => (12749951 / 5000000000 : ℝ)
  | 8 => (5029427 / 2000000000 : ℝ)
  | 9 => (24798719 / 10000000000 : ℝ)
  | 10 => (1528413 / 625000000 : ℝ)
  | 11 => (4822951 / 2000000000 : ℝ)
  | 12 => (5944779 / 2500000000 : ℝ)
  | 13 => (4689529 / 2000000000 : ℝ)
  | 14 => (11560149 / 5000000000 : ℝ)
  | 15 => (2279703 / 1000000000 : ℝ)
  | 16 => (11238899 / 5000000000 : ℝ)
  | 17 => (22162559 / 10000000000 : ℝ)
  | 18 => (5462817 / 2500000000 : ℝ)
  | 19 => (4308777 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch058_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch058Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch058Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1160_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1161_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1162_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1163_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1164_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1165_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1166_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1167_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1168_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1169_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1170_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1171_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1172_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1173_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1174_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1175_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1176_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1177_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1178_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1179_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper] at h ⊢
    exact h

end HodgeProofHP
