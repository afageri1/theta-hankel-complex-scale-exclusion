import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1180_leftExp :
    (1365948679 / 312500000 : ℝ) ≤ Real.exp (59 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 40 : ℝ) (32724143087 / 31250000000 : ℝ) (1365948679
    / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1180_rightExp :
    Real.exp (1181 / 800 : ℝ) ≤ (43765029841 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1181 / 800 : ℝ) (1047213484763 / 1000000000000 : ℝ)
    (43765029841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1180_denomUpper :
    Real.exp (133804411393276713 / 10000000000000000 : ℝ) ≤ (3236098682073221 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (133804411393276713 / 10000000000000000 : ℝ)
    (303826298671 / 200000000000 : ℝ) (3236098682073221 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1180_denomLower :
    (1589991530434501 / 2500000000 : ℝ) ≤ Real.exp (521990176388371 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (521990176388371 / 39062500000000 : ℝ) (1518301295421 /
    1000000000000 : ℝ) (1589991530434501 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1180_product_lower :
    (536406680294621 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (59 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1180_leftExp
    (by norm_num : (0 : ℝ) ≤ (1365948679 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1180_product_upper :
    Real.pi * Real.exp (1181 / 800 : ℝ) ≤ (137491911393276713 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1180_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1180_endpointLower :
    (415241 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 80 : ℝ) (1181 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (536406680294621 / 39062500000000 : ℝ) (Real.pi * Real.exp (59 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1180_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1181 / 800 : ℝ) - (59 / 160 : ℝ)) ≤
      (3236098682073221 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1180_denomUpper
    linarith [hpThetaJensenCell1180_product_upper]
  have hi : (1 / (3236098682073221 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1181 / 800 : ℝ) - (59 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3236098682073221 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3236098682073221 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 160 : ℝ) - Real.pi * Real.exp (1181 / 800 : ℝ)) := by
    rw [show (59 / 160 : ℝ) - Real.pi * Real.exp (1181 / 800 : ℝ) =
      -(Real.pi * Real.exp (1181 / 800 : ℝ) - (59 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1180_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3236098682073221 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1180_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 80 : ℝ) (1181 / 1600 : ℝ) ≤ (4248073 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1181 / 800 : ℝ)) (137491911393276713 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1181 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1180_product_upper
  have hD : (1589991530434501 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 40 : ℝ) - (1181 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1180_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1180_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 40 : ℝ) - (1181 / 3200 : ℝ)) ≤
      (1 / (1589991530434501 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1589991530434501 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1181 / 3200 : ℝ) - Real.pi * Real.exp (59 / 40 : ℝ)) ≤
      (2 / (1589991530434501 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1181 / 3200 : ℝ) - Real.pi * Real.exp (59 / 40 : ℝ) =
      -(Real.pi * Real.exp (59 / 40 : ℝ) - (1181 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (137491911393276713 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (137491911393276713 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1180_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 80 : ℝ) (1181 / 1600 : ℝ)) :
    (415241 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4248073 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1180_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1180_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1181_leftExp :
    (21882514919 / 5000000000 : ℝ) ≤ Real.exp (1181 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1181 / 800 : ℝ) (523606742381 / 500000000000 : ℝ)
    (21882514919 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1181_rightExp :
    Real.exp (591 / 400 : ℝ) ≤ (21909885167 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (591 / 400 : ℝ) (1047254392339 / 1000000000000 : ℝ)
    (21909885167 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1181_denomUpper :
    Real.exp (66986629371451031 / 5000000000000000 : ℝ) ≤ (3291203254546483 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (66986629371451031 / 5000000000000000 : ℝ) (151993327151
    / 100000000000 : ℝ) (3291203254546483 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1181_denomLower :
    (3234062595284669 / 5000000000 : ℝ) ≤ Real.exp (8362382351176381 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8362382351176381 / 625000000000000 : ℝ) (1519101615301 /
    1000000000000 : ℝ) (3234062595284669 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1181_product_lower :
    (8593241726176381 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1181 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1181_leftExp
    (by norm_num : (0 : ℝ) ≤ (21882514919 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1181_product_upper :
    Real.pi * Real.exp (591 / 400 : ℝ) ≤ (68831941871451031 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1181_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1181_endpointLower :
    (10234333 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1181 / 1600 : ℝ) (591 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8593241726176381 / 625000000000000 : ℝ) (Real.pi * Real.exp (1181 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1181_product_lower
  have hD : Real.exp (Real.pi * Real.exp (591 / 400 : ℝ) - (1181 / 3200 : ℝ)) ≤
      (3291203254546483 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1181_denomUpper
    linarith [hpThetaJensenCell1181_product_upper]
  have hi : (1 / (3291203254546483 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (591 / 400 : ℝ) - (1181 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3291203254546483 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3291203254546483 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1181 / 3200 : ℝ) - Real.pi * Real.exp (591 / 400 : ℝ)) := by
    rw [show (1181 / 3200 : ℝ) - Real.pi * Real.exp (591 / 400 : ℝ) =
      -(Real.pi * Real.exp (591 / 400 : ℝ) - (1181 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1181 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1181 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1181_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3291203254546483 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1181_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1181 / 1600 : ℝ) (591 / 800 : ℝ) ≤ (5235167 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (591 / 400 : ℝ)) (68831941871451031 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (591 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1181_product_upper
  have hD : (3234062595284669 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1181 / 800 : ℝ) - (591 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1181_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1181_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1181 / 800 : ℝ) - (591 / 1600 : ℝ)) ≤
      (1 / (3234062595284669 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3234062595284669 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((591 / 1600 : ℝ) - Real.pi * Real.exp (1181 / 800 : ℝ)) ≤
      (2 / (3234062595284669 / 5000000000 : ℝ) : ℝ) := by
    rw [show (591 / 1600 : ℝ) - Real.pi * Real.exp (1181 / 800 : ℝ) =
      -(Real.pi * Real.exp (1181 / 800 : ℝ) - (591 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (68831941871451031 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (68831941871451031 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1181_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1181 / 1600 : ℝ) (591 / 800 : ℝ)) :
    (10234333 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5235167 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1181_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1181_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1182_leftExp :
    (10954942583 / 2500000000 : ℝ) ≤ Real.exp (591 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (591 / 400 : ℝ) (523627196169 / 500000000000 : ℝ)
    (10954942583 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1182_rightExp :
    Real.exp (1183 / 800 : ℝ) ≤ (8774915859 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1183 / 800 : ℝ) (130911912689 / 125000000000 : ℝ)
    (8774915859 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1182_denomUpper :
    Real.exp (26828464238223387 / 2000000000000000 : ℝ) ≤ (6694636304132473 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (26828464238223387 / 2000000000000000 : ℝ) (760368247523
    / 500000000000 : ℝ) (6694636304132473 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1182_denomLower :
    (1315652992030251 / 2000000000 : ℝ) ≤ Real.exp (4186467653651517 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4186467653651517 / 312500000000000 : ℝ) (1519903377441 /
    1000000000000 : ℝ) (1315652992030251 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1182_product_lower :
    (4301994997401517 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (591 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1182_leftExp
    (by norm_num : (0 : ℝ) ≤ (10954942583 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1182_product_upper :
    Real.pi * Real.exp (1183 / 800 : ℝ) ≤ (27567214238223387 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1182_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1182_endpointLower :
    (2017899 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (591 / 800 : ℝ) (1183 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4301994997401517 / 312500000000000 : ℝ) (Real.pi * Real.exp (591 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1182_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1183 / 800 : ℝ) - (591 / 1600 : ℝ)) ≤
      (6694636304132473 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1182_denomUpper
    linarith [hpThetaJensenCell1182_product_upper]
  have hi : (1 / (6694636304132473 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1183 / 800 : ℝ) - (591 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6694636304132473 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6694636304132473 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((591 / 1600 : ℝ) - Real.pi * Real.exp (1183 / 800 : ℝ)) := by
    rw [show (591 / 1600 : ℝ) - Real.pi * Real.exp (1183 / 800 : ℝ) =
      -(Real.pi * Real.exp (1183 / 800 : ℝ) - (591 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (591 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (591 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1182_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6694636304132473 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1182_endpointUpper :
    hpThetaJensenKernelEndpointUpper (591 / 800 : ℝ) (1183 / 1600 : ℝ) ≤ (1290297 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1183 / 800 : ℝ)) (27567214238223387 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1183 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1182_product_upper
  have hD : (1315652992030251 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (591 / 400 : ℝ) - (1183 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1182_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1182_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (591 / 400 : ℝ) - (1183 / 3200 : ℝ)) ≤
      (1 / (1315652992030251 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1315652992030251 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1183 / 3200 : ℝ) - Real.pi * Real.exp (591 / 400 : ℝ)) ≤
      (2 / (1315652992030251 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1183 / 3200 : ℝ) - Real.pi * Real.exp (591 / 400 : ℝ) =
      -(Real.pi * Real.exp (591 / 400 : ℝ) - (1183 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (27567214238223387 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (27567214238223387 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1182_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (591 / 800 : ℝ) (1183 / 1600 : ℝ)) :
    (2017899 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1290297 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1182_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1182_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1183_leftExp :
    (10968644823 / 2500000000 : ℝ) ≤ Real.exp (1183 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1183 / 800 : ℝ) (1047295301511 / 1000000000000 : ℝ)
    (10968644823 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1183_rightExp :
    Real.exp (37 / 25 : ℝ) ≤ (4392945681 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 25 : ℝ) (261834053071 / 250000000000 : ℝ)
    (4392945681 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1183_denomUpper :
    Real.exp (13431159900809833 / 1000000000000000 : ℝ) ≤ (6808926254459803 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (13431159900809833 / 1000000000000000 : ℝ) (1521541167091
    / 1000000000000 : ℝ) (6808926254459803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1183_denomLower :
    (6690424103187227 / 10000000000 : ℝ) ≤ Real.exp (4191750853347277 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4191750853347277 / 312500000000000 : ℝ) (190088323113 /
    125000000000 : ℝ) (6690424103187227 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1183_product_lower :
    (4307375853347277 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1183 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1183_leftExp
    (by norm_num : (0 : ℝ) ≤ (10968644823 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1183_product_upper :
    Real.pi * Real.exp (37 / 25 : ℝ) ≤ (13800847400809833 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1183_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1183_endpointLower :
    (994649 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1183 / 1600 : ℝ) (37 / 50 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4307375853347277 / 312500000000000 : ℝ) (Real.pi * Real.exp (1183 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1183_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 25 : ℝ) - (1183 / 3200 : ℝ)) ≤
      (6808926254459803 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1183_denomUpper
    linarith [hpThetaJensenCell1183_product_upper]
  have hi : (1 / (6808926254459803 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 25 : ℝ) - (1183 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (6808926254459803 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (6808926254459803 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1183 / 3200 : ℝ) - Real.pi * Real.exp (37 / 25 : ℝ)) := by
    rw [show (1183 / 3200 : ℝ) - Real.pi * Real.exp (37 / 25 : ℝ) =
      -(Real.pi * Real.exp (37 / 25 : ℝ) - (1183 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1183 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1183 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1183_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (6808926254459803 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1183_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1183 / 1600 : ℝ) (37 / 50 : ℝ) ≤ (814103 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 25 : ℝ)) (13800847400809833 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 50 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1183_product_upper
  have hD : (6690424103187227 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1183 / 800 : ℝ) - (37 / 100 : ℝ)) := by
    apply le_trans hpThetaJensenCell1183_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1183_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1183 / 800 : ℝ) - (37 / 100 : ℝ)) ≤
      (1 / (6690424103187227 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6690424103187227 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 100 : ℝ) - Real.pi * Real.exp (1183 / 800 : ℝ)) ≤
      (2 / (6690424103187227 / 10000000000 : ℝ) : ℝ) := by
    rw [show (37 / 100 : ℝ) - Real.pi * Real.exp (1183 / 800 : ℝ) =
      -(Real.pi * Real.exp (1183 / 800 : ℝ) - (37 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13800847400809833 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (13800847400809833 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1183_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1183 / 1600 : ℝ) (37 / 50 : ℝ)) :
    (994649 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (814103 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1183_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1183_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1184_leftExp :
    (5491182101 / 1250000000 : ℝ) ≤ Real.exp (37 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 25 : ℝ) (1047336212283 / 1000000000000 : ℝ)
    (5491182101 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1184_rightExp :
    Real.exp (237 / 160 : ℝ) ≤ (21992201483 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (237 / 160 : ℝ) (523688562327 / 500000000000 : ℝ)
    (21992201483 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1184_denomUpper :
    Real.exp (67240546233582419 / 5000000000000000 : ℝ) ≤ (3462658342647729 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (67240546233582419 / 5000000000000000 : ℝ) (1522347290797
    / 1000000000000 : ℝ) (3462658342647729 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1184_denomLower :
    (6804642108232173 / 10000000000 : ℝ) ≤ Real.exp (2098520391755599 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2098520391755599 / 156250000000000 : ℝ) (1521511240877 /
    1000000000000 : ℝ) (6804642108232173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1184_product_lower :
    (2156381719880599 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1184_leftExp
    (by norm_num : (0 : ℝ) ≤ (5491182101 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1184_product_upper :
    Real.pi * Real.exp (237 / 160 : ℝ) ≤ (69090546233582419 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1184_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1184_endpointLower :
    (9805299 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 50 : ℝ) (237 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2156381719880599 / 156250000000000 : ℝ) (Real.pi * Real.exp (37 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1184_product_lower
  have hD : Real.exp (Real.pi * Real.exp (237 / 160 : ℝ) - (37 / 100 : ℝ)) ≤
      (3462658342647729 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1184_denomUpper
    linarith [hpThetaJensenCell1184_product_upper]
  have hi : (1 / (3462658342647729 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (237 / 160 : ℝ) - (37 / 100 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3462658342647729 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3462658342647729 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 100 : ℝ) - Real.pi * Real.exp (237 / 160 : ℝ)) := by
    rw [show (37 / 100 : ℝ) - Real.pi * Real.exp (237 / 160 : ℝ) =
      -(Real.pi * Real.exp (237 / 160 : ℝ) - (37 / 100 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1184_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3462658342647729 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1184_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 50 : ℝ) (237 / 320 : ℝ) ≤ (627003 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (237 / 160 : ℝ)) (69090546233582419 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (237 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1184_product_upper
  have hD : (6804642108232173 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 25 : ℝ) - (237 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1184_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1184_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 25 : ℝ) - (237 / 640 : ℝ)) ≤
      (1 / (6804642108232173 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6804642108232173 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((237 / 640 : ℝ) - Real.pi * Real.exp (37 / 25 : ℝ)) ≤
      (2 / (6804642108232173 / 10000000000 : ℝ) : ℝ) := by
    rw [show (237 / 640 : ℝ) - Real.pi * Real.exp (37 / 25 : ℝ) =
      -(Real.pi * Real.exp (37 / 25 : ℝ) - (237 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (69090546233582419 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (69090546233582419 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1184_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 50 : ℝ) (237 / 320 : ℝ)) :
    (9805299 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (627003 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1184_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1184_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1185_leftExp :
    (43984402963 / 10000000000 : ℝ) ≤ Real.exp (237 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (237 / 160 : ℝ) (1047377124653 / 1000000000000 : ℝ)
    (43984402963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1185_rightExp :
    Real.exp (593 / 400 : ℝ) ≤ (44039417847 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (593 / 400 : ℝ) (523709019311 / 500000000000 : ℝ)
    (44039417847 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1185_denomUpper :
    Real.exp (134650801832210271 / 10000000000000000 : ℝ) ≤ (7043848750275273 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (134650801832210271 / 10000000000000000 : ℝ) (60926194771
    / 40000000000 : ℝ) (7043848750275273 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1185_denomLower :
    (1730239816647493 / 2500000000 : ℝ) ≤ Real.exp (16809349809167137 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16809349809167137 / 1250000000000000 : ℝ) (380579337113
    / 250000000000 : ℝ) (1730239816647493 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1185_product_lower :
    (17272631059167137 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (237 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1185_leftExp
    (by norm_num : (0 : ℝ) ≤ (43984402963 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1185_product_upper :
    Real.pi * Real.exp (593 / 400 : ℝ) ≤ (138353926832210271 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1185_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1185_endpointLower :
    (9665901 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (237 / 320 : ℝ) (593 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17272631059167137 / 1250000000000000 : ℝ) (Real.pi * Real.exp (237 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1185_product_lower
  have hD : Real.exp (Real.pi * Real.exp (593 / 400 : ℝ) - (237 / 640 : ℝ)) ≤
      (7043848750275273 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1185_denomUpper
    linarith [hpThetaJensenCell1185_product_upper]
  have hi : (1 / (7043848750275273 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (593 / 400 : ℝ) - (237 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7043848750275273 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7043848750275273 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((237 / 640 : ℝ) - Real.pi * Real.exp (593 / 400 : ℝ)) := by
    rw [show (237 / 640 : ℝ) - Real.pi * Real.exp (593 / 400 : ℝ) =
      -(Real.pi * Real.exp (593 / 400 : ℝ) - (237 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (237 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (237 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1185_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7043848750275273 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1185_endpointUpper :
    hpThetaJensenKernelEndpointUpper (237 / 320 : ℝ) (593 / 800 : ℝ) ≤ (4944819 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (593 / 400 : ℝ)) (138353926832210271 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (593 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1185_product_upper
  have hD : (1730239816647493 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (237 / 160 : ℝ) - (593 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1185_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1185_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (237 / 160 : ℝ) - (593 / 1600 : ℝ)) ≤
      (1 / (1730239816647493 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1730239816647493 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((593 / 1600 : ℝ) - Real.pi * Real.exp (237 / 160 : ℝ)) ≤
      (2 / (1730239816647493 / 2500000000 : ℝ) : ℝ) := by
    rw [show (593 / 1600 : ℝ) - Real.pi * Real.exp (237 / 160 : ℝ) =
      -(Real.pi * Real.exp (237 / 160 : ℝ) - (593 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (138353926832210271 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (138353926832210271 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1185_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (237 / 320 : ℝ) (593 / 800 : ℝ)) :
    (9665901 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4944819 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1185_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1185_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1186_leftExp :
    (11009854461 / 2500000000 : ℝ) ≤ Real.exp (593 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (593 / 400 : ℝ) (1047418038621 / 1000000000000 : ℝ)
    (11009854461 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1186_rightExp :
    Real.exp (1187 / 800 : ℝ) ≤ (44094501539 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1187 / 800 : ℝ) (261864738547 / 250000000000 : ℝ)
    (44094501539 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1186_denomUpper :
    Real.exp (134820727373411627 / 10000000000000000 : ℝ) ≤ (1791141115203043 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (134820727373411627 / 10000000000000000 : ℝ)
    (1523963905673 / 1000000000000 : ℝ) (1791141115203043 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1186_denomLower :
    (281576668484801 / 400000000 : ℝ) ≤ Real.exp (4207640868230239 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4207640868230239 / 312500000000000 : ℝ) (1523124910783 /
    1000000000000 : ℝ) (281576668484801 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1186_product_lower :
    (4323558836980239 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (593 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1186_leftExp
    (by norm_num : (0 : ℝ) ≤ (11009854461 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1186_product_upper :
    Real.pi * Real.exp (1187 / 800 : ℝ) ≤ (138526977373411627 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1186_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1186_endpointLower :
    (19056553 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (593 / 800 : ℝ) (1187 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4323558836980239 / 312500000000000 : ℝ) (Real.pi * Real.exp (593 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1186_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1187 / 800 : ℝ) - (593 / 1600 : ℝ)) ≤
      (1791141115203043 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1186_denomUpper
    linarith [hpThetaJensenCell1186_product_upper]
  have hi : (1 / (1791141115203043 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1187 / 800 : ℝ) - (593 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1791141115203043 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1791141115203043 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((593 / 1600 : ℝ) - Real.pi * Real.exp (1187 / 800 : ℝ)) := by
    rw [show (593 / 1600 : ℝ) - Real.pi * Real.exp (1187 / 800 : ℝ) =
      -(Real.pi * Real.exp (1187 / 800 : ℝ) - (593 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (593 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (593 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1186_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1791141115203043 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1186_endpointUpper :
    hpThetaJensenKernelEndpointUpper (593 / 800 : ℝ) (1187 / 1600 : ℝ) ≤ (9749037 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1187 / 800 : ℝ)) (138526977373411627 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1187 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1186_product_upper
  have hD : (281576668484801 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (593 / 400 : ℝ) - (1187 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1186_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1186_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (593 / 400 : ℝ) - (1187 / 3200 : ℝ)) ≤
      (1 / (281576668484801 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (281576668484801 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1187 / 3200 : ℝ) - Real.pi * Real.exp (593 / 400 : ℝ)) ≤
      (2 / (281576668484801 / 400000000 : ℝ) : ℝ) := by
    rw [show (1187 / 3200 : ℝ) - Real.pi * Real.exp (593 / 400 : ℝ) =
      -(Real.pi * Real.exp (593 / 400 : ℝ) - (1187 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (138526977373411627 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (138526977373411627 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1186_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (593 / 800 : ℝ) (1187 / 1600 : ℝ)) :
    (19056553 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9749037 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1186_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1186_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1187_leftExp :
    (1377953173 / 312500000 : ℝ) ≤ Real.exp (1187 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1187 / 800 : ℝ) (1047458954187 / 1000000000000 : ℝ)
    (1377953173 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1187_rightExp :
    Real.exp (297 / 200 : ℝ) ≤ (44149654129 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (297 / 200 : ℝ) (1047499871353 / 1000000000000 : ℝ)
    (44149654129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1187_denomUpper :
    Real.exp (134990869364087497 / 10000000000000000 : ℝ) ≤ (291500268111551 / 400000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (134990869364087497 / 10000000000000000 : ℝ)
    (1524774403161 / 1000000000000 : ℝ) (291500268111551 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1187_denomLower :
    (447503526754011 / 625000000 : ℝ) ≤ Real.exp (526618879958927 / 39062500000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (526618879958927 / 39062500000000 : ℝ) (761966965503 /
    500000000000 : ℝ) (447503526754011 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1187_product_lower :
    (541120833083927 / 39062500000000 : ℝ) ≤ Real.pi * Real.exp (1187 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1187_leftExp
    (by norm_num : (0 : ℝ) ≤ (1377953173 / 312500000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1187_product_upper :
    Real.pi * Real.exp (297 / 200 : ℝ) ≤ (138700244364087497 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1187_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1187_endpointLower :
    (9392407 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1187 / 1600 : ℝ) (297 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (541120833083927 / 39062500000000 : ℝ) (Real.pi * Real.exp (1187 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1187_product_lower
  have hD : Real.exp (Real.pi * Real.exp (297 / 200 : ℝ) - (1187 / 3200 : ℝ)) ≤
      (291500268111551 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1187_denomUpper
    linarith [hpThetaJensenCell1187_product_upper]
  have hi : (1 / (291500268111551 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (297 / 200 : ℝ) - (1187 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (291500268111551 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (291500268111551 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1187 / 3200 : ℝ) - Real.pi * Real.exp (297 / 200 : ℝ)) := by
    rw [show (1187 / 3200 : ℝ) - Real.pi * Real.exp (297 / 200 : ℝ) =
      -(Real.pi * Real.exp (297 / 200 : ℝ) - (1187 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1187 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1187 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1187_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (291500268111551 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1187_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1187 / 1600 : ℝ) (297 / 400 : ℝ) ≤ (384409 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (297 / 200 : ℝ)) (138700244364087497 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (297 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1187_product_upper
  have hD : (447503526754011 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1187 / 800 : ℝ) - (297 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1187_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1187_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1187 / 800 : ℝ) - (297 / 800 : ℝ)) ≤
      (1 / (447503526754011 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (447503526754011 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((297 / 800 : ℝ) - Real.pi * Real.exp (1187 / 800 : ℝ)) ≤
      (2 / (447503526754011 / 625000000 : ℝ) : ℝ) := by
    rw [show (297 / 800 : ℝ) - Real.pi * Real.exp (1187 / 800 : ℝ) =
      -(Real.pi * Real.exp (1187 / 800 : ℝ) - (297 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (138700244364087497 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (138700244364087497 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1187_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1187 / 1600 : ℝ) (297 / 400 : ℝ)) :
    (9392407 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (384409 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1187_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1187_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1188_leftExp :
    (44149654127 / 10000000000 : ℝ) ≤ Real.exp (297 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (297 / 200 : ℝ) (130937483919 / 125000000000 : ℝ)
    (44149654127 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1188_rightExp :
    Real.exp (1189 / 800 : ℝ) ≤ (44204875703 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1189 / 800 : ℝ) (261885197529 / 250000000000 : ℝ)
    (44204875703 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1188_denomUpper :
    Real.exp (135161228074414879 / 10000000000000000 : ℝ) ≤ (1482543850257869 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (135161228074414879 / 10000000000000000 : ℝ)
    (762793182451 / 500000000000 : ℝ) (1482543850257869 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1188_denomLower :
    (1456584255118761 / 2000000000 : ℝ) ≤ Real.exp (16873071901018773 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16873071901018773 / 1250000000000000 : ℝ) (762372206153
    / 500000000000 : ℝ) (1456584255118761 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1188_product_lower :
    (17337525026018773 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (297 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1188_leftExp
    (by norm_num : (0 : ℝ) ≤ (44149654127 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1188_product_upper :
    Real.pi * Real.exp (1189 / 800 : ℝ) ≤ (138873728074414879 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1188_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1188_endpointLower :
    (18516543 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (297 / 400 : ℝ) (1189 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17337525026018773 / 1250000000000000 : ℝ) (Real.pi * Real.exp (297 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1188_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1189 / 800 : ℝ) - (297 / 800 : ℝ)) ≤
      (1482543850257869 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1188_denomUpper
    linarith [hpThetaJensenCell1188_product_upper]
  have hi : (1 / (1482543850257869 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1189 / 800 : ℝ) - (297 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1482543850257869 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1482543850257869 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((297 / 800 : ℝ) - Real.pi * Real.exp (1189 / 800 : ℝ)) := by
    rw [show (297 / 800 : ℝ) - Real.pi * Real.exp (1189 / 800 : ℝ) =
      -(Real.pi * Real.exp (1189 / 800 : ℝ) - (297 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (297 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (297 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1188_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1482543850257869 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1188_endpointUpper :
    hpThetaJensenKernelEndpointUpper (297 / 400 : ℝ) (1189 / 1600 : ℝ) ≤ (3789273 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1189 / 800 : ℝ)) (138873728074414879 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1189 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1188_product_upper
  have hD : (1456584255118761 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (297 / 200 : ℝ) - (1189 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1188_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1188_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (297 / 200 : ℝ) - (1189 / 3200 : ℝ)) ≤
      (1 / (1456584255118761 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1456584255118761 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1189 / 3200 : ℝ) - Real.pi * Real.exp (297 / 200 : ℝ)) ≤
      (2 / (1456584255118761 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1189 / 3200 : ℝ) - Real.pi * Real.exp (297 / 200 : ℝ) =
      -(Real.pi * Real.exp (297 / 200 : ℝ) - (1189 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (138873728074414879 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (138873728074414879 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1188_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (297 / 400 : ℝ) (1189 / 1600 : ℝ)) :
    (18516543 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3789273 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1188_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1188_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1189_leftExp :
    (44204875701 / 10000000000 : ℝ) ≤ Real.exp (1189 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1189 / 800 : ℝ) (209508158023 / 200000000000 : ℝ)
    (44204875701 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1189_rightExp :
    Real.exp (119 / 80 : ℝ) ≤ (44260166347 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (119 / 80 : ℝ) (1047581710477 / 1000000000000 : ℝ)
    (44260166347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1189_denomUpper :
    Real.exp (135331803774570771 / 10000000000000000 : ℝ) ≤ (754024679180803 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (135331803774570771 / 10000000000000000 : ℝ) (95399987129
    / 62500000000 : ℝ) (754024679180803 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1189_denomLower :
    (3704027498608097 / 5000000000 : ℝ) ≤ Real.exp (16894366732906999 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16894366732906999 / 1250000000000000 : ℝ) (1525556357813
    / 1000000000000 : ℝ) (3704027498608097 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1189_product_lower :
    (17359210482906999 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1189 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1189_leftExp
    (by norm_num : (0 : ℝ) ≤ (44204875701 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1189_product_upper :
    Real.pi * Real.exp (119 / 80 : ℝ) ≤ (139047428774570771 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1189_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1189_endpointLower :
    (2281463 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1189 / 1600 : ℝ) (119 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17359210482906999 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1189 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1189_product_lower
  have hD : Real.exp (Real.pi * Real.exp (119 / 80 : ℝ) - (1189 / 3200 : ℝ)) ≤
      (754024679180803 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1189_denomUpper
    linarith [hpThetaJensenCell1189_product_upper]
  have hi : (1 / (754024679180803 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (119 / 80 : ℝ) - (1189 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (754024679180803 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (754024679180803 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1189 / 3200 : ℝ) - Real.pi * Real.exp (119 / 80 : ℝ)) := by
    rw [show (1189 / 3200 : ℝ) - Real.pi * Real.exp (119 / 80 : ℝ) =
      -(Real.pi * Real.exp (119 / 80 : ℝ) - (1189 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1189 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1189 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1189_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (754024679180803 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1189_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1189 / 1600 : ℝ) (119 / 160 : ℝ) ≤ (933789 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (119 / 80 : ℝ)) (139047428774570771 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (119 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1189_product_upper
  have hD : (3704027498608097 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1189 / 800 : ℝ) - (119 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1189_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1189_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1189 / 800 : ℝ) - (119 / 320 : ℝ)) ≤
      (1 / (3704027498608097 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3704027498608097 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((119 / 320 : ℝ) - Real.pi * Real.exp (1189 / 800 : ℝ)) ≤
      (2 / (3704027498608097 / 5000000000 : ℝ) : ℝ) := by
    rw [show (119 / 320 : ℝ) - Real.pi * Real.exp (1189 / 800 : ℝ) =
      -(Real.pi * Real.exp (1189 / 800 : ℝ) - (119 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (139047428774570771 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (139047428774570771 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1189_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1189 / 1600 : ℝ) (119 / 160 : ℝ)) :
    (2281463 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (933789 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1189_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1189_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1190_leftExp :
    (8852033269 / 2000000000 : ℝ) ≤ Real.exp (119 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (119 / 80 : ℝ) (261895427619 / 250000000000 : ℝ)
    (8852033269 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1190_rightExp :
    Real.exp (1191 / 800 : ℝ) ≤ (11078881537 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1191 / 800 : ℝ) (1047622632437 / 1000000000000 : ℝ)
    (11078881537 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1190_denomUpper :
    Real.exp (33875649184468441 / 2500000000000000 : ℝ) ≤ (3835067471443541 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (33875649184468441 / 2500000000000000 : ℝ) (1527214693837
    / 1000000000000 : ℝ) (3835067471443541 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1190_denomLower :
    (1883875563169753 / 2500000000 : ℝ) ≤ Real.exp (3383137737703031 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3383137737703031 / 250000000000000 : ℝ) (1526369770711 /
    1000000000000 : ℝ) (1883875563169753 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1190_product_lower :
    (3476184612703031 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (119 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1190_leftExp
    (by norm_num : (0 : ℝ) ≤ (8852033269 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1190_product_upper :
    Real.pi * Real.exp (1191 / 800 : ℝ) ≤ (34805336684468441 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1190_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1190_endpointLower :
    (17990259 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (119 / 160 : ℝ) (1191 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3476184612703031 / 250000000000000 : ℝ) (Real.pi * Real.exp (119 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1190_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1191 / 800 : ℝ) - (119 / 320 : ℝ)) ≤
      (3835067471443541 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1190_denomUpper
    linarith [hpThetaJensenCell1190_product_upper]
  have hi : (1 / (3835067471443541 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1191 / 800 : ℝ) - (119 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3835067471443541 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3835067471443541 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((119 / 320 : ℝ) - Real.pi * Real.exp (1191 / 800 : ℝ)) := by
    rw [show (119 / 320 : ℝ) - Real.pi * Real.exp (1191 / 800 : ℝ) =
      -(Real.pi * Real.exp (1191 / 800 : ℝ) - (119 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (119 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (119 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1190_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3835067471443541 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1190_endpointUpper :
    hpThetaJensenKernelEndpointUpper (119 / 160 : ℝ) (1191 / 1600 : ℝ) ≤ (1150541 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1191 / 800 : ℝ)) (34805336684468441 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1191 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1190_product_upper
  have hD : (1883875563169753 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (119 / 80 : ℝ) - (1191 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1190_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1190_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (119 / 80 : ℝ) - (1191 / 3200 : ℝ)) ≤
      (1 / (1883875563169753 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1883875563169753 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1191 / 3200 : ℝ) - Real.pi * Real.exp (119 / 80 : ℝ)) ≤
      (2 / (1883875563169753 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1191 / 3200 : ℝ) - Real.pi * Real.exp (119 / 80 : ℝ) =
      -(Real.pi * Real.exp (119 / 80 : ℝ) - (1191 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34805336684468441 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (34805336684468441 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1190_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (119 / 160 : ℝ) (1191 / 1600 : ℝ)) :
    (17990259 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1150541 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1190_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1190_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1191_leftExp :
    (22157763073 / 5000000000 : ℝ) ≤ Real.exp (1191 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1191 / 800 : ℝ) (261905658109 / 250000000000 : ℝ)
    (22157763073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1191_rightExp :
    Real.exp (149 / 100 : ℝ) ≤ (44370955191 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (149 / 100 : ℝ) (209532711199 / 200000000000 : ℝ)
    (44370955191 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1191_denomUpper :
    Real.exp (135673607231359263 / 10000000000000000 : ℝ) ≤ (3901215134758453 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (135673607231359263 / 10000000000000000 : ℝ)
    (1528031067389 / 1000000000000 : ℝ) (3901215134758453 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1191_denomLower :
    (1916327158026517 / 2500000000 : ℝ) ≤ Real.exp (8468518901004027 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8468518901004027 / 625000000000000 : ℝ) (95449040887 /
    62500000000 : ℝ) (1916327158026517 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1191_product_lower :
    (8701331401004027 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1191 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1191_leftExp
    (by norm_num : (0 : ℝ) ≤ (22157763073 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1191_product_upper :
    Real.pi * Real.exp (149 / 100 : ℝ) ≤ (139395482231359263 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1191_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1191_endpointLower :
    (2216521 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1191 / 1600 : ℝ) (149 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8701331401004027 / 625000000000000 : ℝ) (Real.pi * Real.exp (1191 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1191_product_lower
  have hD : Real.exp (Real.pi * Real.exp (149 / 100 : ℝ) - (1191 / 3200 : ℝ)) ≤
      (3901215134758453 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1191_denomUpper
    linarith [hpThetaJensenCell1191_product_upper]
  have hi : (1 / (3901215134758453 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (149 / 100 : ℝ) - (1191 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3901215134758453 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3901215134758453 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1191 / 3200 : ℝ) - Real.pi * Real.exp (149 / 100 : ℝ)) := by
    rw [show (1191 / 3200 : ℝ) - Real.pi * Real.exp (149 / 100 : ℝ) =
      -(Real.pi * Real.exp (149 / 100 : ℝ) - (1191 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1191 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1191 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1191_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3901215134758453 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1191_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1191 / 1600 : ℝ) (149 / 200 : ℝ) ≤ (9072477 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (149 / 100 : ℝ)) (139395482231359263 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (149 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1191_product_upper
  have hD : (1916327158026517 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1191 / 800 : ℝ) - (149 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1191_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1191_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1191 / 800 : ℝ) - (149 / 400 : ℝ)) ≤
      (1 / (1916327158026517 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1916327158026517 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((149 / 400 : ℝ) - Real.pi * Real.exp (1191 / 800 : ℝ)) ≤
      (2 / (1916327158026517 / 2500000000 : ℝ) : ℝ) := by
    rw [show (149 / 400 : ℝ) - Real.pi * Real.exp (1191 / 800 : ℝ) =
      -(Real.pi * Real.exp (1191 / 800 : ℝ) - (149 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (139395482231359263 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (139395482231359263 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1191_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1191 / 1600 : ℝ) (149 / 200 : ℝ)) :
    (2216521 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9072477 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1191_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1191_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1192_leftExp :
    (44370955189 / 10000000000 : ℝ) ≤ Real.exp (149 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (149 / 100 : ℝ) (523831777997 / 500000000000 : ℝ)
    (44370955189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1192_rightExp :
    Real.exp (1193 / 800 : ℝ) ≤ (11106613391 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1193 / 800 : ℝ) (8185191259 / 7812500000 : ℝ)
    (11106613391 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1192_denomUpper :
    Real.exp (33961208882871863 / 2500000000000000 : ℝ) ≤ (7937180315398173 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (33961208882871863 / 2500000000000000 : ℝ) (1528848917937
    / 1000000000000 : ℝ) (7937180315398173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1192_denomLower :
    (7797520670678113 / 10000000000 : ℝ) ≤ Real.exp (16958414106765111 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16958414106765111 / 1250000000000000 : ℝ) (1528001011421
    / 1000000000000 : ℝ) (7797520670678113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1192_product_lower :
    (17424429731765111 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (149 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1192_leftExp
    (by norm_num : (0 : ℝ) ≤ (44370955189 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1192_product_upper :
    Real.pi * Real.exp (1193 / 800 : ℝ) ≤ (34892458882871863 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1192_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1192_endpointLower :
    (17477397 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (149 / 200 : ℝ) (1193 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17424429731765111 / 1250000000000000 : ℝ) (Real.pi * Real.exp (149 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1192_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1193 / 800 : ℝ) - (149 / 400 : ℝ)) ≤
      (7937180315398173 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1192_denomUpper
    linarith [hpThetaJensenCell1192_product_upper]
  have hi : (1 / (7937180315398173 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1193 / 800 : ℝ) - (149 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7937180315398173 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7937180315398173 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((149 / 400 : ℝ) - Real.pi * Real.exp (1193 / 800 : ℝ)) := by
    rw [show (149 / 400 : ℝ) - Real.pi * Real.exp (1193 / 800 : ℝ) =
      -(Real.pi * Real.exp (1193 / 800 : ℝ) - (149 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (149 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (149 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1192_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7937180315398173 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1192_endpointUpper :
    hpThetaJensenKernelEndpointUpper (149 / 200 : ℝ) (1193 / 1600 : ℝ) ≤ (8942319 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1193 / 800 : ℝ)) (34892458882871863 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1193 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1192_product_upper
  have hD : (7797520670678113 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (149 / 100 : ℝ) - (1193 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1192_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1192_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (149 / 100 : ℝ) - (1193 / 3200 : ℝ)) ≤
      (1 / (7797520670678113 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7797520670678113 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1193 / 3200 : ℝ) - Real.pi * Real.exp (149 / 100 : ℝ)) ≤
      (2 / (7797520670678113 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1193 / 3200 : ℝ) - Real.pi * Real.exp (149 / 100 : ℝ) =
      -(Real.pi * Real.exp (149 / 100 : ℝ) - (1193 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (34892458882871863 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (34892458882871863 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1192_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (149 / 200 : ℝ) (1193 / 1600 : ℝ)) :
    (17477397 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8942319 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1192_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1192_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1193_leftExp :
    (22213226781 / 5000000000 : ℝ) ≤ Real.exp (1193 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1193 / 800 : ℝ) (1047704481151 / 1000000000000 : ℝ)
    (22213226781 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1193_rightExp :
    Real.exp (597 / 400 : ℝ) ≤ (22241010677 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (597 / 400 : ℝ) (261936351977 / 250000000000 : ℝ)
    (22241010677 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1193_denomUpper :
    Real.exp (68008140955788461 / 5000000000000000 : ℝ) ≤ (8074433615901501 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (68008140955788461 / 5000000000000000 : ℝ) (764834124347
    / 500000000000 : ℝ) (8074433615901501 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1193_denomLower :
    (7932185882467853 / 10000000000 : ℝ) ≤ Real.exp (8489908818671919 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8489908818671919 / 625000000000000 : ℝ) (1528818845617 /
    1000000000000 : ℝ) (7932185882467853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1193_product_lower :
    (8723111943671919 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1193 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1193_leftExp
    (by norm_num : (0 : ℝ) ≤ (22213226781 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1193_product_upper :
    Real.pi * Real.exp (597 / 400 : ℝ) ≤ (69872203455788461 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1193_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1193_endpointLower :
    (8612953 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1193 / 1600 : ℝ) (597 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8723111943671919 / 625000000000000 : ℝ) (Real.pi * Real.exp (1193 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1193_product_lower
  have hD : Real.exp (Real.pi * Real.exp (597 / 400 : ℝ) - (1193 / 3200 : ℝ)) ≤
      (8074433615901501 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1193_denomUpper
    linarith [hpThetaJensenCell1193_product_upper]
  have hi : (1 / (8074433615901501 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (597 / 400 : ℝ) - (1193 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8074433615901501 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8074433615901501 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1193 / 3200 : ℝ) - Real.pi * Real.exp (597 / 400 : ℝ)) := by
    rw [show (1193 / 3200 : ℝ) - Real.pi * Real.exp (597 / 400 : ℝ) =
      -(Real.pi * Real.exp (597 / 400 : ℝ) - (1193 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1193 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1193 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1193_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8074433615901501 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1193_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1193 / 1600 : ℝ) (597 / 800 : ℝ) ≤ (4406917 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (597 / 400 : ℝ)) (69872203455788461 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (597 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1193_product_upper
  have hD : (7932185882467853 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1193 / 800 : ℝ) - (597 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1193_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1193_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1193 / 800 : ℝ) - (597 / 1600 : ℝ)) ≤
      (1 / (7932185882467853 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7932185882467853 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((597 / 1600 : ℝ) - Real.pi * Real.exp (1193 / 800 : ℝ)) ≤
      (2 / (7932185882467853 / 10000000000 : ℝ) : ℝ) := by
    rw [show (597 / 1600 : ℝ) - Real.pi * Real.exp (1193 / 800 : ℝ) =
      -(Real.pi * Real.exp (1193 / 800 : ℝ) - (597 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (69872203455788461 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (69872203455788461 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1193_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1193 / 1600 : ℝ) (597 / 800 : ℝ)) :
    (8612953 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4406917 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1193_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1193_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1194_leftExp :
    (5560252669 / 1250000000 : ℝ) ≤ Real.exp (597 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (597 / 400 : ℝ) (1047745407907 / 1000000000000 : ℝ)
    (5560252669 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1194_rightExp :
    Real.exp (239 / 160 : ℝ) ≤ (44537658647 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (239 / 160 : ℝ) (523893168131 / 500000000000 : ℝ)
    (44537658647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1194_denomUpper :
    Real.exp (136187946641804671 / 10000000000000000 : ℝ) ≤ (4107119859188297 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (136187946641804671 / 10000000000000000 : ℝ)
    (1530489062861 / 1000000000000 : ℝ) (4107119859188297 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1194_denomLower :
    (8069352772108891 / 10000000000 : ℝ) ≤ Real.exp (2125156053488631 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2125156053488631 / 156250000000000 : ℝ) (191204769999 /
    125000000000 : ℝ) (8069352772108891 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1194_product_lower :
    (2183505662863631 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (597 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1194_leftExp
    (by norm_num : (0 : ℝ) ≤ (5560252669 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1194_product_upper :
    Real.pi * Real.exp (239 / 160 : ℝ) ≤ (139919196641804671 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1194_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1194_endpointLower :
    (848883 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (597 / 800 : ℝ) (239 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2183505662863631 / 156250000000000 : ℝ) (Real.pi * Real.exp (597 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1194_product_lower
  have hD : Real.exp (Real.pi * Real.exp (239 / 160 : ℝ) - (597 / 1600 : ℝ)) ≤
      (4107119859188297 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1194_denomUpper
    linarith [hpThetaJensenCell1194_product_upper]
  have hi : (1 / (4107119859188297 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (239 / 160 : ℝ) - (597 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4107119859188297 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4107119859188297 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((597 / 1600 : ℝ) - Real.pi * Real.exp (239 / 160 : ℝ)) := by
    rw [show (597 / 1600 : ℝ) - Real.pi * Real.exp (239 / 160 : ℝ) =
      -(Real.pi * Real.exp (239 / 160 : ℝ) - (597 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (597 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (597 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1194_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4107119859188297 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1194_endpointUpper :
    hpThetaJensenKernelEndpointUpper (597 / 800 : ℝ) (239 / 320 : ℝ) ≤ (2171751 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (239 / 160 : ℝ)) (139919196641804671 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (239 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1194_product_upper
  have hD : (8069352772108891 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (597 / 400 : ℝ) - (239 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1194_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1194_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (597 / 400 : ℝ) - (239 / 640 : ℝ)) ≤
      (1 / (8069352772108891 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8069352772108891 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((239 / 640 : ℝ) - Real.pi * Real.exp (597 / 400 : ℝ)) ≤
      (2 / (8069352772108891 / 10000000000 : ℝ) : ℝ) := by
    rw [show (239 / 640 : ℝ) - Real.pi * Real.exp (597 / 400 : ℝ) =
      -(Real.pi * Real.exp (597 / 400 : ℝ) - (239 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (139919196641804671 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (139919196641804671 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1194_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (597 / 800 : ℝ) (239 / 320 : ℝ)) :
    (848883 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2171751 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1194_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1194_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1195_leftExp :
    (11134414661 / 2500000000 : ℝ) ≤ Real.exp (239 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (239 / 160 : ℝ) (1047786336261 / 1000000000000 : ℝ)
    (11134414661 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1195_rightExp :
    Real.exp (299 / 200 : ℝ) ≤ (44593365529 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (299 / 200 : ℝ) (209565453243 / 200000000000 : ℝ)
    (44593365529 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1195_denomUpper :
    Real.exp (136359829992347697 / 10000000000000000 : ℝ) ≤ (261145287740833 / 312500000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (136359829992347697 / 10000000000000000 : ℝ)
    (1531311363647 / 1000000000000 : ℝ) (261145287740833 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1195_denomLower :
    (8209070853162517 / 10000000000 : ℝ) ≤ Real.exp (4255676627960039 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4255676627960039 / 312500000000000 : ℝ) (382614739433 /
    250000000000 : ℝ) (8209070853162517 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1195_product_lower :
    (4372473502960039 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (239 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1195_leftExp
    (by norm_num : (0 : ℝ) ≤ (11134414661 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1195_product_upper :
    Real.pi * Real.exp (299 / 200 : ℝ) ≤ (140094204992347697 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1195_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1195_endpointLower :
    (8366311 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (239 / 320 : ℝ) (299 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4372473502960039 / 312500000000000 : ℝ) (Real.pi * Real.exp (239 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1195_product_lower
  have hD : Real.exp (Real.pi * Real.exp (299 / 200 : ℝ) - (239 / 640 : ℝ)) ≤
      (261145287740833 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1195_denomUpper
    linarith [hpThetaJensenCell1195_product_upper]
  have hi : (1 / (261145287740833 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (299 / 200 : ℝ) - (239 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (261145287740833 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (261145287740833 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((239 / 640 : ℝ) - Real.pi * Real.exp (299 / 200 : ℝ)) := by
    rw [show (239 / 640 : ℝ) - Real.pi * Real.exp (299 / 200 : ℝ) =
      -(Real.pi * Real.exp (299 / 200 : ℝ) - (239 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (239 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (239 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1195_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (261145287740833 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1195_endpointUpper :
    hpThetaJensenKernelEndpointUpper (239 / 320 : ℝ) (299 / 400 : ℝ) ≤ (856181 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (299 / 200 : ℝ)) (140094204992347697 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (299 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1195_product_upper
  have hD : (8209070853162517 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (239 / 160 : ℝ) - (299 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1195_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1195_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (239 / 160 : ℝ) - (299 / 800 : ℝ)) ≤
      (1 / (8209070853162517 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8209070853162517 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((299 / 800 : ℝ) - Real.pi * Real.exp (239 / 160 : ℝ)) ≤
      (2 / (8209070853162517 / 10000000000 : ℝ) : ℝ) := by
    rw [show (299 / 800 : ℝ) - Real.pi * Real.exp (239 / 160 : ℝ) =
      -(Real.pi * Real.exp (239 / 160 : ℝ) - (299 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (140094204992347697 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (140094204992347697 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1195_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (239 / 320 : ℝ) (299 / 400 : ℝ)) :
    (8366311 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (856181 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1195_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1195_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1196_leftExp :
    (44593365527 / 10000000000 : ℝ) ≤ Real.exp (299 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (299 / 200 : ℝ) (523913633107 / 500000000000 : ℝ)
    (44593365527 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1196_rightExp :
    Real.exp (1197 / 800 : ℝ) ≤ (44649142089 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1197 / 800 : ℝ) (1047868197767 / 1000000000000 : ℝ)
    (44649142089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1196_denomUpper :
    Real.exp (136531932242807777 / 10000000000000000 : ℝ) ≤ (212542843433283 / 250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (136531932242807777 / 10000000000000000 : ℝ)
    (306427030863 / 200000000000 : ℝ) (212542843433283 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1196_denomLower :
    (8351390686543139 / 10000000000 : ℝ) ≤ Real.exp (17044191924087373 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17044191924087373 / 1250000000000000 : ℝ) (382820310523
    / 250000000000 : ℝ) (8351390686543139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1196_product_lower :
    (17511770049087373 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (299 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1196_leftExp
    (by norm_num : (0 : ℝ) ≤ (44593365527 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1196_product_upper :
    Real.pi * Real.exp (1197 / 800 : ℝ) ≤ (140269432242807777 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1196_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1196_endpointLower :
    (4122689 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (299 / 400 : ℝ) (1197 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17511770049087373 / 1250000000000000 : ℝ) (Real.pi * Real.exp (299 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1196_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1197 / 800 : ℝ) - (299 / 800 : ℝ)) ≤
      (212542843433283 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1196_denomUpper
    linarith [hpThetaJensenCell1196_product_upper]
  have hi : (1 / (212542843433283 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1197 / 800 : ℝ) - (299 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (212542843433283 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (212542843433283 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((299 / 800 : ℝ) - Real.pi * Real.exp (1197 / 800 : ℝ)) := by
    rw [show (299 / 800 : ℝ) - Real.pi * Real.exp (1197 / 800 : ℝ) =
      -(Real.pi * Real.exp (1197 / 800 : ℝ) - (299 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (299 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (299 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1196_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (212542843433283 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1196_endpointUpper :
    hpThetaJensenKernelEndpointUpper (299 / 400 : ℝ) (1197 / 1600 : ℝ) ≤ (4219117 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1197 / 800 : ℝ)) (140269432242807777 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1197 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1196_product_upper
  have hD : (8351390686543139 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (299 / 200 : ℝ) - (1197 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1196_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1196_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (299 / 200 : ℝ) - (1197 / 3200 : ℝ)) ≤
      (1 / (8351390686543139 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8351390686543139 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1197 / 3200 : ℝ) - Real.pi * Real.exp (299 / 200 : ℝ)) ≤
      (2 / (8351390686543139 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1197 / 3200 : ℝ) - Real.pi * Real.exp (299 / 200 : ℝ) =
      -(Real.pi * Real.exp (299 / 200 : ℝ) - (1197 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (140269432242807777 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (140269432242807777 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1196_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (299 / 400 : ℝ) (1197 / 1600 : ℝ)) :
    (4122689 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4219117 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1196_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1196_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1197_leftExp :
    (44649142087 / 10000000000 : ℝ) ≤ Real.exp (1197 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1197 / 800 : ℝ) (523934098883 / 500000000000 : ℝ)
    (44649142087 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1197_rightExp :
    Real.exp (599 / 400 : ℝ) ≤ (22352494207 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (599 / 400 : ℝ) (523954565459 / 500000000000 : ℝ)
    (22352494207 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1197_denomUpper :
    Real.exp (68352126833251751 / 5000000000000000 : ℝ) ≤ (2162371509672799 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (68352126833251751 / 5000000000000000 : ℝ) (1532960438101
    / 1000000000000 : ℝ) (2162371509672799 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1197_denomLower :
    (8496363885080459 / 10000000000 : ℝ) ≤ Real.exp (17065704698422813 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17065704698422813 / 1250000000000000 : ℝ) (47878281759 /
    31250000000 : ℝ) (8496363885080459 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1197_product_lower :
    (17533673448422813 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1197 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1197_leftExp
    (by norm_num : (0 : ℝ) ≤ (44649142087 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1197_product_upper :
    Real.pi * Real.exp (599 / 400 : ℝ) ≤ (70222439333251751 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1197_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1197_endpointLower :
    (16252027 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1197 / 1600 : ℝ) (599 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17533673448422813 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1197 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1197_product_lower
  have hD : Real.exp (Real.pi * Real.exp (599 / 400 : ℝ) - (1197 / 3200 : ℝ)) ≤
      (2162371509672799 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1197_denomUpper
    linarith [hpThetaJensenCell1197_product_upper]
  have hi : (1 / (2162371509672799 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (599 / 400 : ℝ) - (1197 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2162371509672799 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2162371509672799 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1197 / 3200 : ℝ) - Real.pi * Real.exp (599 / 400 : ℝ)) := by
    rw [show (1197 / 3200 : ℝ) - Real.pi * Real.exp (599 / 400 : ℝ) =
      -(Real.pi * Real.exp (599 / 400 : ℝ) - (1197 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1197 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1197 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1197_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2162371509672799 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1197_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1197 / 1600 : ℝ) (599 / 800 : ℝ) ≤ (4158129 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (599 / 400 : ℝ)) (70222439333251751 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (599 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1197_product_upper
  have hD : (8496363885080459 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1197 / 800 : ℝ) - (599 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1197_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1197_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1197 / 800 : ℝ) - (599 / 1600 : ℝ)) ≤
      (1 / (8496363885080459 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8496363885080459 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((599 / 1600 : ℝ) - Real.pi * Real.exp (1197 / 800 : ℝ)) ≤
      (2 / (8496363885080459 / 10000000000 : ℝ) : ℝ) := by
    rw [show (599 / 1600 : ℝ) - Real.pi * Real.exp (1197 / 800 : ℝ) =
      -(Real.pi * Real.exp (1197 / 800 : ℝ) - (599 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (70222439333251751 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (70222439333251751 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1197_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1197 / 1600 : ℝ) (599 / 800 : ℝ)) :
    (16252027 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4158129 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1197_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1197_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1198_leftExp :
    (44704988411 / 10000000000 : ℝ) ≤ Real.exp (599 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (599 / 400 : ℝ) (1047909130917 / 1000000000000 : ℝ)
    (44704988411 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1198_rightExp :
    Real.exp (1199 / 800 : ℝ) ≤ (4476090459 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1199 / 800 : ℝ) (261987516417 / 250000000000 : ℝ)
    (4476090459 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1198_denomUpper :
    Real.exp (13687679453361187 / 1000000000000000 : ℝ) ≤ (8800019948864801 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (13687679453361187 / 1000000000000000 : ℝ) (1533787218237
    / 1000000000000 : ℝ) (8800019948864801 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1198_denomLower :
    (4322021573698321 / 5000000000 : ℝ) ≤ Real.exp (17087244869011289 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17087244869011289 / 1250000000000000 : ℝ) (1532930283559
    / 1000000000000 : ℝ) (4322021573698321 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1198_product_lower :
    (17555604244011289 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (599 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1198_leftExp
    (by norm_num : (0 : ℝ) ≤ (44704988411 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1198_product_upper :
    Real.pi * Real.exp (1199 / 800 : ℝ) ≤ (14062054453361187 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1198_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1198_endpointLower :
    (16016399 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (599 / 800 : ℝ) (1199 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17555604244011289 / 1250000000000000 : ℝ) (Real.pi * Real.exp (599 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1198_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1199 / 800 : ℝ) - (599 / 1600 : ℝ)) ≤
      (8800019948864801 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1198_denomUpper
    linarith [hpThetaJensenCell1198_product_upper]
  have hi : (1 / (8800019948864801 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1199 / 800 : ℝ) - (599 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8800019948864801 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8800019948864801 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((599 / 1600 : ℝ) - Real.pi * Real.exp (1199 / 800 : ℝ)) := by
    rw [show (599 / 1600 : ℝ) - Real.pi * Real.exp (1199 / 800 : ℝ) =
      -(Real.pi * Real.exp (1199 / 800 : ℝ) - (599 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (599 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (599 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1198_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8800019948864801 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1198_endpointUpper :
    hpThetaJensenKernelEndpointUpper (599 / 800 : ℝ) (1199 / 1600 : ℝ) ≤ (1024483 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1199 / 800 : ℝ)) (14062054453361187 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1199 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1198_product_upper
  have hD : (4322021573698321 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (599 / 400 : ℝ) - (1199 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1198_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1198_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (599 / 400 : ℝ) - (1199 / 3200 : ℝ)) ≤
      (1 / (4322021573698321 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4322021573698321 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1199 / 3200 : ℝ) - Real.pi * Real.exp (599 / 400 : ℝ)) ≤
      (2 / (4322021573698321 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1199 / 3200 : ℝ) - Real.pi * Real.exp (599 / 400 : ℝ) =
      -(Real.pi * Real.exp (599 / 400 : ℝ) - (1199 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (14062054453361187 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (14062054453361187 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1198_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (599 / 800 : ℝ) (1199 / 1600 : ℝ)) :
    (16016399 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1024483 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1198_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1198_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1199_leftExp :
    (44760904587 / 10000000000 : ℝ) ≤ Real.exp (1199 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1199 / 800 : ℝ) (1047950065667 / 1000000000000 : ℝ)
    (44760904587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1199_rightExp :
    Real.exp (3 / 2 : ℝ) ≤ (2801055669 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 2 : ℝ) (1047991002017 / 1000000000000 : ℝ)
    (2801055669 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1199_denomUpper :
    Real.exp (8565597194840717 / 625000000000000 : ℝ) ≤ (4476685219578913 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8565597194840717 / 625000000000000 : ℝ) (767307748987 /
    500000000000 : ℝ) (4476685219578913 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1199_denomLower :
    (2198620570326753 / 2500000000 : ℝ) ≤ Real.exp (17108812470410313 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (17108812470410313 / 1250000000000000 : ℝ) (1533757047163
    / 1000000000000 : ℝ) (2198620570326753 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1199_product_lower :
    (17577562470410313 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1199 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1199_leftExp
    (by norm_num : (0 : ℝ) ≤ (44760904587 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1199_product_upper :
    Real.pi * Real.exp (3 / 2 : ℝ) ≤ (8799776882340717 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1199_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1199_endpointLower :
    (15783837 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1199 / 1600 : ℝ) (3 / 4 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (17577562470410313 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1199 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1199_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 2 : ℝ) - (1199 / 3200 : ℝ)) ≤
      (4476685219578913 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1199_denomUpper
    linarith [hpThetaJensenCell1199_product_upper]
  have hi : (1 / (4476685219578913 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 2 : ℝ) - (1199 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4476685219578913 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4476685219578913 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1199 / 3200 : ℝ) - Real.pi * Real.exp (3 / 2 : ℝ)) := by
    rw [show (1199 / 3200 : ℝ) - Real.pi * Real.exp (3 / 2 : ℝ) =
      -(Real.pi * Real.exp (3 / 2 : ℝ) - (1199 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1199 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1199 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1199_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4476685219578913 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1199_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1199 / 1600 : ℝ) (3 / 4 : ℝ) ≤ (4038517 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 2 : ℝ)) (8799776882340717 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 4 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1199_product_upper
  have hD : (2198620570326753 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1199 / 800 : ℝ) - (3 / 8 : ℝ)) := by
    apply le_trans hpThetaJensenCell1199_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1199_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1199 / 800 : ℝ) - (3 / 8 : ℝ)) ≤
      (1 / (2198620570326753 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2198620570326753 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 8 : ℝ) - Real.pi * Real.exp (1199 / 800 : ℝ)) ≤
      (2 / (2198620570326753 / 2500000000 : ℝ) : ℝ) := by
    rw [show (3 / 8 : ℝ) - Real.pi * Real.exp (1199 / 800 : ℝ) =
      -(Real.pi * Real.exp (1199 / 800 : ℝ) - (3 / 8 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8799776882340717 / 625000000000000 : ℝ) ^ 2 - 6 *
      (8799776882340717 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1199_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1199 / 1600 : ℝ) (3 / 4 : ℝ)) :
    (15783837 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4038517 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1199_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1199_endpointUpper

def hpThetaJensenCellsBatch059Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (415241 / 200000000 : ℝ)
  | 1 => (10234333 / 5000000000 : ℝ)
  | 2 => (2017899 / 1000000000 : ℝ)
  | 3 => (994649 / 500000000 : ℝ)
  | 4 => (9805299 / 5000000000 : ℝ)
  | 5 => (9665901 / 5000000000 : ℝ)
  | 6 => (19056553 / 10000000000 : ℝ)
  | 7 => (9392407 / 5000000000 : ℝ)
  | 8 => (18516543 / 10000000000 : ℝ)
  | 9 => (2281463 / 1250000000 : ℝ)
  | 10 => (17990259 / 10000000000 : ℝ)
  | 11 => (2216521 / 1250000000 : ℝ)
  | 12 => (17477397 / 10000000000 : ℝ)
  | 13 => (8612953 / 5000000000 : ℝ)
  | 14 => (848883 / 500000000 : ℝ)
  | 15 => (8366311 / 5000000000 : ℝ)
  | 16 => (4122689 / 2500000000 : ℝ)
  | 17 => (16252027 / 10000000000 : ℝ)
  | 18 => (16016399 / 10000000000 : ℝ)
  | 19 => (15783837 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch059Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4248073 / 2000000000 : ℝ)
  | 1 => (5235167 / 2500000000 : ℝ)
  | 2 => (1290297 / 625000000 : ℝ)
  | 3 => (814103 / 400000000 : ℝ)
  | 4 => (627003 / 312500000 : ℝ)
  | 5 => (4944819 / 2500000000 : ℝ)
  | 6 => (9749037 / 5000000000 : ℝ)
  | 7 => (384409 / 200000000 : ℝ)
  | 8 => (3789273 / 2000000000 : ℝ)
  | 9 => (933789 / 500000000 : ℝ)
  | 10 => (1150541 / 625000000 : ℝ)
  | 11 => (9072477 / 5000000000 : ℝ)
  | 12 => (8942319 / 5000000000 : ℝ)
  | 13 => (4406917 / 2500000000 : ℝ)
  | 14 => (2171751 / 1250000000 : ℝ)
  | 15 => (856181 / 500000000 : ℝ)
  | 16 => (4219117 / 2500000000 : ℝ)
  | 17 => (4158129 / 2500000000 : ℝ)
  | 18 => (1024483 / 625000000 : ℝ)
  | 19 => (4038517 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch059_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch059Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch059Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1180_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1181_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1182_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1183_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1184_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1185_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1186_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1187_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1188_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1189_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1190_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1191_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1192_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1193_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1194_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1195_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1196_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1197_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1198_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1199_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper] at h ⊢
    exact h

end HodgeProofHP
