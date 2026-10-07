import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1520_leftExp :
    (66858944421 / 10000000000 : ℝ) ≤ Real.exp (19 / 10 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (19 / 10 : ℝ) (21223462121 / 20000000000 : ℝ)
    (66858944421 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1520_rightExp :
    Real.exp (1521 / 800 : ℝ) ≤ (1673564259 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1521 / 800 : ℝ) (212242911787 / 200000000000 : ℝ)
    (1673564259 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1520_denomUpper :
    Real.exp (5138907761124587 / 250000000000000 : ℝ) ≤ (4228313103393172523 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (5138907761124587 / 250000000000000 : ℝ) (950484228137 /
    500000000000 : ℝ) (4228313103393172523 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1520_denomLower :
    (823471906259875373 / 1000000000 : ℝ) ≤ Real.exp (25661299990182279 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (25661299990182279 / 1250000000000000 : ℝ) (1899389463909
    / 1000000000000 : ℝ) (823471906259875373 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1520_product_lower :
    (26255440615182279 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (19 / 10 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1520_leftExp
    (by norm_num : (0 : ℝ) ≤ (66858944421 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1520_product_upper :
    Real.pi * Real.exp (1521 / 800 : ℝ) ≤ (5257657761124587 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1520_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1520_endpointLower :
    (7751 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 20 : ℝ) (1521 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26255440615182279 / 1250000000000000 : ℝ) (Real.pi * Real.exp (19 / 10 : ℝ))
    (by norm_num) hpThetaJensenCell1520_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1521 / 800 : ℝ) - (19 / 40 : ℝ)) ≤
      (4228313103393172523 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1520_denomUpper
    linarith [hpThetaJensenCell1520_product_upper]
  have hi : (1 / (4228313103393172523 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1521 / 800 : ℝ) - (19 / 40 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4228313103393172523 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4228313103393172523 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((19 / 40 : ℝ) - Real.pi * Real.exp (1521 / 800 : ℝ)) := by
    rw [show (19 / 40 : ℝ) - Real.pi * Real.exp (1521 / 800 : ℝ) =
      -(Real.pi * Real.exp (1521 / 800 : ℝ) - (19 / 40 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (19 / 10 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (19 / 10 : ℝ)) := by
    have h := hpThetaJensenCell1520_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4228313103393172523 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1520_endpointUpper :
    hpThetaJensenKernelEndpointUpper (19 / 20 : ℝ) (1521 / 1600 : ℝ) ≤ (40009 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1521 / 800 : ℝ)) (5257657761124587 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1521 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1520_product_upper
  have hD : (823471906259875373 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (19 / 10 : ℝ) - (1521 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1520_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1520_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (19 / 10 : ℝ) - (1521 / 3200 : ℝ)) ≤
      (1 / (823471906259875373 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (823471906259875373 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1521 / 3200 : ℝ) - Real.pi * Real.exp (19 / 10 : ℝ)) ≤
      (2 / (823471906259875373 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1521 / 3200 : ℝ) - Real.pi * Real.exp (19 / 10 : ℝ) =
      -(Real.pi * Real.exp (19 / 10 : ℝ) - (1521 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5257657761124587 / 250000000000000 : ℝ) ^ 2 - 6 *
      (5257657761124587 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1520_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (19 / 20 : ℝ) (1521 / 1600 : ℝ)) :
    (7751 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40009 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1520_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1520_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1521_leftExp :
    (66942570357 / 10000000000 : ℝ) ≤ Real.exp (1521 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1521 / 800 : ℝ) (530607279467 / 500000000000 : ℝ)
    (66942570357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1521_rightExp :
    Real.exp (761 / 400 : ℝ) ≤ (67026300893 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (761 / 400 : ℝ) (530628006719 / 500000000000 : ℝ)
    (67026300893 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1521_denomUpper :
    Real.exp (205816232701342549 / 10000000000000000 : ℝ) ≤ (135614285713250237 / 156250000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (205816232701342549 / 10000000000000000 : ℝ)
    (190251315857 / 100000000000 : ℝ) (135614285713250237 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1521_denomLower :
    (1690257176357510829 / 2000000000 : ℝ) ≤ Real.exp (25693749186623543 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25693749186623543 / 1250000000000000 : ℝ) (475232732653
    / 250000000000 : ℝ) (1690257176357510829 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1521_product_lower :
    (26288280436623543 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1521 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1521_leftExp
    (by norm_num : (0 : ℝ) ≤ (66942570357 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1521_product_upper :
    Real.pi * Real.exp (761 / 400 : ℝ) ≤ (210569357701342549 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1521_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1521_endpointLower :
    (37859 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1521 / 1600 : ℝ) (761 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26288280436623543 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1521 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1521_product_lower
  have hD : Real.exp (Real.pi * Real.exp (761 / 400 : ℝ) - (1521 / 3200 : ℝ)) ≤
      (135614285713250237 / 156250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1521_denomUpper
    linarith [hpThetaJensenCell1521_product_upper]
  have hi : (1 / (135614285713250237 / 156250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (761 / 400 : ℝ) - (1521 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (135614285713250237 / 156250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (135614285713250237 / 156250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1521 / 3200 : ℝ) - Real.pi * Real.exp (761 / 400 : ℝ)) := by
    rw [show (1521 / 3200 : ℝ) - Real.pi * Real.exp (761 / 400 : ℝ) =
      -(Real.pi * Real.exp (761 / 400 : ℝ) - (1521 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1521 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1521 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1521_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (135614285713250237 / 156250000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1521_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1521 / 1600 : ℝ) (761 / 800 : ℝ) ≤ (7817 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (761 / 400 : ℝ)) (210569357701342549 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (761 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1521_product_upper
  have hD : (1690257176357510829 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1521 / 800 : ℝ) - (761 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1521_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1521_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1521 / 800 : ℝ) - (761 / 1600 : ℝ)) ≤
      (1 / (1690257176357510829 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1690257176357510829 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((761 / 1600 : ℝ) - Real.pi * Real.exp (1521 / 800 : ℝ)) ≤
      (2 / (1690257176357510829 / 2000000000 : ℝ) : ℝ) := by
    rw [show (761 / 1600 : ℝ) - Real.pi * Real.exp (1521 / 800 : ℝ) =
      -(Real.pi * Real.exp (1521 / 800 : ℝ) - (761 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (210569357701342549 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (210569357701342549 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1521_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1521 / 1600 : ℝ) (761 / 800 : ℝ)) :
    (37859 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7817 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1521_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1521_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1522_leftExp :
    (6702630089 / 1000000000 : ℝ) ≤ Real.exp (761 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (761 / 400 : ℝ) (1061256013437 / 1000000000000 : ℝ)
    (6702630089 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1522_rightExp :
    Real.exp (1523 / 800 : ℝ) ≤ (16777534039 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1523 / 800 : ℝ) (1061297469561 / 1000000000000 : ℝ)
    (16777534039 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1522_denomUpper :
    Real.exp (51519120994184127 / 2500000000000000 : ℝ) ≤ (4454079746644483963 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (51519120994184127 / 2500000000000000 : ℝ) (380812214759
    / 200000000000 : ℝ) (4454079746644483963 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1522_denomLower :
    (2168458315339771071 / 2500000000 : ℝ) ≤ Real.exp (2572623945820211 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2572623945820211 / 125000000000000 : ℝ) (1902475601917 /
    1000000000000 : ℝ) (2168458315339771071 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1522_product_lower :
    (2632116133320211 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (761 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1522_leftExp
    (by norm_num : (0 : ℝ) ≤ (6702630089 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1522_product_upper :
    Real.pi * Real.exp (1523 / 800 : ℝ) ≤ (52708183494184127 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1522_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1522_endpointLower :
    (18491 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (761 / 800 : ℝ) (1523 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2632116133320211 / 125000000000000 : ℝ) (Real.pi * Real.exp (761 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1522_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1523 / 800 : ℝ) - (761 / 1600 : ℝ)) ≤
      (4454079746644483963 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1522_denomUpper
    linarith [hpThetaJensenCell1522_product_upper]
  have hi : (1 / (4454079746644483963 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1523 / 800 : ℝ) - (761 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4454079746644483963 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4454079746644483963 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((761 / 1600 : ℝ) - Real.pi * Real.exp (1523 / 800 : ℝ)) := by
    rw [show (761 / 1600 : ℝ) - Real.pi * Real.exp (1523 / 800 : ℝ) =
      -(Real.pi * Real.exp (1523 / 800 : ℝ) - (761 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (761 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (761 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1522_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4454079746644483963 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1522_endpointUpper :
    hpThetaJensenKernelEndpointUpper (761 / 800 : ℝ) (1523 / 1600 : ℝ) ≤ (38181 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1523 / 800 : ℝ)) (52708183494184127 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1523 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1522_product_upper
  have hD : (2168458315339771071 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (761 / 400 : ℝ) - (1523 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1522_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1522_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (761 / 400 : ℝ) - (1523 / 3200 : ℝ)) ≤
      (1 / (2168458315339771071 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2168458315339771071 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1523 / 3200 : ℝ) - Real.pi * Real.exp (761 / 400 : ℝ)) ≤
      (2 / (2168458315339771071 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1523 / 3200 : ℝ) - Real.pi * Real.exp (761 / 400 : ℝ) =
      -(Real.pi * Real.exp (761 / 400 : ℝ) - (1523 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (52708183494184127 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (52708183494184127 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1522_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (761 / 800 : ℝ) (1523 / 1600 : ℝ)) :
    (18491 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (38181 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1522_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1522_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1523_leftExp :
    (67110136153 / 10000000000 : ℝ) ≤ Real.exp (1523 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1523 / 800 : ℝ) (26532436739 / 25000000000 : ℝ)
    (67110136153 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1523_rightExp :
    Real.exp (381 / 200 : ℝ) ≤ (67194076277 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (381 / 200 : ℝ) (1061338927303 / 1000000000000 : ℝ)
    (67194076277 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1523_denomUpper :
    Real.exp (206337064673289261 / 10000000000000000 : ℝ) ≤ (9143339798729289053 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (206337064673289261 / 10000000000000000 : ℝ) (59550381567
    / 31250000000 : ℝ) (9143339798729289053 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1523_denomLower :
    (890253387756122141 / 1000000000 : ℝ) ≤ Real.exp (25758770857146947 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (25758770857146947 / 1250000000000000 : ℝ) (952011743043
    / 500000000000 : ℝ) (890253387756122141 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1523_product_lower :
    (26354083357146947 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1523 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1523_leftExp
    (by norm_num : (0 : ℝ) ≤ (67110136153 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1523_product_upper :
    Real.pi * Real.exp (381 / 200 : ℝ) ≤ (211096439673289261 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1523_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1523_endpointLower :
    (289 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (1523 / 1600 : ℝ) (381 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26354083357146947 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1523 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1523_product_lower
  have hD : Real.exp (Real.pi * Real.exp (381 / 200 : ℝ) - (1523 / 3200 : ℝ)) ≤
      (9143339798729289053 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1523_denomUpper
    linarith [hpThetaJensenCell1523_product_upper]
  have hi : (1 / (9143339798729289053 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (381 / 200 : ℝ) - (1523 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9143339798729289053 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9143339798729289053 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1523 / 3200 : ℝ) - Real.pi * Real.exp (381 / 200 : ℝ)) := by
    rw [show (1523 / 3200 : ℝ) - Real.pi * Real.exp (381 / 200 : ℝ) =
      -(Real.pi * Real.exp (381 / 200 : ℝ) - (1523 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1523 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1523 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1523_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9143339798729289053 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1523_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1523 / 1600 : ℝ) (381 / 400 : ℝ) ≤ (37297 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (381 / 200 : ℝ)) (211096439673289261 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (381 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1523_product_upper
  have hD : (890253387756122141 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1523 / 800 : ℝ) - (381 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1523_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1523_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1523 / 800 : ℝ) - (381 / 800 : ℝ)) ≤
      (1 / (890253387756122141 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (890253387756122141 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((381 / 800 : ℝ) - Real.pi * Real.exp (1523 / 800 : ℝ)) ≤
      (2 / (890253387756122141 / 1000000000 : ℝ) : ℝ) := by
    rw [show (381 / 800 : ℝ) - Real.pi * Real.exp (1523 / 800 : ℝ) =
      -(Real.pi * Real.exp (1523 / 800 : ℝ) - (381 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (211096439673289261 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (211096439673289261 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1523_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1523 / 1600 : ℝ) (381 / 400 : ℝ)) :
    (289 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (37297 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1523_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1523_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1524_leftExp :
    (33597038137 / 5000000000 : ℝ) ≤ Real.exp (381 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (381 / 200 : ℝ) (530669463651 / 500000000000 : ℝ)
    (33597038137 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1524_rightExp :
    Real.exp (61 / 32 : ℝ) ≤ (67278121391 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 32 : ℝ) (212276077333 / 200000000000 : ℝ)
    (67278121391 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1524_denomUpper :
    Real.exp (206597975215115863 / 10000000000000000 : ℝ) ≤ (9385038549275180141 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (206597975215115863 / 10000000000000000 : ℝ)
    (953583287981 / 500000000000 : ℝ) (9385038549275180141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1524_denomLower :
    (571097849180289407 / 625000000 : ℝ) ≤ Real.exp (12895671716861763 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12895671716861763 / 625000000000000 : ℝ) (952787295657 /
    500000000000 : ℝ) (571097849180289407 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1524_product_lower :
    (13193523279361763 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (381 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1524_leftExp
    (by norm_num : (0 : ℝ) ≤ (33597038137 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1524_product_upper :
    Real.pi * Real.exp (61 / 32 : ℝ) ≤ (211360475215115863 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1524_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1524_endpointLower :
    (17643 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (381 / 400 : ℝ) (61 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13193523279361763 / 625000000000000 : ℝ) (Real.pi * Real.exp (381 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1524_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 32 : ℝ) - (381 / 800 : ℝ)) ≤
      (9385038549275180141 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1524_denomUpper
    linarith [hpThetaJensenCell1524_product_upper]
  have hi : (1 / (9385038549275180141 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 32 : ℝ) - (381 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9385038549275180141 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9385038549275180141 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((381 / 800 : ℝ) - Real.pi * Real.exp (61 / 32 : ℝ)) := by
    rw [show (381 / 800 : ℝ) - Real.pi * Real.exp (61 / 32 : ℝ) =
      -(Real.pi * Real.exp (61 / 32 : ℝ) - (381 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (381 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (381 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1524_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9385038549275180141 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1524_endpointUpper :
    hpThetaJensenKernelEndpointUpper (381 / 400 : ℝ) (61 / 64 : ℝ) ≤ (2277 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 32 : ℝ)) (211360475215115863 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1524_product_upper
  have hD : (571097849180289407 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (381 / 200 : ℝ) - (61 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1524_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1524_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (381 / 200 : ℝ) - (61 / 128 : ℝ)) ≤
      (1 / (571097849180289407 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (571097849180289407 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 128 : ℝ) - Real.pi * Real.exp (381 / 200 : ℝ)) ≤
      (2 / (571097849180289407 / 625000000 : ℝ) : ℝ) := by
    rw [show (61 / 128 : ℝ) - Real.pi * Real.exp (381 / 200 : ℝ) =
      -(Real.pi * Real.exp (381 / 200 : ℝ) - (61 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (211360475215115863 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (211360475215115863 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1524_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (381 / 400 : ℝ) (61 / 64 : ℝ)) :
    (17643 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2277 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1524_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1524_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1525_leftExp :
    (16819530347 / 2500000000 : ℝ) ≤ Real.exp (61 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 32 : ℝ) (132672548333 / 125000000000 : ℝ)
    (16819530347 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1525_rightExp :
    Real.exp (763 / 400 : ℝ) ≤ (538898173 / 80000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (763 / 400 : ℝ) (530710923823 / 500000000000 : ℝ)
    (538898173 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1525_denomUpper :
    Real.exp (1654873728009589 / 80000000000000 : ℝ) ≤ (9633444596350946157 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (1654873728009589 / 80000000000000 : ℝ) (190872417947 /
    100000000000 : ℝ) (9633444596350946157 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1525_denomLower :
    (4689555810431767949 / 5000000000 : ℝ) ≤ Real.exp (6455989310236553 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6455989310236553 / 312500000000000 : ℝ) (1907128925947 /
    1000000000000 : ℝ) (4689555810431767949 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1525_product_lower :
    (6605012747736553 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1525_leftExp
    (by norm_num : (0 : ℝ) ≤ (16819530347 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1525_product_upper :
    Real.pi * Real.exp (763 / 400 : ℝ) ≤ (1692998728009589 / 80000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1525_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1525_endpointLower :
    (6893 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 64 : ℝ) (763 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6605012747736553 / 312500000000000 : ℝ) (Real.pi * Real.exp (61 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1525_product_lower
  have hD : Real.exp (Real.pi * Real.exp (763 / 400 : ℝ) - (61 / 128 : ℝ)) ≤
      (9633444596350946157 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1525_denomUpper
    linarith [hpThetaJensenCell1525_product_upper]
  have hi : (1 / (9633444596350946157 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (763 / 400 : ℝ) - (61 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9633444596350946157 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9633444596350946157 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 128 : ℝ) - Real.pi * Real.exp (763 / 400 : ℝ)) := by
    rw [show (61 / 128 : ℝ) - Real.pi * Real.exp (763 / 400 : ℝ) =
      -(Real.pi * Real.exp (763 / 400 : ℝ) - (61 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1525_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9633444596350946157 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1525_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 64 : ℝ) (763 / 800 : ℝ) ≤ (17793 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (763 / 400 : ℝ)) (1692998728009589 / 80000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (763 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1525_product_upper
  have hD : (4689555810431767949 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 32 : ℝ) - (763 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1525_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1525_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 32 : ℝ) - (763 / 1600 : ℝ)) ≤
      (1 / (4689555810431767949 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4689555810431767949 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((763 / 1600 : ℝ) - Real.pi * Real.exp (61 / 32 : ℝ)) ≤
      (2 / (4689555810431767949 / 5000000000 : ℝ) : ℝ) := by
    rw [show (763 / 1600 : ℝ) - Real.pi * Real.exp (61 / 32 : ℝ) =
      -(Real.pi * Real.exp (61 / 32 : ℝ) - (763 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1692998728009589 / 80000000000000 : ℝ) ^ 2 - 6 *
      (1692998728009589 / 80000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1525_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 64 : ℝ) (763 / 800 : ℝ)) :
    (6893 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17793 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1525_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1525_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1526_leftExp :
    (33681135811 / 5000000000 : ℝ) ≤ Real.exp (763 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (763 / 400 : ℝ) (212284369529 / 200000000000 : ℝ)
    (33681135811 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1526_rightExp :
    Real.exp (1527 / 800 : ℝ) ≤ (33723263557 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1527 / 800 : ℝ) (1061463310247 / 1000000000000 : ℝ)
    (33723263557 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1526_denomUpper :
    Real.exp (103560393727826301 / 5000000000000000 : ℝ) ≤ (9888752514403024139 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (103560393727826301 / 5000000000000000 : ℝ) (95514251453
    / 50000000000 : ℝ) (9888752514403024139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1526_denomLower :
    (9627360711201893819 / 10000000000 : ℝ) ≤ Real.exp (12928306164343889 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (12928306164343889 / 625000000000000 : ℝ) (477171624551 /
    250000000000 : ℝ) (9627360711201893819 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1526_product_lower :
    (13226548351843889 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (763 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1526_leftExp
    (by norm_num : (0 : ℝ) ≤ (33681135811 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1526_product_upper :
    Real.pi * Real.exp (1527 / 800 : ℝ) ≤ (105944768727826301 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1526_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1526_endpointLower :
    (33663 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (763 / 800 : ℝ) (1527 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13226548351843889 / 625000000000000 : ℝ) (Real.pi * Real.exp (763 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1526_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1527 / 800 : ℝ) - (763 / 1600 : ℝ)) ≤
      (9888752514403024139 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1526_denomUpper
    linarith [hpThetaJensenCell1526_product_upper]
  have hi : (1 / (9888752514403024139 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1527 / 800 : ℝ) - (763 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (9888752514403024139 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (9888752514403024139 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((763 / 1600 : ℝ) - Real.pi * Real.exp (1527 / 800 : ℝ)) := by
    rw [show (763 / 1600 : ℝ) - Real.pi * Real.exp (1527 / 800 : ℝ) =
      -(Real.pi * Real.exp (1527 / 800 : ℝ) - (763 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (763 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (763 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1526_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (9888752514403024139 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1526_endpointUpper :
    hpThetaJensenKernelEndpointUpper (763 / 800 : ℝ) (1527 / 1600 : ℝ) ≤ (34759 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1527 / 800 : ℝ)) (105944768727826301 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1527 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1526_product_upper
  have hD : (9627360711201893819 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (763 / 400 : ℝ) - (1527 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1526_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1526_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (763 / 400 : ℝ) - (1527 / 3200 : ℝ)) ≤
      (1 / (9627360711201893819 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (9627360711201893819 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1527 / 3200 : ℝ) - Real.pi * Real.exp (763 / 400 : ℝ)) ≤
      (2 / (9627360711201893819 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1527 / 3200 : ℝ) - Real.pi * Real.exp (763 / 400 : ℝ) =
      -(Real.pi * Real.exp (763 / 400 : ℝ) - (1527 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (105944768727826301 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (105944768727826301 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1526_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (763 / 800 : ℝ) (1527 / 1600 : ℝ)) :
    (33663 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (34759 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1526_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1526_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1527_leftExp :
    (67446527111 / 10000000000 : ℝ) ≤ Real.exp (1527 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1527 / 800 : ℝ) (530731655123 / 500000000000 : ℝ)
    (67446527111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1527_rightExp :
    Real.exp (191 / 100 : ℝ) ≤ (67530887987 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (191 / 100 : ℝ) (1061504774467 / 1000000000000 : ℝ)
    (67530887987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1527_denomUpper :
    Real.exp (207382689983743291 / 10000000000000000 : ℝ) ≤ (10151162738405975077 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (207382689983743291 / 10000000000000000 : ℝ)
    (382369826607 / 200000000000 : ℝ) (10151162738405975077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1527_denomLower :
    (2470626827326679877 / 2500000000 : ℝ) ≤ Real.exp (25889308749962589 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25889308749962589 / 1250000000000000 : ℝ) (1910247316477
    / 1000000000000 : ℝ) (2470626827326679877 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1527_product_lower :
    (26486183749962589 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1527 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1527_leftExp
    (by norm_num : (0 : ℝ) ≤ (67446527111 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1527_product_upper :
    Real.pi * Real.exp (191 / 100 : ℝ) ≤ (212154564983743291 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1527_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1527_endpointLower :
    (16439 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1527 / 1600 : ℝ) (191 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26486183749962589 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1527 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1527_product_lower
  have hD : Real.exp (Real.pi * Real.exp (191 / 100 : ℝ) - (1527 / 3200 : ℝ)) ≤
      (10151162738405975077 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1527_denomUpper
    linarith [hpThetaJensenCell1527_product_upper]
  have hi : (1 / (10151162738405975077 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (191 / 100 : ℝ) - (1527 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10151162738405975077 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10151162738405975077 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1527 / 3200 : ℝ) - Real.pi * Real.exp (191 / 100 : ℝ)) := by
    rw [show (1527 / 3200 : ℝ) - Real.pi * Real.exp (191 / 100 : ℝ) =
      -(Real.pi * Real.exp (191 / 100 : ℝ) - (1527 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1527 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1527 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1527_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10151162738405975077 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1527_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1527 / 1600 : ℝ) (191 / 200 : ℝ) ≤ (33949 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (191 / 100 : ℝ)) (212154564983743291 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (191 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1527_product_upper
  have hD : (2470626827326679877 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1527 / 800 : ℝ) - (191 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1527_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1527_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1527 / 800 : ℝ) - (191 / 400 : ℝ)) ≤
      (1 / (2470626827326679877 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2470626827326679877 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((191 / 400 : ℝ) - Real.pi * Real.exp (1527 / 800 : ℝ)) ≤
      (2 / (2470626827326679877 / 2500000000 : ℝ) : ℝ) := by
    rw [show (191 / 400 : ℝ) - Real.pi * Real.exp (1527 / 800 : ℝ) =
      -(Real.pi * Real.exp (1527 / 800 : ℝ) - (191 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (212154564983743291 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (212154564983743291 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1527_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1527 / 1600 : ℝ) (191 / 200 : ℝ)) :
    (16439 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (33949 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1527_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1527_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1528_leftExp :
    (67530887983 / 10000000000 : ℝ) ≤ Real.exp (191 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (191 / 100 : ℝ) (530752387233 / 500000000000 : ℝ)
    (67530887983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1528_rightExp :
    Real.exp (1529 / 800 : ℝ) ≤ (67615354377 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1529 / 800 : ℝ) (1061546240307 / 1000000000000 : ℝ)
    (67615354377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1528_denomUpper :
    Real.exp (207644924003302561 / 10000000000000000 : ℝ) ≤ (2605220444581018803 / 2500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (207644924003302561 / 10000000000000000 : ℝ)
    (382683299959 / 200000000000 : ℝ) (2605220444581018803 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1528_denomLower :
    (634046982521914733 / 625000000 : ℝ) ≤ Real.exp (25922046555036117 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (25922046555036117 / 1250000000000000 : ℝ) (1911811389051
    / 1000000000000 : ℝ) (634046982521914733 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1528_product_lower :
    (26519312180036117 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (191 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1528_leftExp
    (by norm_num : (0 : ℝ) ≤ (67530887983 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1528_product_upper :
    Real.pi * Real.exp (1529 / 800 : ℝ) ≤ (212419924003302561 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1528_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1528_endpointLower :
    (3211 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (191 / 200 : ℝ) (1529 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26519312180036117 / 1250000000000000 : ℝ) (Real.pi * Real.exp (191 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1528_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1529 / 800 : ℝ) - (191 / 400 : ℝ)) ≤
      (2605220444581018803 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1528_denomUpper
    linarith [hpThetaJensenCell1528_product_upper]
  have hi : (1 / (2605220444581018803 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1529 / 800 : ℝ) - (191 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2605220444581018803 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2605220444581018803 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((191 / 400 : ℝ) - Real.pi * Real.exp (1529 / 800 : ℝ)) := by
    rw [show (191 / 400 : ℝ) - Real.pi * Real.exp (1529 / 800 : ℝ) =
      -(Real.pi * Real.exp (1529 / 800 : ℝ) - (191 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (191 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (191 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1528_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2605220444581018803 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1528_endpointUpper :
    hpThetaJensenKernelEndpointUpper (191 / 200 : ℝ) (1529 / 1600 : ℝ) ≤ (16579 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1529 / 800 : ℝ)) (212419924003302561 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1529 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1528_product_upper
  have hD : (634046982521914733 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (191 / 100 : ℝ) - (1529 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1528_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1528_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (191 / 100 : ℝ) - (1529 / 3200 : ℝ)) ≤
      (1 / (634046982521914733 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (634046982521914733 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1529 / 3200 : ℝ) - Real.pi * Real.exp (191 / 100 : ℝ)) ≤
      (2 / (634046982521914733 / 625000000 : ℝ) : ℝ) := by
    rw [show (1529 / 3200 : ℝ) - Real.pi * Real.exp (191 / 100 : ℝ) =
      -(Real.pi * Real.exp (191 / 100 : ℝ) - (1529 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (212419924003302561 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (212419924003302561 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1528_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (191 / 200 : ℝ) (1529 / 1600 : ℝ)) :
    (3211 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16579 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1528_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1528_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1529_leftExp :
    (33807677187 / 5000000000 : ℝ) ≤ Real.exp (1529 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1529 / 800 : ℝ) (530773120153 / 500000000000 : ℝ)
    (33807677187 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1529_rightExp :
    Real.exp (153 / 80 : ℝ) ≤ (4231245401 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (153 / 80 : ℝ) (1061587707767 / 1000000000000 : ℝ)
    (4231245401 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1529_denomUpper :
    Real.exp (12994218120563793 / 625000000000000 : ℝ) ≤ (10698122395040095151 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (12994218120563793 / 625000000000000 : ℝ) (1914987137747
    / 1000000000000 : ℝ) (10698122395040095151 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1529_denomLower :
    (2603575083263751099 / 2500000000 : ℝ) ≤ Real.exp (12977412898657713 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12977412898657713 / 625000000000000 : ℝ) (1913378724381
    / 1000000000000 : ℝ) (2603575083263751099 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1529_product_lower :
    (13276241023657713 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1529 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1529_leftExp
    (by norm_num : (0 : ℝ) ≤ (33807677187 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1529_product_upper :
    Real.pi * Real.exp (153 / 80 : ℝ) ≤ (13292850933063793 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1529_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1529_endpointLower :
    (31359 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1529 / 1600 : ℝ) (153 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13276241023657713 / 625000000000000 : ℝ) (Real.pi * Real.exp (1529 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1529_product_lower
  have hD : Real.exp (Real.pi * Real.exp (153 / 80 : ℝ) - (1529 / 3200 : ℝ)) ≤
      (10698122395040095151 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1529_denomUpper
    linarith [hpThetaJensenCell1529_product_upper]
  have hi : (1 / (10698122395040095151 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (153 / 80 : ℝ) - (1529 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10698122395040095151 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10698122395040095151 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1529 / 3200 : ℝ) - Real.pi * Real.exp (153 / 80 : ℝ)) := by
    rw [show (1529 / 3200 : ℝ) - Real.pi * Real.exp (153 / 80 : ℝ) =
      -(Real.pi * Real.exp (153 / 80 : ℝ) - (1529 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1529 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1529 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1529_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10698122395040095151 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1529_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1529 / 1600 : ℝ) (153 / 160 : ℝ) ≤ (32383 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (153 / 80 : ℝ)) (13292850933063793 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (153 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1529_product_upper
  have hD : (2603575083263751099 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1529 / 800 : ℝ) - (153 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1529_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1529_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1529 / 800 : ℝ) - (153 / 320 : ℝ)) ≤
      (1 / (2603575083263751099 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2603575083263751099 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((153 / 320 : ℝ) - Real.pi * Real.exp (1529 / 800 : ℝ)) ≤
      (2 / (2603575083263751099 / 2500000000 : ℝ) : ℝ) := by
    rw [show (153 / 320 : ℝ) - Real.pi * Real.exp (1529 / 800 : ℝ) =
      -(Real.pi * Real.exp (1529 / 800 : ℝ) - (153 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13292850933063793 / 625000000000000 : ℝ) ^ 2 - 6 *
      (13292850933063793 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1529_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1529 / 1600 : ℝ) (153 / 160 : ℝ)) :
    (31359 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32383 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1529_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1529_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1530_leftExp :
    (67699926413 / 10000000000 : ℝ) ≤ Real.exp (153 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (153 / 80 : ℝ) (530793853883 / 500000000000 : ℝ)
    (67699926413 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1530_rightExp :
    Real.exp (1531 / 800 : ℝ) ≤ (67784604237 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1531 / 800 : ℝ) (1061629176847 / 1000000000000 : ℝ)
    (67784604237 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1530_denomUpper :
    Real.exp (208170388178729541 / 10000000000000000 : ℝ) ≤ (1372887975288373511 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (208170388178729541 / 10000000000000000 : ℝ)
    (239570131917 / 125000000000 : ℝ) (1372887975288373511 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1530_denomLower :
    (5345682882125206547 / 5000000000 : ℝ) ≤ Real.exp (25987646527458687 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (25987646527458687 / 1250000000000000 : ℝ) (957474665409
    / 500000000000 : ℝ) (5345682882125206547 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1530_product_lower :
    (26585693402458687 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (153 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1530_leftExp
    (by norm_num : (0 : ℝ) ≤ (67699926413 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1530_product_upper :
    Real.pi * Real.exp (1531 / 800 : ℝ) ≤ (212951638178729541 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1530_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1530_endpointLower :
    (49 / 16000000 : ℝ) ≤ hpThetaTraceEndpointLower (153 / 160 : ℝ) (1531 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26585693402458687 / 1250000000000000 : ℝ) (Real.pi * Real.exp (153 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1530_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1531 / 800 : ℝ) - (153 / 320 : ℝ)) ≤
      (1372887975288373511 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1530_denomUpper
    linarith [hpThetaJensenCell1530_product_upper]
  have hi : (1 / (1372887975288373511 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1531 / 800 : ℝ) - (153 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1372887975288373511 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1372887975288373511 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((153 / 320 : ℝ) - Real.pi * Real.exp (1531 / 800 : ℝ)) := by
    rw [show (153 / 320 : ℝ) - Real.pi * Real.exp (1531 / 800 : ℝ) =
      -(Real.pi * Real.exp (1531 / 800 : ℝ) - (153 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (153 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (153 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1530_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1372887975288373511 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1530_endpointUpper :
    hpThetaJensenKernelEndpointUpper (153 / 160 : ℝ) (1531 / 1600 : ℝ) ≤ (15813 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1531 / 800 : ℝ)) (212951638178729541 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1531 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1530_product_upper
  have hD : (5345682882125206547 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (153 / 80 : ℝ) - (1531 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1530_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1530_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (153 / 80 : ℝ) - (1531 / 3200 : ℝ)) ≤
      (1 / (5345682882125206547 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (5345682882125206547 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1531 / 3200 : ℝ) - Real.pi * Real.exp (153 / 80 : ℝ)) ≤
      (2 / (5345682882125206547 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1531 / 3200 : ℝ) - Real.pi * Real.exp (153 / 80 : ℝ) =
      -(Real.pi * Real.exp (153 / 80 : ℝ) - (1531 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (212951638178729541 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (212951638178729541 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1530_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (153 / 160 : ℝ) (1531 / 1600 : ℝ)) :
    (49 / 16000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15813 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1530_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1530_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1531_leftExp :
    (33892302117 / 5000000000 : ℝ) ≤ Real.exp (1531 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1531 / 800 : ℝ) (530814588423 / 500000000000 : ℝ)
    (33892302117 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1531_rightExp :
    Real.exp (383 / 200 : ℝ) ≤ (16967346993 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (383 / 200 : ℝ) (1061670647547 / 1000000000000 : ℝ)
    (16967346993 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1531_denomUpper :
    Real.exp (52108404791779849 / 2500000000000000 : ℝ) ≤ (352376620759043427 / 312500000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (52108404791779849 / 2500000000000000 : ℝ) (959069130507
    / 500000000000 : ℝ) (352376620759043427 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1531_denomLower :
    (10976167092297144757 / 10000000000 : ℝ) ≤ Real.exp (13010254399043783 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (13010254399043783 / 625000000000000 : ℝ) (958261608413 /
    500000000000 : ℝ) (10976167092297144757 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1531_product_lower :
    (13309473149043783 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1531 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1531_leftExp
    (by norm_num : (0 : ℝ) ≤ (33892302117 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1531_product_upper :
    Real.pi * Real.exp (383 / 200 : ℝ) ≤ (53304498541779849 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1531_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1531_endpointLower :
    (14953 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1531 / 1600 : ℝ) (383 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13309473149043783 / 625000000000000 : ℝ) (Real.pi * Real.exp (1531 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1531_product_lower
  have hD : Real.exp (Real.pi * Real.exp (383 / 200 : ℝ) - (1531 / 3200 : ℝ)) ≤
      (352376620759043427 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1531_denomUpper
    linarith [hpThetaJensenCell1531_product_upper]
  have hi : (1 / (352376620759043427 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (383 / 200 : ℝ) - (1531 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (352376620759043427 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (352376620759043427 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1531 / 3200 : ℝ) - Real.pi * Real.exp (383 / 200 : ℝ)) := by
    rw [show (1531 / 3200 : ℝ) - Real.pi * Real.exp (383 / 200 : ℝ) =
      -(Real.pi * Real.exp (383 / 200 : ℝ) - (1531 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1531 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1531 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1531_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (352376620759043427 / 312500000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1531_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1531 / 1600 : ℝ) (383 / 400 : ℝ) ≤ (15443 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (383 / 200 : ℝ)) (53304498541779849 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (383 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1531_product_upper
  have hD : (10976167092297144757 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1531 / 800 : ℝ) - (383 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1531_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1531_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1531 / 800 : ℝ) - (383 / 800 : ℝ)) ≤
      (1 / (10976167092297144757 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (10976167092297144757 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((383 / 800 : ℝ) - Real.pi * Real.exp (1531 / 800 : ℝ)) ≤
      (2 / (10976167092297144757 / 10000000000 : ℝ) : ℝ) := by
    rw [show (383 / 800 : ℝ) - Real.pi * Real.exp (1531 / 800 : ℝ) =
      -(Real.pi * Real.exp (1531 / 800 : ℝ) - (383 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53304498541779849 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (53304498541779849 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1531_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1531 / 1600 : ℝ) (383 / 400 : ℝ)) :
    (14953 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15443 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1531_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1531_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1532_leftExp :
    (67869387969 / 10000000000 : ℝ) ≤ Real.exp (383 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (383 / 200 : ℝ) (530835323773 / 500000000000 : ℝ)
    (67869387969 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1532_rightExp :
    Real.exp (1533 / 800 : ℝ) ≤ (67954277751 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1533 / 800 : ℝ) (530856059933 / 500000000000 : ℝ)
    (67954277751 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1532_denomUpper :
    Real.exp (208697183302597343 / 10000000000000000 : ℝ) ≤ (578859965048410149 / 500000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (208697183302597343 / 10000000000000000 : ℝ) (95985938161
    / 50000000000 : ℝ) (578859965048410149 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1532_denomLower :
    (11268930038723956421 / 10000000000 : ℝ) ≤ Real.exp (26053412661038331 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26053412661038331 / 1250000000000000 : ℝ) (959050195429
    / 500000000000 : ℝ) (11268930038723956421 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1532_product_lower :
    (26652240786038331 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (383 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1532_leftExp
    (by norm_num : (0 : ℝ) ≤ (67869387969 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1532_product_upper :
    Real.pi * Real.exp (1533 / 800 : ℝ) ≤ (213484683302597343 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1532_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1532_endpointLower :
    (7301 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (383 / 400 : ℝ) (1533 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26652240786038331 / 1250000000000000 : ℝ) (Real.pi * Real.exp (383 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1532_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1533 / 800 : ℝ) - (383 / 800 : ℝ)) ≤
      (578859965048410149 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1532_denomUpper
    linarith [hpThetaJensenCell1532_product_upper]
  have hi : (1 / (578859965048410149 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1533 / 800 : ℝ) - (383 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (578859965048410149 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (578859965048410149 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((383 / 800 : ℝ) - Real.pi * Real.exp (1533 / 800 : ℝ)) := by
    rw [show (383 / 800 : ℝ) - Real.pi * Real.exp (1533 / 800 : ℝ) =
      -(Real.pi * Real.exp (1533 / 800 : ℝ) - (383 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (383 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (383 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1532_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (578859965048410149 / 500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1532_endpointUpper :
    hpThetaJensenKernelEndpointUpper (383 / 400 : ℝ) (1533 / 1600 : ℝ) ≤ (30161 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1533 / 800 : ℝ)) (213484683302597343 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1533 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1532_product_upper
  have hD : (11268930038723956421 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (383 / 200 : ℝ) - (1533 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1532_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1532_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (383 / 200 : ℝ) - (1533 / 3200 : ℝ)) ≤
      (1 / (11268930038723956421 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11268930038723956421 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1533 / 3200 : ℝ) - Real.pi * Real.exp (383 / 200 : ℝ)) ≤
      (2 / (11268930038723956421 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1533 / 3200 : ℝ) - Real.pi * Real.exp (383 / 200 : ℝ) =
      -(Real.pi * Real.exp (383 / 200 : ℝ) - (1533 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (213484683302597343 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (213484683302597343 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1532_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (383 / 400 : ℝ) (1533 / 1600 : ℝ)) :
    (7301 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (30161 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1532_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1532_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1533_leftExp :
    (16988569437 / 2500000000 : ℝ) ≤ Real.exp (1533 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1533 / 800 : ℝ) (212342423973 / 200000000000 : ℝ)
    (16988569437 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1533_rightExp :
    Real.exp (767 / 400 : ℝ) ≤ (6803927371 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (767 / 400 : ℝ) (530876796903 / 500000000000 : ℝ)
    (6803927371 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1533_denomUpper :
    Real.exp (20896108101242003 / 1000000000000000 : ℝ) ≤ (11886785932618327453 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (20896108101242003 / 1000000000000000 : ℝ) (960651285263
    / 500000000000 : ℝ) (11886785932618327453 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1533_denomLower :
    (11569887175789031157 / 10000000000 : ℝ) ≤ Real.exp (6521589541840463 / 312500000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (6521589541840463 / 312500000000000 : ℝ) (38393617227 /
    20000000000 : ℝ) (11569887175789031157 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1533_product_lower :
    (6671394229340463 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1533 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1533_leftExp
    (by norm_num : (0 : ℝ) ≤ (16988569437 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1533_product_upper :
    Real.pi * Real.exp (767 / 400 : ℝ) ≤ (21375170601242003 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1533_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1533_endpointLower :
    (28517 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1533 / 1600 : ℝ) (767 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6671394229340463 / 312500000000000 : ℝ) (Real.pi * Real.exp (1533 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1533_product_lower
  have hD : Real.exp (Real.pi * Real.exp (767 / 400 : ℝ) - (1533 / 3200 : ℝ)) ≤
      (11886785932618327453 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1533_denomUpper
    linarith [hpThetaJensenCell1533_product_upper]
  have hi : (1 / (11886785932618327453 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (767 / 400 : ℝ) - (1533 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (11886785932618327453 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (11886785932618327453 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1533 / 3200 : ℝ) - Real.pi * Real.exp (767 / 400 : ℝ)) := by
    rw [show (1533 / 3200 : ℝ) - Real.pi * Real.exp (767 / 400 : ℝ) =
      -(Real.pi * Real.exp (767 / 400 : ℝ) - (1533 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1533 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1533 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1533_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (11886785932618327453 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1533_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1533 / 1600 : ℝ) (767 / 800 : ℝ) ≤ (29453 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (767 / 400 : ℝ)) (21375170601242003 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (767 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1533_product_upper
  have hD : (11569887175789031157 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1533 / 800 : ℝ) - (767 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1533_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1533_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1533 / 800 : ℝ) - (767 / 1600 : ℝ)) ≤
      (1 / (11569887175789031157 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11569887175789031157 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((767 / 1600 : ℝ) - Real.pi * Real.exp (1533 / 800 : ℝ)) ≤
      (2 / (11569887175789031157 / 10000000000 : ℝ) : ℝ) := by
    rw [show (767 / 1600 : ℝ) - Real.pi * Real.exp (1533 / 800 : ℝ) =
      -(Real.pi * Real.exp (1533 / 800 : ℝ) - (767 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21375170601242003 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (21375170601242003 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1533_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1533 / 1600 : ℝ) (767 / 800 : ℝ)) :
    (28517 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (29453 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1533_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1533_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1534_leftExp :
    (68039273707 / 10000000000 : ℝ) ≤ Real.exp (767 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (767 / 400 : ℝ) (212350718761 / 200000000000 : ℝ)
    (68039273707 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1534_rightExp :
    Real.exp (307 / 160 : ℝ) ≤ (3406218799 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (307 / 160 : ℝ) (530897534683 / 500000000000 : ℝ)
    (3406218799 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1534_denomUpper :
    Real.exp (10461265635406807 / 500000000000000 : ℝ) ≤ (2441011773059825721 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (10461265635406807 / 500000000000000 : ℝ) (480722422859 /
    250000000000 : ℝ) (2441011773059825721 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1534_denomLower :
    (11879278172485933493 / 10000000000 : ℝ) ≤ Real.exp (26119345370465193 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26119345370465193 / 1250000000000000 : ℝ) (480316159219
    / 250000000000 : ℝ) (11879278172485933493 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1534_product_lower :
    (26718954745465193 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (767 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1534_leftExp
    (by norm_num : (0 : ℝ) ≤ (68039273707 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1534_product_upper :
    Real.pi * Real.exp (307 / 160 : ℝ) ≤ (10700953135406807 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1534_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1534_endpointLower :
    (13923 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (767 / 800 : ℝ) (307 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26718954745465193 / 1250000000000000 : ℝ) (Real.pi * Real.exp (767 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1534_product_lower
  have hD : Real.exp (Real.pi * Real.exp (307 / 160 : ℝ) - (767 / 1600 : ℝ)) ≤
      (2441011773059825721 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1534_denomUpper
    linarith [hpThetaJensenCell1534_product_upper]
  have hi : (1 / (2441011773059825721 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (307 / 160 : ℝ) - (767 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2441011773059825721 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2441011773059825721 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((767 / 1600 : ℝ) - Real.pi * Real.exp (307 / 160 : ℝ)) := by
    rw [show (767 / 1600 : ℝ) - Real.pi * Real.exp (307 / 160 : ℝ) =
      -(Real.pi * Real.exp (307 / 160 : ℝ) - (767 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (767 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (767 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1534_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2441011773059825721 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1534_endpointUpper :
    hpThetaJensenKernelEndpointUpper (767 / 800 : ℝ) (307 / 320 : ℝ) ≤ (28761 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (307 / 160 : ℝ)) (10700953135406807 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (307 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1534_product_upper
  have hD : (11879278172485933493 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (767 / 400 : ℝ) - (307 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1534_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1534_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (767 / 400 : ℝ) - (307 / 640 : ℝ)) ≤
      (1 / (11879278172485933493 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (11879278172485933493 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((307 / 640 : ℝ) - Real.pi * Real.exp (767 / 400 : ℝ)) ≤
      (2 / (11879278172485933493 / 10000000000 : ℝ) : ℝ) := by
    rw [show (307 / 640 : ℝ) - Real.pi * Real.exp (767 / 400 : ℝ) =
      -(Real.pi * Real.exp (767 / 400 : ℝ) - (307 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10700953135406807 / 500000000000000 : ℝ) ^ 2 - 6 *
      (10700953135406807 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1534_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (767 / 800 : ℝ) (307 / 320 : ℝ)) :
    (13923 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (28761 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1534_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1534_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1535_leftExp :
    (68124375977 / 10000000000 : ℝ) ≤ Real.exp (307 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (307 / 160 : ℝ) (212359013873 / 200000000000 : ℝ)
    (68124375977 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1535_rightExp :
    Real.exp (48 / 25 : ℝ) ≤ (13641916939 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48 / 25 : ℝ) (530918273273 / 500000000000 : ℝ)
    (13641916939 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1535_denomUpper :
    Real.exp (41897975762143827 / 2000000000000000 : ℝ) ≤ (12532272750039380643 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (41897975762143827 / 2000000000000000 : ℝ) (1924480134533
    / 1000000000000 : ℝ) (12532272750039380643 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1535_denomLower :
    (6098674989106712619 / 5000000000 : ℝ) ≤ Real.exp (26152374321791923 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26152374321791923 / 1250000000000000 : ℝ) (961425862969
    / 500000000000 : ℝ) (6098674989106712619 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1535_product_lower :
    (26752374321791923 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (307 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1535_leftExp
    (by norm_num : (0 : ℝ) ≤ (68124375977 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1535_product_upper :
    Real.pi * Real.exp (48 / 25 : ℝ) ≤ (42857350762143827 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1535_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1535_endpointLower :
    (27189 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (307 / 320 : ℝ) (24 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26752374321791923 / 1250000000000000 : ℝ) (Real.pi * Real.exp (307 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1535_product_lower
  have hD : Real.exp (Real.pi * Real.exp (48 / 25 : ℝ) - (307 / 640 : ℝ)) ≤
      (12532272750039380643 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1535_denomUpper
    linarith [hpThetaJensenCell1535_product_upper]
  have hi : (1 / (12532272750039380643 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (48 / 25 : ℝ) - (307 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12532272750039380643 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12532272750039380643 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((307 / 640 : ℝ) - Real.pi * Real.exp (48 / 25 : ℝ)) := by
    rw [show (307 / 640 : ℝ) - Real.pi * Real.exp (48 / 25 : ℝ) =
      -(Real.pi * Real.exp (48 / 25 : ℝ) - (307 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (307 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (307 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1535_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12532272750039380643 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1535_endpointUpper :
    hpThetaJensenKernelEndpointUpper (307 / 320 : ℝ) (24 / 25 : ℝ) ≤ (28083 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (48 / 25 : ℝ)) (42857350762143827 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (24 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1535_product_upper
  have hD : (6098674989106712619 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (307 / 160 : ℝ) - (12 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell1535_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1535_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (307 / 160 : ℝ) - (12 / 25 : ℝ)) ≤
      (1 / (6098674989106712619 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6098674989106712619 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((12 / 25 : ℝ) - Real.pi * Real.exp (307 / 160 : ℝ)) ≤
      (2 / (6098674989106712619 / 5000000000 : ℝ) : ℝ) := by
    rw [show (12 / 25 : ℝ) - Real.pi * Real.exp (307 / 160 : ℝ) =
      -(Real.pi * Real.exp (307 / 160 : ℝ) - (12 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (42857350762143827 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (42857350762143827 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1535_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (307 / 320 : ℝ) (24 / 25 : ℝ)) :
    (27189 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (28083 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1535_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1535_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1536_leftExp :
    (17052396173 / 2500000000 : ℝ) ≤ Real.exp (48 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (48 / 25 : ℝ) (212367309309 / 200000000000 : ℝ)
    (17052396173 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1536_rightExp :
    Real.exp (1537 / 800 : ℝ) ≤ (34147449993 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1537 / 800 : ℝ) (530939012673 / 500000000000 : ℝ)
    (34147449993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1536_denomUpper :
    Real.exp (104877389865858849 / 5000000000000000 : ℝ) ≤ (12868689998789240667 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (104877389865858849 / 5000000000000000 : ℝ)
    (1926073908367 / 1000000000000 : ℝ) (12868689998789240667 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1536_denomLower :
    (12524357083360581003 / 10000000000 : ℝ) ≤ Real.exp (6546361268490927 / 312500000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (6546361268490927 / 312500000000000 : ℝ) (1924442137121 /
    1000000000000 : ℝ) (12524357083360581003 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1536_product_lower :
    (6696458924740927 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (48 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1536_leftExp
    (by norm_num : (0 : ℝ) ≤ (17052396173 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1536_product_upper :
    Real.pi * Real.exp (1537 / 800 : ℝ) ≤ (107277389865858849 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1536_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1536_endpointLower :
    (26547 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (24 / 25 : ℝ) (1537 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6696458924740927 / 312500000000000 : ℝ) (Real.pi * Real.exp (48 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1536_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1537 / 800 : ℝ) - (12 / 25 : ℝ)) ≤
      (12868689998789240667 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1536_denomUpper
    linarith [hpThetaJensenCell1536_product_upper]
  have hi : (1 / (12868689998789240667 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1537 / 800 : ℝ) - (12 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12868689998789240667 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12868689998789240667 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((12 / 25 : ℝ) - Real.pi * Real.exp (1537 / 800 : ℝ)) := by
    rw [show (12 / 25 : ℝ) - Real.pi * Real.exp (1537 / 800 : ℝ) =
      -(Real.pi * Real.exp (1537 / 800 : ℝ) - (12 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (48 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (48 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1536_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12868689998789240667 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1536_endpointUpper :
    hpThetaJensenKernelEndpointUpper (24 / 25 : ℝ) (1537 / 1600 : ℝ) ≤ (27421 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1537 / 800 : ℝ)) (107277389865858849 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1537 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1536_product_upper
  have hD : (12524357083360581003 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (48 / 25 : ℝ) - (1537 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1536_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1536_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (48 / 25 : ℝ) - (1537 / 3200 : ℝ)) ≤
      (1 / (12524357083360581003 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12524357083360581003 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1537 / 3200 : ℝ) - Real.pi * Real.exp (48 / 25 : ℝ)) ≤
      (2 / (12524357083360581003 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1537 / 3200 : ℝ) - Real.pi * Real.exp (48 / 25 : ℝ) =
      -(Real.pi * Real.exp (48 / 25 : ℝ) - (1537 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (107277389865858849 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (107277389865858849 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1536_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (24 / 25 : ℝ) (1537 / 1600 : ℝ)) :
    (26547 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (27421 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1536_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1536_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1537_leftExp :
    (68294899983 / 10000000000 : ℝ) ≤ Real.exp (1537 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1537 / 800 : ℝ) (212375605069 / 200000000000 : ℝ)
    (68294899983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1537_rightExp :
    Real.exp (769 / 400 : ℝ) ≤ (6838032199 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (769 / 400 : ℝ) (1061919505767 / 1000000000000 : ℝ)
    (6838032199 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1537_denomUpper :
    Real.exp (21002001590153007 / 1000000000000000 : ℝ) ≤ (2642916213373118561 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (21002001590153007 / 1000000000000000 : ℝ) (1927671021627
    / 1000000000000 : ℝ) (2642916213373118561 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1537_denomLower :
    (6430280866865778853 / 5000000000 : ℝ) ≤ Real.exp (26218557678424117 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (26218557678424117 / 1250000000000000 : ℝ) (963017939487
    / 500000000000 : ℝ) (6430280866865778853 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1537_product_lower :
    (26819338928424117 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1537 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1537_leftExp
    (by norm_num : (0 : ℝ) ≤ (68294899983 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1537_product_upper :
    Real.pi * Real.exp (769 / 400 : ℝ) ≤ (21482314090153007 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1537_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1537_endpointLower :
    (81 / 31250000 : ℝ) ≤ hpThetaTraceEndpointLower (1537 / 1600 : ℝ) (769 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26819338928424117 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1537 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1537_product_lower
  have hD : Real.exp (Real.pi * Real.exp (769 / 400 : ℝ) - (1537 / 3200 : ℝ)) ≤
      (2642916213373118561 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1537_denomUpper
    linarith [hpThetaJensenCell1537_product_upper]
  have hi : (1 / (2642916213373118561 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (769 / 400 : ℝ) - (1537 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2642916213373118561 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2642916213373118561 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1537 / 3200 : ℝ) - Real.pi * Real.exp (769 / 400 : ℝ)) := by
    rw [show (1537 / 3200 : ℝ) - Real.pi * Real.exp (769 / 400 : ℝ) =
      -(Real.pi * Real.exp (769 / 400 : ℝ) - (1537 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1537 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1537 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1537_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2642916213373118561 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1537_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1537 / 1600 : ℝ) (769 / 800 : ℝ) ≤ (13387 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (769 / 400 : ℝ)) (21482314090153007 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (769 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1537_product_upper
  have hD : (6430280866865778853 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1537 / 800 : ℝ) - (769 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1537_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1537_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1537 / 800 : ℝ) - (769 / 1600 : ℝ)) ≤
      (1 / (6430280866865778853 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6430280866865778853 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((769 / 1600 : ℝ) - Real.pi * Real.exp (1537 / 800 : ℝ)) ≤
      (2 / (6430280866865778853 / 5000000000 : ℝ) : ℝ) := by
    rw [show (769 / 1600 : ℝ) - Real.pi * Real.exp (1537 / 800 : ℝ) =
      -(Real.pi * Real.exp (1537 / 800 : ℝ) - (769 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21482314090153007 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (21482314090153007 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1537_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1537 / 1600 : ℝ) (769 / 800 : ℝ)) :
    (81 / 31250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (13387 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1537_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1537_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1538_leftExp :
    (68380321987 / 10000000000 : ℝ) ≤ Real.exp (769 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (769 / 400 : ℝ) (530959752883 / 500000000000 : ℝ)
    (68380321987 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1538_rightExp :
    Real.exp (1539 / 800 : ℝ) ≤ (13693170167 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1539 / 800 : ℝ) (1061960987807 / 1000000000000 : ℝ)
    (13693170167 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1538_denomUpper :
    Real.exp (42057117544456031 / 2000000000000000 : ℝ) ≤ (13570224645708437321 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (42057117544456031 / 2000000000000000 : ℝ) (1929271482853
    / 1000000000000 : ℝ) (13570224645708437321 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1538_denomLower :
    (825389638336896803 / 625000000 : ℝ) ≤ Real.exp (26251712188972913 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (26251712188972913 / 1250000000000000 : ℝ) (385526592037
    / 200000000000 : ℝ) (825389638336896803 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1538_product_lower :
    (26852884063972913 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (769 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1538_leftExp
    (by norm_num : (0 : ℝ) ≤ (68380321987 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1538_product_upper :
    Real.pi * Real.exp (1539 / 800 : ℝ) ≤ (43018367544456031 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1538_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1538_endpointLower :
    (12653 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (769 / 800 : ℝ) (1539 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (26852884063972913 / 1250000000000000 : ℝ) (Real.pi * Real.exp (769 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1538_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1539 / 800 : ℝ) - (769 / 1600 : ℝ)) ≤
      (13570224645708437321 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1538_denomUpper
    linarith [hpThetaJensenCell1538_product_upper]
  have hi : (1 / (13570224645708437321 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1539 / 800 : ℝ) - (769 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13570224645708437321 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13570224645708437321 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((769 / 1600 : ℝ) - Real.pi * Real.exp (1539 / 800 : ℝ)) := by
    rw [show (769 / 1600 : ℝ) - Real.pi * Real.exp (1539 / 800 : ℝ) =
      -(Real.pi * Real.exp (1539 / 800 : ℝ) - (769 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (769 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (769 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1538_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13570224645708437321 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1538_endpointUpper :
    hpThetaJensenKernelEndpointUpper (769 / 800 : ℝ) (1539 / 1600 : ℝ) ≤ (26141 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1539 / 800 : ℝ)) (43018367544456031 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1539 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1538_product_upper
  have hD : (825389638336896803 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (769 / 400 : ℝ) - (1539 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1538_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1538_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (769 / 400 : ℝ) - (1539 / 3200 : ℝ)) ≤
      (1 / (825389638336896803 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (825389638336896803 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1539 / 3200 : ℝ) - Real.pi * Real.exp (769 / 400 : ℝ)) ≤
      (2 / (825389638336896803 / 625000000 : ℝ) : ℝ) := by
    rw [show (1539 / 3200 : ℝ) - Real.pi * Real.exp (769 / 400 : ℝ) =
      -(Real.pi * Real.exp (769 / 400 : ℝ) - (1539 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (43018367544456031 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (43018367544456031 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1538_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (769 / 800 : ℝ) (1539 / 1600 : ℝ)) :
    (12653 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (26141 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1538_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1538_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1539_leftExp :
    (4279115677 / 625000000 : ℝ) ≤ Real.exp (1539 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1539 / 800 : ℝ) (530980493903 / 500000000000 : ℝ)
    (4279115677 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1539_rightExp :
    Real.exp (77 / 40 : ℝ) ≤ (68551486661 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (77 / 40 : ℝ) (1062002471469 / 1000000000000 : ℝ)
    (68551486661 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1539_denomUpper :
    Real.exp (210551495633790973 / 10000000000000000 : ℝ) ≤ (13935908013466717031 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (210551495633790973 / 10000000000000000 : ℝ)
    (965437650419 / 500000000000 : ℝ) (13935908013466717031 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1539_denomLower :
    (13561653037517580717 / 10000000000 : ℝ) ≤ Real.exp (1642806790992223 / 78125000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (1642806790992223 / 78125000000000 : ℝ) (964616694647 /
    500000000000 : ℝ) (13561653037517580717 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1539_product_lower :
    (1680404447242223 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (1539 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1539_leftExp
    (by norm_num : (0 : ℝ) ≤ (4279115677 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1539_product_upper :
    Real.pi * Real.exp (77 / 40 : ℝ) ≤ (215360870633790973 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1539_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1539_endpointLower :
    (12353 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1539 / 1600 : ℝ) (77 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1680404447242223 / 78125000000000 : ℝ) (Real.pi * Real.exp (1539 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1539_product_lower
  have hD : Real.exp (Real.pi * Real.exp (77 / 40 : ℝ) - (1539 / 3200 : ℝ)) ≤
      (13935908013466717031 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1539_denomUpper
    linarith [hpThetaJensenCell1539_product_upper]
  have hi : (1 / (13935908013466717031 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (77 / 40 : ℝ) - (1539 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13935908013466717031 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13935908013466717031 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1539 / 3200 : ℝ) - Real.pi * Real.exp (77 / 40 : ℝ)) := by
    rw [show (1539 / 3200 : ℝ) - Real.pi * Real.exp (77 / 40 : ℝ) =
      -(Real.pi * Real.exp (77 / 40 : ℝ) - (1539 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1539 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1539 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1539_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13935908013466717031 / 10000000000 :
    ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1539_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1539 / 1600 : ℝ) (77 / 80 : ℝ) ≤ (12761 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (77 / 40 : ℝ)) (215360870633790973 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (77 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1539_product_upper
  have hD : (13561653037517580717 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1539 / 800 : ℝ) - (77 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1539_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1539_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1539 / 800 : ℝ) - (77 / 160 : ℝ)) ≤
      (1 / (13561653037517580717 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (13561653037517580717 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((77 / 160 : ℝ) - Real.pi * Real.exp (1539 / 800 : ℝ)) ≤
      (2 / (13561653037517580717 / 10000000000 : ℝ) : ℝ) := by
    rw [show (77 / 160 : ℝ) - Real.pi * Real.exp (1539 / 800 : ℝ) =
      -(Real.pi * Real.exp (1539 / 800 : ℝ) - (77 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (215360870633790973 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (215360870633790973 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1539_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1539 / 1600 : ℝ) (77 / 80 : ℝ)) :
    (12353 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12761 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1539_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1539_endpointUpper

def hpThetaJensenCellsBatch076Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7751 / 2000000000 : ℝ)
  | 1 => (37859 / 10000000000 : ℝ)
  | 2 => (18491 / 5000000000 : ℝ)
  | 3 => (289 / 80000000 : ℝ)
  | 4 => (17643 / 5000000000 : ℝ)
  | 5 => (6893 / 2000000000 : ℝ)
  | 6 => (33663 / 10000000000 : ℝ)
  | 7 => (16439 / 5000000000 : ℝ)
  | 8 => (3211 / 1000000000 : ℝ)
  | 9 => (31359 / 10000000000 : ℝ)
  | 10 => (49 / 16000000 : ℝ)
  | 11 => (14953 / 5000000000 : ℝ)
  | 12 => (7301 / 2500000000 : ℝ)
  | 13 => (28517 / 10000000000 : ℝ)
  | 14 => (13923 / 5000000000 : ℝ)
  | 15 => (27189 / 10000000000 : ℝ)
  | 16 => (26547 / 10000000000 : ℝ)
  | 17 => (81 / 31250000 : ℝ)
  | 18 => (12653 / 5000000000 : ℝ)
  | 19 => (12353 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch076Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (40009 / 10000000000 : ℝ)
  | 1 => (7817 / 2000000000 : ℝ)
  | 2 => (38181 / 10000000000 : ℝ)
  | 3 => (37297 / 10000000000 : ℝ)
  | 4 => (2277 / 625000000 : ℝ)
  | 5 => (17793 / 5000000000 : ℝ)
  | 6 => (34759 / 10000000000 : ℝ)
  | 7 => (33949 / 10000000000 : ℝ)
  | 8 => (16579 / 5000000000 : ℝ)
  | 9 => (32383 / 10000000000 : ℝ)
  | 10 => (15813 / 5000000000 : ℝ)
  | 11 => (15443 / 5000000000 : ℝ)
  | 12 => (30161 / 10000000000 : ℝ)
  | 13 => (29453 / 10000000000 : ℝ)
  | 14 => (28761 / 10000000000 : ℝ)
  | 15 => (28083 / 10000000000 : ℝ)
  | 16 => (27421 / 10000000000 : ℝ)
  | 17 => (13387 / 5000000000 : ℝ)
  | 18 => (26141 / 10000000000 : ℝ)
  | 19 => (12761 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch076_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch076Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch076Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1520_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1521_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1522_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1523_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1524_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1525_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1526_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1527_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1528_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1529_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1530_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1531_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1532_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1533_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1534_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1535_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1536_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1537_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1538_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1539_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper] at h ⊢
    exact h

end HodgeProofHP
