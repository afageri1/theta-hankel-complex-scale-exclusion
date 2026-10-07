import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1440_leftExp :
    (60496474643 / 10000000000 : ℝ) ≤ Real.exp (9 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 5 : ℝ) (105786211621 / 100000000000 : ℝ)
    (60496474643 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1440_rightExp :
    Real.exp (1441 / 800 : ℝ) ≤ (30286071261 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1441 / 800 : ℝ) (1057903439757 / 1000000000000 : ℝ)
    (30286071261 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1440_denomUpper :
    Real.exp (92896509471058773 / 5000000000000000 : ℝ) ≤ (1171893890892026737 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (92896509471058773 / 5000000000000000 : ℝ) (446779016469
    / 250000000000 : ℝ) (1171893890892026737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1440_denomLower :
    (571999965497743019 / 5000000000 : ℝ) ≤ Real.exp (23194014470831457 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23194014470831457 / 1250000000000000 : ℝ) (1785771191113
    / 1000000000000 : ℝ) (571999965497743019 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1440_product_lower :
    (23756905095831457 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1440_leftExp
    (by norm_num : (0 : ℝ) ≤ (60496474643 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1440_product_upper :
    Real.pi * Real.exp (1441 / 800 : ℝ) ≤ (95146509471058773 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1440_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1440_endpointLower :
    (2839 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 10 : ℝ) (1441 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23756905095831457 / 1250000000000000 : ℝ) (Real.pi * Real.exp (9 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell1440_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1441 / 800 : ℝ) - (9 / 20 : ℝ)) ≤
      (1171893890892026737 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1440_denomUpper
    linarith [hpThetaJensenCell1440_product_upper]
  have hi : (1 / (1171893890892026737 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1441 / 800 : ℝ) - (9 / 20 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1171893890892026737 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1171893890892026737 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 20 : ℝ) - Real.pi * Real.exp (1441 / 800 : ℝ)) := by
    rw [show (9 / 20 : ℝ) - Real.pi * Real.exp (1441 / 800 : ℝ) =
      -(Real.pi * Real.exp (1441 / 800 : ℝ) - (9 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 5 : ℝ)) := by
    have h := hpThetaJensenCell1440_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1171893890892026737 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1440_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 10 : ℝ) (1441 / 1600 : ℝ) ≤ (233881 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1441 / 800 : ℝ)) (95146509471058773 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1441 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1440_product_upper
  have hD : (571999965497743019 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 5 : ℝ) - (1441 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1440_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1440_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 5 : ℝ) - (1441 / 3200 : ℝ)) ≤
      (1 / (571999965497743019 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (571999965497743019 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1441 / 3200 : ℝ) - Real.pi * Real.exp (9 / 5 : ℝ)) ≤
      (2 / (571999965497743019 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1441 / 3200 : ℝ) - Real.pi * Real.exp (9 / 5 : ℝ) =
      -(Real.pi * Real.exp (9 / 5 : ℝ) - (1441 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95146509471058773 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (95146509471058773 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1440_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 10 : ℝ) (1441 / 1600 : ℝ)) :
    (2839 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (233881 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1440_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1440_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1441_leftExp :
    (60572142519 / 10000000000 : ℝ) ≤ Real.exp (1441 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1441 / 800 : ℝ) (264475859939 / 250000000000 : ℝ)
    (60572142519 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1441_rightExp :
    Real.exp (721 / 400 : ℝ) ≤ (60647905041 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (721 / 400 : ℝ) (1057944764917 / 1000000000000 : ℝ)
    (60647905041 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1441_denomUpper :
    Real.exp (186027908941470313 / 10000000000000000 : ℝ) ≤ (149968292362282263 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (186027908941470313 / 10000000000000000 : ℝ) (22355354331
    / 12500000000 : ℝ) (149968292362282263 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1441_denomLower :
    (234230918178079999 / 2000000000 : ℝ) ≤ Real.exp (23223338545068781 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23223338545068781 / 1250000000000000 : ℝ) (446770205819
    / 250000000000 : ℝ) (234230918178079999 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1441_product_lower :
    (23786619795068781 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1441 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1441_leftExp
    (by norm_num : (0 : ℝ) ≤ (60572142519 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1441_product_upper :
    Real.pi * Real.exp (721 / 400 : ℝ) ≤ (190531033941470313 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1441_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1441_endpointLower :
    (222427 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1441 / 1600 : ℝ) (721 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23786619795068781 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1441 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1441_product_lower
  have hD : Real.exp (Real.pi * Real.exp (721 / 400 : ℝ) - (1441 / 3200 : ℝ)) ≤
      (149968292362282263 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1441_denomUpper
    linarith [hpThetaJensenCell1441_product_upper]
  have hi : (1 / (149968292362282263 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (721 / 400 : ℝ) - (1441 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (149968292362282263 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (149968292362282263 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1441 / 3200 : ℝ) - Real.pi * Real.exp (721 / 400 : ℝ)) := by
    rw [show (1441 / 3200 : ℝ) - Real.pi * Real.exp (721 / 400 : ℝ) =
      -(Real.pi * Real.exp (721 / 400 : ℝ) - (1441 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1441 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1441 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1441_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (149968292362282263 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1441_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1441 / 1600 : ℝ) (721 / 800 : ℝ) ≤ (114527 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (721 / 400 : ℝ)) (190531033941470313 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (721 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1441_product_upper
  have hD : (234230918178079999 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1441 / 800 : ℝ) - (721 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1441_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1441_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1441 / 800 : ℝ) - (721 / 1600 : ℝ)) ≤
      (1 / (234230918178079999 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (234230918178079999 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((721 / 1600 : ℝ) - Real.pi * Real.exp (1441 / 800 : ℝ)) ≤
      (2 / (234230918178079999 / 2000000000 : ℝ) : ℝ) := by
    rw [show (721 / 1600 : ℝ) - Real.pi * Real.exp (1441 / 800 : ℝ) =
      -(Real.pi * Real.exp (1441 / 800 : ℝ) - (721 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (190531033941470313 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (190531033941470313 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1441_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1441 / 1600 : ℝ) (721 / 800 : ℝ)) :
    (222427 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (114527 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1441_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1441_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1442_leftExp :
    (30323952519 / 5000000000 : ℝ) ≤ Real.exp (721 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (721 / 400 : ℝ) (264486191229 / 250000000000 : ℝ)
    (30323952519 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1442_rightExp :
    Real.exp (1443 / 800 : ℝ) ≤ (15180940581 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1443 / 800 : ℝ) (264496522923 / 250000000000 : ℝ)
    (15180940581 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1442_denomUpper :
    Real.exp (46565774162685533 / 2500000000000000 : ℝ) ≤ (307074331059676107 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (46565774162685533 / 2500000000000000 : ℝ) (1789743255769
    / 1000000000000 : ℝ) (307074331059676107 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1442_denomLower :
    (1198989458863912791 / 10000000000 : ℝ) ≤ Real.exp (11626349892758781 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (11626349892758781 / 625000000000000 : ℝ) (1788393077579
    / 1000000000000 : ℝ) (1198989458863912791 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1442_product_lower :
    (11908185830258781 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (721 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1442_leftExp
    (by norm_num : (0 : ℝ) ≤ (30323952519 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1442_product_upper :
    Real.pi * Real.exp (1443 / 800 : ℝ) ≤ (47692336662685533 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1442_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1442_endpointLower :
    (6807 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (721 / 800 : ℝ) (1443 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11908185830258781 / 625000000000000 : ℝ) (Real.pi * Real.exp (721 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1442_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1443 / 800 : ℝ) - (721 / 1600 : ℝ)) ≤
      (307074331059676107 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1442_denomUpper
    linarith [hpThetaJensenCell1442_product_upper]
  have hi : (1 / (307074331059676107 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1443 / 800 : ℝ) - (721 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (307074331059676107 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (307074331059676107 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((721 / 1600 : ℝ) - Real.pi * Real.exp (1443 / 800 : ℝ)) := by
    rw [show (721 / 1600 : ℝ) - Real.pi * Real.exp (1443 / 800 : ℝ) =
      -(Real.pi * Real.exp (1443 / 800 : ℝ) - (721 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (721 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (721 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1442_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (307074331059676107 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1442_endpointUpper :
    hpThetaJensenKernelEndpointUpper (721 / 800 : ℝ) (1443 / 1600 : ℝ) ≤ (224321 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1443 / 800 : ℝ)) (47692336662685533 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1443 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1442_product_upper
  have hD : (1198989458863912791 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (721 / 400 : ℝ) - (1443 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1442_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1442_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (721 / 400 : ℝ) - (1443 / 3200 : ℝ)) ≤
      (1 / (1198989458863912791 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1198989458863912791 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1443 / 3200 : ℝ) - Real.pi * Real.exp (721 / 400 : ℝ)) ≤
      (2 / (1198989458863912791 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1443 / 3200 : ℝ) - Real.pi * Real.exp (721 / 400 : ℝ) =
      -(Real.pi * Real.exp (721 / 400 : ℝ) - (1443 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47692336662685533 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (47692336662685533 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1442_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (721 / 800 : ℝ) (1443 / 1600 : ℝ)) :
    (6807 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (224321 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1442_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1442_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1443_leftExp :
    (30361881161 / 5000000000 : ℝ) ≤ Real.exp (1443 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1443 / 800 : ℝ) (1057986091691 / 1000000000000 : ℝ)
    (30361881161 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1443_rightExp :
    Real.exp (361 / 200 : ℝ) ≤ (30399857243 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (361 / 200 : ℝ) (13225342751 / 12500000000 : ℝ)
    (30399857243 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1443_denomUpper :
    Real.exp (93249291215608099 / 5000000000000000 : ℝ) ≤ (314391309002096731 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (93249291215608099 / 5000000000000000 : ℝ) (111941300009
    / 62500000000 : ℝ) (314391309002096731 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1443_denomLower :
    (1227522423401031359 / 10000000000 : ℝ) ≤ Real.exp (11641049120043539 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (11641049120043539 / 625000000000000 : ℝ) (178970796053 /
    100000000000 : ℝ) (1227522423401031359 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1443_product_lower :
    (11923080370043539 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1443 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1443_leftExp
    (by norm_num : (0 : ℝ) ≤ (30361881161 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1443_product_upper :
    Real.pi * Real.exp (361 / 200 : ℝ) ≤ (95503978715608099 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1443_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1443_endpointLower :
    (213309 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1443 / 1600 : ℝ) (361 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11923080370043539 / 625000000000000 : ℝ) (Real.pi * Real.exp (1443 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1443_product_lower
  have hD : Real.exp (Real.pi * Real.exp (361 / 200 : ℝ) - (1443 / 3200 : ℝ)) ≤
      (314391309002096731 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1443_denomUpper
    linarith [hpThetaJensenCell1443_product_upper]
  have hi : (1 / (314391309002096731 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (361 / 200 : ℝ) - (1443 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (314391309002096731 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (314391309002096731 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1443 / 3200 : ℝ) - Real.pi * Real.exp (361 / 200 : ℝ)) := by
    rw [show (1443 / 3200 : ℝ) - Real.pi * Real.exp (361 / 200 : ℝ) =
      -(Real.pi * Real.exp (361 / 200 : ℝ) - (1443 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1443 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1443 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1443_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (314391309002096731 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1443_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1443 / 1600 : ℝ) (361 / 400 : ℝ) ≤ (109839 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (361 / 200 : ℝ)) (95503978715608099 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (361 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1443_product_upper
  have hD : (1227522423401031359 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1443 / 800 : ℝ) - (361 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1443_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1443_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1443 / 800 : ℝ) - (361 / 800 : ℝ)) ≤
      (1 / (1227522423401031359 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1227522423401031359 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((361 / 800 : ℝ) - Real.pi * Real.exp (1443 / 800 : ℝ)) ≤
      (2 / (1227522423401031359 / 10000000000 : ℝ) : ℝ) := by
    rw [show (361 / 800 : ℝ) - Real.pi * Real.exp (1443 / 800 : ℝ) =
      -(Real.pi * Real.exp (1443 / 800 : ℝ) - (361 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95503978715608099 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (95503978715608099 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1443_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1443 / 1600 : ℝ) (361 / 400 : ℝ)) :
    (213309 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (109839 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1443_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1443_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1444_leftExp :
    (60799714483 / 10000000000 : ℝ) ≤ Real.exp (361 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (361 / 200 : ℝ) (1058027420079 / 1000000000000 : ℝ)
    (60799714483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1444_rightExp :
    Real.exp (289 / 160 : ℝ) ≤ (1217515233 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (289 / 160 : ℝ) (264517187521 / 250000000000 : ℝ)
    (1217515233 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1444_denomUpper :
    Real.exp (3734687333386169 / 200000000000000 : ℝ) ≤ (643784486245901401 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (3734687333386169 / 200000000000000 : ℝ) (448095246541 /
    250000000000 : ℝ) (643784486245901401 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1444_denomLower :
    (62838593041916623 / 500000000 : ℝ) ≤ Real.exp (23311533952759617 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23311533952759617 / 1250000000000000 : ℝ) (895512739239
    / 500000000000 : ℝ) (62838593041916623 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1444_product_lower :
    (23875987077759617 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (361 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1444_leftExp
    (by norm_num : (0 : ℝ) ≤ (60799714483 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1444_product_upper :
    Real.pi * Real.exp (289 / 160 : ℝ) ≤ (3824937333386169 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1444_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1444_endpointLower :
    (104441 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (361 / 400 : ℝ) (289 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23875987077759617 / 1250000000000000 : ℝ) (Real.pi * Real.exp (361 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1444_product_lower
  have hD : Real.exp (Real.pi * Real.exp (289 / 160 : ℝ) - (361 / 800 : ℝ)) ≤
      (643784486245901401 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1444_denomUpper
    linarith [hpThetaJensenCell1444_product_upper]
  have hi : (1 / (643784486245901401 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (289 / 160 : ℝ) - (361 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (643784486245901401 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (643784486245901401 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((361 / 800 : ℝ) - Real.pi * Real.exp (289 / 160 : ℝ)) := by
    rw [show (361 / 800 : ℝ) - Real.pi * Real.exp (289 / 160 : ℝ) =
      -(Real.pi * Real.exp (289 / 160 : ℝ) - (361 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (361 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (361 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1444_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (643784486245901401 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1444_endpointUpper :
    hpThetaJensenKernelEndpointUpper (361 / 400 : ℝ) (289 / 320 : ℝ) ≤ (107563 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (289 / 160 : ℝ)) (3824937333386169 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (289 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1444_product_upper
  have hD : (62838593041916623 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (361 / 200 : ℝ) - (289 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1444_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1444_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (361 / 200 : ℝ) - (289 / 640 : ℝ)) ≤
      (1 / (62838593041916623 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (62838593041916623 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((289 / 640 : ℝ) - Real.pi * Real.exp (361 / 200 : ℝ)) ≤
      (2 / (62838593041916623 / 500000000 : ℝ) : ℝ) := by
    rw [show (289 / 640 : ℝ) - Real.pi * Real.exp (361 / 200 : ℝ) =
      -(Real.pi * Real.exp (361 / 200 : ℝ) - (289 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3824937333386169 / 200000000000000 : ℝ) ^ 2 - 6 *
      (3824937333386169 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1444_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (361 / 400 : ℝ) (289 / 320 : ℝ)) :
    (104441 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (107563 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1444_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1444_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1445_leftExp :
    (60875761647 / 10000000000 : ℝ) ≤ Real.exp (289 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (289 / 160 : ℝ) (1058068750083 / 1000000000000 : ℝ)
    (60875761647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1445_rightExp :
    Real.exp (723 / 400 : ℝ) ≤ (60951903931 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (723 / 400 : ℝ) (529055040851 / 500000000000 : ℝ)
    (60951903931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1445_denomUpper :
    Real.exp (186970449726302083 / 10000000000000000 : ℝ) ≤ (659163974724143843 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (186970449726302083 / 10000000000000000 : ℝ)
    (896851910133 / 500000000000 : ℝ) (659163974724143843 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1445_denomLower :
    (1286756658731793963 / 10000000000 : ℝ) ≤ Real.exp (23341006973015253 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (23341006973015253 / 1250000000000000 : ℝ) (1792345638037
    / 1000000000000 : ℝ) (1286756658731793963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1445_product_lower :
    (23905850723015253 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (289 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1445_leftExp
    (by norm_num : (0 : ℝ) ≤ (60875761647 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1445_product_upper :
    Real.pi * Real.exp (723 / 400 : ℝ) ≤ (191486074726302083 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1445_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1445_endpointLower :
    (204541 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (289 / 320 : ℝ) (723 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23905850723015253 / 1250000000000000 : ℝ) (Real.pi * Real.exp (289 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1445_product_lower
  have hD : Real.exp (Real.pi * Real.exp (723 / 400 : ℝ) - (289 / 640 : ℝ)) ≤
      (659163974724143843 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1445_denomUpper
    linarith [hpThetaJensenCell1445_product_upper]
  have hi : (1 / (659163974724143843 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (723 / 400 : ℝ) - (289 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (659163974724143843 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (659163974724143843 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((289 / 640 : ℝ) - Real.pi * Real.exp (723 / 400 : ℝ)) := by
    rw [show (289 / 640 : ℝ) - Real.pi * Real.exp (723 / 400 : ℝ) =
      -(Real.pi * Real.exp (723 / 400 : ℝ) - (289 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (289 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (289 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1445_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (659163974724143843 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1445_endpointUpper :
    hpThetaJensenKernelEndpointUpper (289 / 320 : ℝ) (723 / 800 : ℝ) ≤ (210661 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (723 / 400 : ℝ)) (191486074726302083 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (723 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1445_product_upper
  have hD : (1286756658731793963 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (289 / 160 : ℝ) - (723 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1445_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1445_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (289 / 160 : ℝ) - (723 / 1600 : ℝ)) ≤
      (1 / (1286756658731793963 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1286756658731793963 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((723 / 1600 : ℝ) - Real.pi * Real.exp (289 / 160 : ℝ)) ≤
      (2 / (1286756658731793963 / 10000000000 : ℝ) : ℝ) := by
    rw [show (723 / 1600 : ℝ) - Real.pi * Real.exp (289 / 160 : ℝ) =
      -(Real.pi * Real.exp (289 / 160 : ℝ) - (723 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (191486074726302083 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (191486074726302083 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1445_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (289 / 320 : ℝ) (723 / 800 : ℝ)) :
    (204541 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (210661 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1445_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1445_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1446_leftExp :
    (7618987991 / 1250000000 : ℝ) ≤ Real.exp (723 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (723 / 400 : ℝ) (1058110081701 / 1000000000000 : ℝ)
    (7618987991 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1446_rightExp :
    Real.exp (1447 / 800 : ℝ) ≤ (61028141449 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1447 / 800 : ℝ) (529075707467 / 500000000000 : ℝ)
    (61028141449 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1446_denomUpper :
    Real.exp (187206831979188257 / 10000000000000000 : ℝ) ≤ (1349862120093065937 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (187206831979188257 / 10000000000000000 : ℝ)
    (179502930899 / 100000000000 : ℝ) (1349862120093065937 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1446_denomLower :
    (263499244032045569 / 2000000000 : ℝ) ≤ Real.exp (2921314668202709 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2921314668202709 / 156250000000000 : ℝ) (2869869513 /
    1600000000 : ℝ) (263499244032045569 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1446_product_lower :
    (2991968965077709 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (723 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1446_leftExp
    (by norm_num : (0 : ℝ) ≤ (7618987991 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1446_product_upper :
    Real.pi * Real.exp (1447 / 800 : ℝ) ≤ (191725581979188257 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1446_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1446_endpointLower :
    (50071 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (723 / 800 : ℝ) (1447 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2991968965077709 / 156250000000000 : ℝ) (Real.pi * Real.exp (723 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1446_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1447 / 800 : ℝ) - (723 / 1600 : ℝ)) ≤
      (1349862120093065937 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1446_denomUpper
    linarith [hpThetaJensenCell1446_product_upper]
  have hi : (1 / (1349862120093065937 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1447 / 800 : ℝ) - (723 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1349862120093065937 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1349862120093065937 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((723 / 1600 : ℝ) - Real.pi * Real.exp (1447 / 800 : ℝ)) := by
    rw [show (723 / 1600 : ℝ) - Real.pi * Real.exp (1447 / 800 : ℝ) =
      -(Real.pi * Real.exp (1447 / 800 : ℝ) - (723 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (723 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (723 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1446_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1349862120093065937 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1446_endpointUpper :
    hpThetaJensenKernelEndpointUpper (723 / 800 : ℝ) (1447 / 1600 : ℝ) ≤ (206283 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1447 / 800 : ℝ)) (191725581979188257 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1447 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1446_product_upper
  have hD : (263499244032045569 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (723 / 400 : ℝ) - (1447 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1446_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1446_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (723 / 400 : ℝ) - (1447 / 3200 : ℝ)) ≤
      (1 / (263499244032045569 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (263499244032045569 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1447 / 3200 : ℝ) - Real.pi * Real.exp (723 / 400 : ℝ)) ≤
      (2 / (263499244032045569 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1447 / 3200 : ℝ) - Real.pi * Real.exp (723 / 400 : ℝ) =
      -(Real.pi * Real.exp (723 / 400 : ℝ) - (1447 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (191725581979188257 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (191725581979188257 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1446_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (723 / 800 : ℝ) (1447 / 1600 : ℝ)) :
    (50071 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (206283 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1446_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1446_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1447_leftExp :
    (30514070723 / 5000000000 : ℝ) ≤ Real.exp (1447 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1447 / 800 : ℝ) (1058151414933 / 1000000000000 : ℝ)
    (30514070723 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1447_rightExp :
    Real.exp (181 / 100 : ℝ) ≤ (15276118581 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (181 / 100 : ℝ) (1058192749781 / 1000000000000 : ℝ)
    (15276118581 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1447_denomUpper :
    Real.exp (46860878451239533 / 2500000000000000 : ℝ) ≤ (1382191988616450413 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (46860878451239533 / 2500000000000000 : ℝ) (898178729447
    / 500000000000 : ℝ) (1382191988616450413 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1447_denomLower :
    (1349010485711934953 / 10000000000 : ℝ) ≤ Real.exp (11700032558851377 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (11700032558851377 / 625000000000000 : ℝ) (1794993907781
    / 1000000000000 : ℝ) (1349010485711934953 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1447_product_lower :
    (11982845058851377 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1447 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1447_leftExp
    (by norm_num : (0 : ℝ) ≤ (30514070723 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1447_product_upper :
    Real.pi * Real.exp (181 / 100 : ℝ) ≤ (47991347201239533 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1447_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1447_endpointLower :
    (19611 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1447 / 1600 : ℝ) (181 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11982845058851377 / 625000000000000 : ℝ) (Real.pi * Real.exp (1447 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1447_product_lower
  have hD : Real.exp (Real.pi * Real.exp (181 / 100 : ℝ) - (1447 / 3200 : ℝ)) ≤
      (1382191988616450413 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1447_denomUpper
    linarith [hpThetaJensenCell1447_product_upper]
  have hi : (1 / (1382191988616450413 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (181 / 100 : ℝ) - (1447 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1382191988616450413 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1382191988616450413 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1447 / 3200 : ℝ) - Real.pi * Real.exp (181 / 100 : ℝ)) := by
    rw [show (1447 / 3200 : ℝ) - Real.pi * Real.exp (181 / 100 : ℝ) =
      -(Real.pi * Real.exp (181 / 100 : ℝ) - (1447 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1447 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1447 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1447_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1382191988616450413 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1447_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1447 / 1600 : ℝ) (181 / 200 : ℝ) ≤ (20199 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (181 / 100 : ℝ)) (47991347201239533 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (181 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1447_product_upper
  have hD : (1349010485711934953 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1447 / 800 : ℝ) - (181 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1447_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1447_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1447 / 800 : ℝ) - (181 / 400 : ℝ)) ≤
      (1 / (1349010485711934953 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1349010485711934953 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((181 / 400 : ℝ) - Real.pi * Real.exp (1447 / 800 : ℝ)) ≤
      (2 / (1349010485711934953 / 10000000000 : ℝ) : ℝ) := by
    rw [show (181 / 400 : ℝ) - Real.pi * Real.exp (1447 / 800 : ℝ) =
      -(Real.pi * Real.exp (1447 / 800 : ℝ) - (181 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (47991347201239533 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (47991347201239533 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1447_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1447 / 1600 : ℝ) (181 / 200 : ℝ)) :
    (19611 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (20199 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1447_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1447_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1448_leftExp :
    (61104474321 / 10000000000 : ℝ) ≤ Real.exp (181 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (181 / 100 : ℝ) (52909637489 / 50000000000 : ℝ)
    (61104474321 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1448_rightExp :
    Real.exp (1449 / 800 : ℝ) ≤ (30590451337 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1449 / 800 : ℝ) (529117043121 / 500000000000 : ℝ)
    (30590451337 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1448_denomUpper :
    Real.exp (93840247787159841 / 5000000000000000 : ℝ) ≤ (141533862509650017 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (93840247787159841 / 5000000000000000 : ℝ) (1797688276517
    / 1000000000000 : ℝ) (141533862509650017 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1448_denomLower :
    (1381319946600139569 / 10000000000 : ℝ) ≤ Real.exp (23429650336382379 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (23429650336382379 / 1250000000000000 : ℝ) (898161015531
    / 500000000000 : ℝ) (1381319946600139569 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1448_product_lower :
    (23995665961382379 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (181 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1448_leftExp
    (by norm_num : (0 : ℝ) ≤ (61104474321 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1448_product_upper :
    Real.pi * Real.exp (1449 / 800 : ℝ) ≤ (96102747787159841 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1448_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1448_endpointLower :
    (192017 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (181 / 200 : ℝ) (1449 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23995665961382379 / 1250000000000000 : ℝ) (Real.pi * Real.exp (181 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1448_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1449 / 800 : ℝ) - (181 / 400 : ℝ)) ≤
      (141533862509650017 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1448_denomUpper
    linarith [hpThetaJensenCell1448_product_upper]
  have hi : (1 / (141533862509650017 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1449 / 800 : ℝ) - (181 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (141533862509650017 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (141533862509650017 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((181 / 400 : ℝ) - Real.pi * Real.exp (1449 / 800 : ℝ)) := by
    rw [show (181 / 400 : ℝ) - Real.pi * Real.exp (1449 / 800 : ℝ) =
      -(Real.pi * Real.exp (1449 / 800 : ℝ) - (181 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (181 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (181 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1448_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (141533862509650017 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1448_endpointUpper :
    hpThetaJensenKernelEndpointUpper (181 / 200 : ℝ) (1449 / 1600 : ℝ) ≤ (9889 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1449 / 800 : ℝ)) (96102747787159841 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1449 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1448_product_upper
  have hD : (1381319946600139569 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (181 / 100 : ℝ) - (1449 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1448_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1448_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (181 / 100 : ℝ) - (1449 / 3200 : ℝ)) ≤
      (1 / (1381319946600139569 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1381319946600139569 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1449 / 3200 : ℝ) - Real.pi * Real.exp (181 / 100 : ℝ)) ≤
      (2 / (1381319946600139569 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1449 / 3200 : ℝ) - Real.pi * Real.exp (181 / 100 : ℝ) =
      -(Real.pi * Real.exp (181 / 100 : ℝ) - (1449 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (96102747787159841 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (96102747787159841 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1448_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (181 / 200 : ℝ) (1449 / 1600 : ℝ)) :
    (192017 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9889 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1448_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1448_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1449_leftExp :
    (61180902671 / 10000000000 : ℝ) ≤ Real.exp (1449 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1449 / 800 : ℝ) (1058234086241 / 1000000000000 : ℝ)
    (61180902671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1449_rightExp :
    Real.exp (29 / 16 : ℝ) ≤ (61257426621 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 16 : ℝ) (1058275424319 / 1000000000000 : ℝ)
    (61257426621 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1449_denomUpper :
    Real.exp (187917777670547253 / 10000000000000000 : ℝ) ≤ (1449323684466984267 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (187917777670547253 / 10000000000000000 : ℝ)
    (899510884243 / 500000000000 : ℝ) (1449323684466984267 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1449_denomLower :
    (1414445659641616457 / 10000000000 : ℝ) ≤ Real.exp (23459273047999029 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (23459273047999029 / 1250000000000000 : ℝ) (1797652822009
    / 1000000000000 : ℝ) (1414445659641616457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1449_product_lower :
    (24025679297999029 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1449 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1449_leftExp
    (by norm_num : (0 : ℝ) ≤ (61180902671 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1449_product_upper :
    Real.pi * Real.exp (29 / 16 : ℝ) ≤ (192445902670547253 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1449_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1449_endpointLower :
    (47001 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1449 / 1600 : ℝ) (29 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24025679297999029 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1449 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1449_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 16 : ℝ) - (1449 / 3200 : ℝ)) ≤
      (1449323684466984267 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1449_denomUpper
    linarith [hpThetaJensenCell1449_product_upper]
  have hi : (1 / (1449323684466984267 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 16 : ℝ) - (1449 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1449323684466984267 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1449323684466984267 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1449 / 3200 : ℝ) - Real.pi * Real.exp (29 / 16 : ℝ)) := by
    rw [show (1449 / 3200 : ℝ) - Real.pi * Real.exp (29 / 16 : ℝ) =
      -(Real.pi * Real.exp (29 / 16 : ℝ) - (1449 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1449 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1449 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1449_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1449323684466984267 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1449_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1449 / 1600 : ℝ) (29 / 32 : ℝ) ≤ (48413 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 16 : ℝ)) (192445902670547253 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1449_product_upper
  have hD : (1414445659641616457 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1449 / 800 : ℝ) - (29 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell1449_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1449_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1449 / 800 : ℝ) - (29 / 64 : ℝ)) ≤
      (1 / (1414445659641616457 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1414445659641616457 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 64 : ℝ) - Real.pi * Real.exp (1449 / 800 : ℝ)) ≤
      (2 / (1414445659641616457 / 10000000000 : ℝ) : ℝ) := by
    rw [show (29 / 64 : ℝ) - Real.pi * Real.exp (1449 / 800 : ℝ) =
      -(Real.pi * Real.exp (1449 / 800 : ℝ) - (29 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (192445902670547253 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (192445902670547253 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1449_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1449 / 1600 : ℝ) (29 / 32 : ℝ)) :
    (47001 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (48413 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1449_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1449_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1450_leftExp :
    (30628713309 / 5000000000 : ℝ) ≤ Real.exp (29 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 16 : ℝ) (529137712159 / 500000000000 : ℝ)
    (30628713309 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1450_rightExp :
    Real.exp (1451 / 800 : ℝ) ≤ (61334046281 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1451 / 800 : ℝ) (105831676401 / 100000000000 : ℝ)
    (61334046281 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1450_denomUpper :
    Real.exp (188155360458065633 / 10000000000000000 : ℝ) ≤ (1484169418832104679 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (188155360458065633 / 10000000000000000 : ℝ)
    (900178970669 / 500000000000 : ℝ) (1484169418832104679 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1450_denomLower :
    (22631394782293621 / 156250000 : ℝ) ≤ Real.exp (11744466650230991 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11744466650230991 / 625000000000000 : ℝ) (112436642953 /
    62500000000 : ℝ) (22631394782293621 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1450_product_lower :
    (12027865087730991 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1450_leftExp
    (by norm_num : (0 : ℝ) ≤ (30628713309 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1450_product_upper :
    Real.pi * Real.exp (1451 / 800 : ℝ) ≤ (192686610458065633 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1450_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1450_endpointLower :
    (184069 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 32 : ℝ) (1451 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12027865087730991 / 625000000000000 : ℝ) (Real.pi * Real.exp (29 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell1450_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1451 / 800 : ℝ) - (29 / 64 : ℝ)) ≤
      (1484169418832104679 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1450_denomUpper
    linarith [hpThetaJensenCell1450_product_upper]
  have hi : (1 / (1484169418832104679 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1451 / 800 : ℝ) - (29 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1484169418832104679 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1484169418832104679 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 64 : ℝ) - Real.pi * Real.exp (1451 / 800 : ℝ)) := by
    rw [show (29 / 64 : ℝ) - Real.pi * Real.exp (1451 / 800 : ℝ) =
      -(Real.pi * Real.exp (1451 / 800 : ℝ) - (29 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 16 : ℝ)) := by
    have h := hpThetaJensenCell1450_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1484169418832104679 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1450_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 32 : ℝ) (1451 / 1600 : ℝ) ≤ (47401 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1451 / 800 : ℝ)) (192686610458065633 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1451 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1450_product_upper
  have hD : (22631394782293621 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 16 : ℝ) - (1451 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1450_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1450_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 16 : ℝ) - (1451 / 3200 : ℝ)) ≤
      (1 / (22631394782293621 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (22631394782293621 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1451 / 3200 : ℝ) - Real.pi * Real.exp (29 / 16 : ℝ)) ≤
      (2 / (22631394782293621 / 156250000 : ℝ) : ℝ) := by
    rw [show (1451 / 3200 : ℝ) - Real.pi * Real.exp (29 / 16 : ℝ) =
      -(Real.pi * Real.exp (29 / 16 : ℝ) - (1451 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (192686610458065633 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (192686610458065633 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1450_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 32 : ℝ) (1451 / 1600 : ℝ)) :
    (184069 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (47401 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1450_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1450_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1451_leftExp :
    (30667023139 / 5000000000 : ℝ) ≤ Real.exp (1451 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1451 / 800 : ℝ) (1058316764009 / 1000000000000 : ℝ)
    (30667023139 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1451_rightExp :
    Real.exp (363 / 200 : ℝ) ≤ (3838172611 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (363 / 200 : ℝ) (264589526329 / 250000000000 : ℝ)
    (3838172611 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1451_denomUpper :
    Real.exp (11774577770009323 / 625000000000000 : ℝ) ≤ (1519898700251454963 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (11774577770009323 / 625000000000000 : ℝ) (360339360347 /
    200000000000 : ℝ) (1519898700251454963 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1451_denomLower :
    (741616501974853787 / 5000000000 : ℝ) ≤ Real.exp (11759315569662161 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11759315569662161 / 625000000000000 : ℝ) (1800322433317
    / 1000000000000 : ℝ) (741616501974853787 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1451_product_lower :
    (12042909319662161 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1451 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1451_leftExp
    (by norm_num : (0 : ℝ) ≤ (30667023139 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1451_product_upper :
    Real.pi * Real.exp (363 / 200 : ℝ) ≤ (12057976207509323 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1451_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1451_endpointLower :
    (18021 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1451 / 1600 : ℝ) (363 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12042909319662161 / 625000000000000 : ℝ) (Real.pi * Real.exp (1451 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1451_product_lower
  have hD : Real.exp (Real.pi * Real.exp (363 / 200 : ℝ) - (1451 / 3200 : ℝ)) ≤
      (1519898700251454963 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1451_denomUpper
    linarith [hpThetaJensenCell1451_product_upper]
  have hi : (1 / (1519898700251454963 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (363 / 200 : ℝ) - (1451 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1519898700251454963 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1519898700251454963 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1451 / 3200 : ℝ) - Real.pi * Real.exp (363 / 200 : ℝ)) := by
    rw [show (1451 / 3200 : ℝ) - Real.pi * Real.exp (363 / 200 : ℝ) =
      -(Real.pi * Real.exp (363 / 200 : ℝ) - (1451 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1451 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1451 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1451_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1519898700251454963 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1451_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1451 / 1600 : ℝ) (363 / 400 : ℝ) ≤ (46409 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (363 / 200 : ℝ)) (12057976207509323 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (363 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1451_product_upper
  have hD : (741616501974853787 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1451 / 800 : ℝ) - (363 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1451_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1451_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1451 / 800 : ℝ) - (363 / 800 : ℝ)) ≤
      (1 / (741616501974853787 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (741616501974853787 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((363 / 800 : ℝ) - Real.pi * Real.exp (1451 / 800 : ℝ)) ≤
      (2 / (741616501974853787 / 5000000000 : ℝ) : ℝ) := by
    rw [show (363 / 800 : ℝ) - Real.pi * Real.exp (1451 / 800 : ℝ) =
      -(Real.pi * Real.exp (1451 / 800 : ℝ) - (363 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12057976207509323 / 625000000000000 : ℝ) ^ 2 - 6 *
      (12057976207509323 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1451_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1451 / 1600 : ℝ) (363 / 400 : ℝ)) :
    (18021 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (46409 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1451_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1451_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1452_leftExp :
    (61410761773 / 10000000000 : ℝ) ≤ Real.exp (363 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (363 / 200 : ℝ) (211671621063 / 200000000000 : ℝ)
    (61410761773 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1452_rightExp :
    Real.exp (1453 / 800 : ℝ) ≤ (2459502929 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1453 / 800 : ℝ) (1058399448237 / 1000000000000 : ℝ)
    (2459502929 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1452_denomUpper :
    Real.exp (7545257185225897 / 400000000000000 : ℝ) ≤ (77826751722244213 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7545257185225897 / 400000000000000 : ℝ) (1803038356303 /
    1000000000000 : ℝ) (77826751722244213 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1452_denomLower :
    (189867466356227197 / 1250000000 : ℝ) ≤ Real.exp (23548366612495327 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23548366612495327 / 1250000000000000 : ℝ) (450415316719
    / 250000000000 : ℝ) (189867466356227197 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1452_product_lower :
    (24115944737495327 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (363 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1452_leftExp
    (by norm_num : (0 : ℝ) ≤ (61410761773 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1452_product_upper :
    Real.pi * Real.exp (1453 / 800 : ℝ) ≤ (7726757185225897 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1452_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1452_endpointLower :
    (44107 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (363 / 400 : ℝ) (1453 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24115944737495327 / 1250000000000000 : ℝ) (Real.pi * Real.exp (363 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1452_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1453 / 800 : ℝ) - (363 / 800 : ℝ)) ≤
      (77826751722244213 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1452_denomUpper
    linarith [hpThetaJensenCell1452_product_upper]
  have hi : (1 / (77826751722244213 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1453 / 800 : ℝ) - (363 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (77826751722244213 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (77826751722244213 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((363 / 800 : ℝ) - Real.pi * Real.exp (1453 / 800 : ℝ)) := by
    rw [show (363 / 800 : ℝ) - Real.pi * Real.exp (1453 / 800 : ℝ) =
      -(Real.pi * Real.exp (1453 / 800 : ℝ) - (363 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (363 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (363 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1452_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (77826751722244213 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1452_endpointUpper :
    hpThetaJensenKernelEndpointUpper (363 / 400 : ℝ) (1453 / 1600 : ℝ) ≤ (36349 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1453 / 800 : ℝ)) (7726757185225897 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1453 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1452_product_upper
  have hD : (189867466356227197 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (363 / 200 : ℝ) - (1453 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1452_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1452_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (363 / 200 : ℝ) - (1453 / 3200 : ℝ)) ≤
      (1 / (189867466356227197 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (189867466356227197 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1453 / 3200 : ℝ) - Real.pi * Real.exp (363 / 200 : ℝ)) ≤
      (2 / (189867466356227197 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1453 / 3200 : ℝ) - Real.pi * Real.exp (363 / 200 : ℝ) =
      -(Real.pi * Real.exp (363 / 200 : ℝ) - (1453 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7726757185225897 / 400000000000000 : ℝ) ^ 2 - 6 *
      (7726757185225897 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1452_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (363 / 400 : ℝ) (1453 / 1600 : ℝ)) :
    (44107 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (36349 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1452_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1452_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1453_leftExp :
    (30743786611 / 5000000000 : ℝ) ≤ Real.exp (1453 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1453 / 800 : ℝ) (264599862059 / 250000000000 : ℝ)
    (30743786611 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1453_rightExp :
    Real.exp (727 / 400 : ℝ) ≤ (61564480749 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (727 / 400 : ℝ) (1058440792773 / 1000000000000 : ℝ)
    (61564480749 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1453_denomUpper :
    Real.exp (188869916769693157 / 10000000000000000 : ℝ) ≤ (797051290721790571 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (188869916769693157 / 10000000000000000 : ℝ)
    (1804382611719 / 1000000000000 : ℝ) (797051290721790571 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1453_denomLower :
    (388888234409215981 / 2500000000 : ℝ) ≤ Real.exp (11789069883353089 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11789069883353089 / 625000000000000 : ℝ) (1803002794551
    / 1000000000000 : ℝ) (388888234409215981 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1453_product_lower :
    (12073054258353089 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1453 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1453_leftExp
    (by norm_num : (0 : ℝ) ≤ (30743786611 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1453_product_upper :
    Real.pi * Real.exp (727 / 400 : ℝ) ≤ (193410541769693157 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1453_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1453_endpointLower :
    (2159 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (1453 / 1600 : ℝ) (727 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12073054258353089 / 625000000000000 : ℝ) (Real.pi * Real.exp (1453 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1453_product_lower
  have hD : Real.exp (Real.pi * Real.exp (727 / 400 : ℝ) - (1453 / 3200 : ℝ)) ≤
      (797051290721790571 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1453_denomUpper
    linarith [hpThetaJensenCell1453_product_upper]
  have hi : (1 / (797051290721790571 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (727 / 400 : ℝ) - (1453 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (797051290721790571 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (797051290721790571 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1453 / 3200 : ℝ) - Real.pi * Real.exp (727 / 400 : ℝ)) := by
    rw [show (1453 / 3200 : ℝ) - Real.pi * Real.exp (727 / 400 : ℝ) =
      -(Real.pi * Real.exp (727 / 400 : ℝ) - (1453 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1453 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1453 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1453_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (797051290721790571 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1453_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1453 / 1600 : ℝ) (727 / 800 : ℝ) ≤ (17793 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (727 / 400 : ℝ)) (193410541769693157 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (727 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1453_product_upper
  have hD : (388888234409215981 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1453 / 800 : ℝ) - (727 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1453_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1453_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1453 / 800 : ℝ) - (727 / 1600 : ℝ)) ≤
      (1 / (388888234409215981 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (388888234409215981 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((727 / 1600 : ℝ) - Real.pi * Real.exp (1453 / 800 : ℝ)) ≤
      (2 / (388888234409215981 / 2500000000 : ℝ) : ℝ) := by
    rw [show (727 / 1600 : ℝ) - Real.pi * Real.exp (1453 / 800 : ℝ) =
      -(Real.pi * Real.exp (1453 / 800 : ℝ) - (727 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (193410541769693157 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (193410541769693157 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1453_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1453 / 1600 : ℝ) (727 / 800 : ℝ)) :
    (2159 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17793 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1453_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1453_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1454_leftExp :
    (30782240373 / 5000000000 : ℝ) ≤ Real.exp (727 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (727 / 400 : ℝ) (264610198193 / 250000000000 : ℝ)
    (30782240373 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1454_rightExp :
    Real.exp (291 / 160 : ℝ) ≤ (61641484467 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (291 / 160 : ℝ) (264620534731 / 250000000000 : ℝ)
    (61641484467 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1454_denomUpper :
    Real.exp (189108706111135931 / 10000000000000000 : ℝ) ≤ (1632626172640353671 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (189108706111135931 / 10000000000000000 : ℝ)
    (1805729574643 / 1000000000000 : ℝ) (1632626172640353671 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1454_denomLower :
    (1593096769106864571 / 10000000000 : ℝ) ≤ Real.exp (11803975324736727 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (11803975324736727 / 625000000000000 : ℝ) (90217351151 /
    50000000000 : ℝ) (1593096769106864571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1454_product_lower :
    (12088155012236727 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (727 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1454_leftExp
    (by norm_num : (0 : ℝ) ≤ (30782240373 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1454_product_upper :
    Real.pi * Real.exp (291 / 160 : ℝ) ≤ (193652456111135931 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1454_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1454_endpointLower :
    (42271 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (727 / 800 : ℝ) (291 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12088155012236727 / 625000000000000 : ℝ) (Real.pi * Real.exp (727 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1454_product_lower
  have hD : Real.exp (Real.pi * Real.exp (291 / 160 : ℝ) - (727 / 1600 : ℝ)) ≤
      (1632626172640353671 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1454_denomUpper
    linarith [hpThetaJensenCell1454_product_upper]
  have hi : (1 / (1632626172640353671 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (291 / 160 : ℝ) - (727 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1632626172640353671 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1632626172640353671 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((727 / 1600 : ℝ) - Real.pi * Real.exp (291 / 160 : ℝ)) := by
    rw [show (727 / 1600 : ℝ) - Real.pi * Real.exp (291 / 160 : ℝ) =
      -(Real.pi * Real.exp (291 / 160 : ℝ) - (727 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (727 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (727 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1454_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1632626172640353671 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1454_endpointUpper :
    hpThetaJensenKernelEndpointUpper (727 / 800 : ℝ) (291 / 320 : ℝ) ≤ (17419 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (291 / 160 : ℝ)) (193652456111135931 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (291 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1454_product_upper
  have hD : (1593096769106864571 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (727 / 400 : ℝ) - (291 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1454_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1454_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (727 / 400 : ℝ) - (291 / 640 : ℝ)) ≤
      (1 / (1593096769106864571 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1593096769106864571 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((291 / 640 : ℝ) - Real.pi * Real.exp (727 / 400 : ℝ)) ≤
      (2 / (1593096769106864571 / 10000000000 : ℝ) : ℝ) := by
    rw [show (291 / 640 : ℝ) - Real.pi * Real.exp (727 / 400 : ℝ) =
      -(Real.pi * Real.exp (727 / 400 : ℝ) - (291 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (193652456111135931 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (193652456111135931 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1454_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (727 / 800 : ℝ) (291 / 320 : ℝ)) :
    (42271 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17419 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1454_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1454_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1455_leftExp :
    (3852592779 / 625000000 : ℝ) ≤ Real.exp (291 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (291 / 160 : ℝ) (1058482138923 / 1000000000000 : ℝ)
    (3852592779 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1455_rightExp :
    Real.exp (91 / 50 : ℝ) ≤ (123437169 / 20000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91 / 50 : ℝ) (105852348669 / 100000000000 : ℝ)
    (123437169 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1455_denomUpper :
    Real.exp (378695596070217 / 20000000000000 : ℝ) ≤ (1672131332255183313 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (378695596070217 / 20000000000000 : ℝ) (1807079251789 /
    1000000000000 : ℝ) (1672131332255183313 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1455_denomLower :
    (81579802048353351 / 500000000 : ℝ) ≤ Real.exp (1477362456720521 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1477362456720521 / 78125000000000 : ℝ) (1805693958943 /
    1000000000000 : ℝ) (81579802048353351 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1455_product_lower :
    (1512909331720521 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (291 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1455_leftExp
    (by norm_num : (0 : ℝ) ≤ (3852592779 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1455_product_upper :
    Real.pi * Real.exp (91 / 50 : ℝ) ≤ (387789346070217 / 20000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1455_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1455_endpointLower :
    (2069 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (291 / 320 : ℝ) (91 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1512909331720521 / 78125000000000 : ℝ) (Real.pi * Real.exp (291 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1455_product_lower
  have hD : Real.exp (Real.pi * Real.exp (91 / 50 : ℝ) - (291 / 640 : ℝ)) ≤
      (1672131332255183313 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1455_denomUpper
    linarith [hpThetaJensenCell1455_product_upper]
  have hi : (1 / (1672131332255183313 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (91 / 50 : ℝ) - (291 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1672131332255183313 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1672131332255183313 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((291 / 640 : ℝ) - Real.pi * Real.exp (91 / 50 : ℝ)) := by
    rw [show (291 / 640 : ℝ) - Real.pi * Real.exp (91 / 50 : ℝ) =
      -(Real.pi * Real.exp (91 / 50 : ℝ) - (291 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (291 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (291 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1455_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1672131332255183313 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1455_endpointUpper :
    hpThetaJensenKernelEndpointUpper (291 / 320 : ℝ) (91 / 100 : ℝ) ≤ (170523 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (91 / 50 : ℝ)) (387789346070217 / 20000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (91 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1455_product_upper
  have hD : (81579802048353351 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (291 / 160 : ℝ) - (91 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1455_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1455_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (291 / 160 : ℝ) - (91 / 200 : ℝ)) ≤
      (1 / (81579802048353351 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (81579802048353351 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((91 / 200 : ℝ) - Real.pi * Real.exp (291 / 160 : ℝ)) ≤
      (2 / (81579802048353351 / 500000000 : ℝ) : ℝ) := by
    rw [show (91 / 200 : ℝ) - Real.pi * Real.exp (291 / 160 : ℝ) =
      -(Real.pi * Real.exp (291 / 160 : ℝ) - (91 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (387789346070217 / 20000000000000 : ℝ) ^ 2 - 6 *
      (387789346070217 / 20000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1455_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (291 / 320 : ℝ) (91 / 100 : ℝ)) :
    (2069 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (170523 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1455_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1455_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1456_leftExp :
    (61718584497 / 10000000000 : ℝ) ≤ Real.exp (91 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (91 / 50 : ℝ) (1058523486689 / 1000000000000 : ℝ)
    (61718584497 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1456_rightExp :
    Real.exp (1457 / 800 : ℝ) ≤ (7724472621 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1457 / 800 : ℝ) (1058564836071 / 1000000000000 : ℝ)
    (7724472621 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1456_denomUpper :
    Real.exp (23698399114825253 / 1250000000000000 : ℝ) ≤ (1712644295794767881 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (23698399114825253 / 1250000000000000 : ℝ) (452107912467
    / 250000000000 : ℝ) (1712644295794767881 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1456_denomLower :
    (1671076261284765139 / 10000000000 : ℝ) ≤ Real.exp (23667685788387403 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (23667685788387403 / 1250000000000000 : ℝ) (1807043609033
    / 1000000000000 : ℝ) (1671076261284765139 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1456_product_lower :
    (24236826413387403 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (91 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1456_leftExp
    (by norm_num : (0 : ℝ) ≤ (61718584497 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1456_product_upper :
    Real.pi * Real.exp (1457 / 800 : ℝ) ≤ (24267149114825253 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1456_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1456_endpointLower :
    (81013 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 100 : ℝ) (1457 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24236826413387403 / 1250000000000000 : ℝ) (Real.pi * Real.exp (91 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1456_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1457 / 800 : ℝ) - (91 / 200 : ℝ)) ≤
      (1712644295794767881 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1456_denomUpper
    linarith [hpThetaJensenCell1456_product_upper]
  have hi : (1 / (1712644295794767881 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1457 / 800 : ℝ) - (91 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1712644295794767881 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1712644295794767881 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((91 / 200 : ℝ) - Real.pi * Real.exp (1457 / 800 : ℝ)) := by
    rw [show (91 / 200 : ℝ) - Real.pi * Real.exp (1457 / 800 : ℝ) =
      -(Real.pi * Real.exp (1457 / 800 : ℝ) - (91 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (91 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (91 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1456_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1712644295794767881 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1456_endpointUpper :
    hpThetaJensenKernelEndpointUpper (91 / 100 : ℝ) (1457 / 1600 : ℝ) ≤ (166929 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1457 / 800 : ℝ)) (24267149114825253 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1457 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1456_product_upper
  have hD : (1671076261284765139 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (91 / 50 : ℝ) - (1457 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1456_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1456_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (91 / 50 : ℝ) - (1457 / 3200 : ℝ)) ≤
      (1 / (1671076261284765139 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1671076261284765139 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1457 / 3200 : ℝ) - Real.pi * Real.exp (91 / 50 : ℝ)) ≤
      (2 / (1671076261284765139 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1457 / 3200 : ℝ) - Real.pi * Real.exp (91 / 50 : ℝ) =
      -(Real.pi * Real.exp (91 / 50 : ℝ) - (1457 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24267149114825253 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (24267149114825253 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1456_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (91 / 100 : ℝ) (1457 / 1600 : ℝ)) :
    (81013 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (166929 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1456_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1456_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1457_leftExp :
    (12359156193 / 2000000000 : ℝ) ≤ Real.exp (1457 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1457 / 800 : ℝ) (105856483607 / 100000000000 : ℝ)
    (12359156193 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1457_rightExp :
    Real.exp (729 / 400 : ℝ) ≤ (61873073993 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (729 / 400 : ℝ) (264651546767 / 250000000000 : ℝ)
    (61873073993 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1457_denomUpper :
    Real.exp (189826891144890849 / 10000000000000000 : ℝ) ≤ (219274004059958489 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (189826891144890849 / 10000000000000000 : ℝ)
    (1809786775647 / 1000000000000 : ℝ) (219274004059958489 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1457_denomLower :
    (1711563648992261029 / 10000000000 : ℝ) ≤ Real.exp (4739522027834907 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4739522027834907 / 250000000000000 : ℝ) (1808395980001 /
    1000000000000 : ℝ) (1711563648992261029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1457_product_lower :
    (4853428277834907 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1457 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1457_leftExp
    (by norm_num : (0 : ℝ) ≤ (12359156193 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1457_product_upper :
    Real.pi * Real.exp (729 / 400 : ℝ) ≤ (194380016144890849 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1457_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1457_endpointLower :
    (158601 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1457 / 1600 : ℝ) (729 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4853428277834907 / 250000000000000 : ℝ) (Real.pi * Real.exp (1457 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1457_product_lower
  have hD : Real.exp (Real.pi * Real.exp (729 / 400 : ℝ) - (1457 / 3200 : ℝ)) ≤
      (219274004059958489 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1457_denomUpper
    linarith [hpThetaJensenCell1457_product_upper]
  have hi : (1 / (219274004059958489 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (729 / 400 : ℝ) - (1457 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (219274004059958489 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (219274004059958489 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1457 / 3200 : ℝ) - Real.pi * Real.exp (729 / 400 : ℝ)) := by
    rw [show (1457 / 3200 : ℝ) - Real.pi * Real.exp (729 / 400 : ℝ) =
      -(Real.pi * Real.exp (729 / 400 : ℝ) - (1457 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1457 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1457 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1457_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (219274004059958489 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1457_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1457 / 1600 : ℝ) (729 / 800 : ℝ) ≤ (32681 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (729 / 400 : ℝ)) (194380016144890849 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (729 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1457_product_upper
  have hD : (1711563648992261029 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1457 / 800 : ℝ) - (729 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1457_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1457_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1457 / 800 : ℝ) - (729 / 1600 : ℝ)) ≤
      (1 / (1711563648992261029 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1711563648992261029 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((729 / 1600 : ℝ) - Real.pi * Real.exp (1457 / 800 : ℝ)) ≤
      (2 / (1711563648992261029 / 10000000000 : ℝ) : ℝ) := by
    rw [show (729 / 1600 : ℝ) - Real.pi * Real.exp (1457 / 800 : ℝ) =
      -(Real.pi * Real.exp (1457 / 800 : ℝ) - (729 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (194380016144890849 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (194380016144890849 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1457_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1457 / 1600 : ℝ) (729 / 800 : ℝ)) :
    (158601 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32681 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1457_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1457_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1458_leftExp :
    (6187307399 / 1000000000 : ℝ) ≤ Real.exp (729 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (729 / 400 : ℝ) (1058606187067 / 1000000000000 : ℝ)
    (6187307399 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1458_rightExp :
    Real.exp (1459 / 800 : ℝ) ≤ (30975231847 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1459 / 800 : ℝ) (6616547123 / 6250000000 : ℝ)
    (30975231847 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1458_denomUpper :
    Real.exp (95033446543912271 / 5000000000000000 : ℝ) ≤ (224600282961236767 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (95033446543912271 / 5000000000000000 : ℝ) (362228927171
    / 200000000000 : ℝ) (224600282961236767 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1458_denomLower :
    (175308515627227947 / 1000000000 : ℝ) ≤ Real.exp (2372757240779901 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2372757240779901 / 125000000000000 : ℝ) (904875539307 /
    500000000000 : ℝ) (175308515627227947 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1458_product_lower :
    (2429749428279901 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (729 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1458_leftExp
    (by norm_num : (0 : ℝ) ≤ (6187307399 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1458_product_upper :
    Real.pi * Real.exp (1459 / 800 : ℝ) ≤ (97311571543912271 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1458_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1458_endpointLower :
    (38811 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (729 / 800 : ℝ) (1459 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2429749428279901 / 125000000000000 : ℝ) (Real.pi * Real.exp (729 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1458_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1459 / 800 : ℝ) - (729 / 1600 : ℝ)) ≤
      (224600282961236767 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1458_denomUpper
    linarith [hpThetaJensenCell1458_product_upper]
  have hi : (1 / (224600282961236767 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1459 / 800 : ℝ) - (729 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (224600282961236767 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (224600282961236767 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((729 / 1600 : ℝ) - Real.pi * Real.exp (1459 / 800 : ℝ)) := by
    rw [show (729 / 1600 : ℝ) - Real.pi * Real.exp (1459 / 800 : ℝ) =
      -(Real.pi * Real.exp (1459 / 800 : ℝ) - (729 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (729 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (729 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1458_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (224600282961236767 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1458_endpointUpper :
    hpThetaJensenKernelEndpointUpper (729 / 800 : ℝ) (1459 / 1600 : ℝ) ≤ (159951 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1459 / 800 : ℝ)) (97311571543912271 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1459 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1458_product_upper
  have hD : (175308515627227947 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (729 / 400 : ℝ) - (1459 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1458_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1458_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (729 / 400 : ℝ) - (1459 / 3200 : ℝ)) ≤
      (1 / (175308515627227947 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (175308515627227947 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1459 / 3200 : ℝ) - Real.pi * Real.exp (729 / 400 : ℝ)) ≤
      (2 / (175308515627227947 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1459 / 3200 : ℝ) - Real.pi * Real.exp (729 / 400 : ℝ) =
      -(Real.pi * Real.exp (729 / 400 : ℝ) - (1459 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (97311571543912271 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (97311571543912271 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1458_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (729 / 800 : ℝ) (1459 / 1600 : ℝ)) :
    (38811 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (159951 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1458_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1458_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1459_leftExp :
    (61950463691 / 10000000000 : ℝ) ≤ Real.exp (1459 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1459 / 800 : ℝ) (1058647539679 / 1000000000000 : ℝ)
    (61950463691 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1459_rightExp :
    Real.exp (73 / 40 : ℝ) ≤ (3876746887 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 40 : ℝ) (1058688893907 / 1000000000000 : ℝ)
    (3876746887 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1459_denomUpper :
    Real.exp (11894199945470991 / 625000000000000 : ℝ) ≤ (115031467982358591 / 625000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (11894199945470991 / 625000000000000 : ℝ) (453126309319 /
    250000000000 : ℝ) (115031467982358591 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1459_denomLower :
    (1795668486991853341 / 10000000000 : ℝ) ≤ Real.exp (23757572640992009 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (23757572640992009 / 1250000000000000 : ℝ) (1811108911601
    / 1000000000000 : ℝ) (1795668486991853341 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1459_product_lower :
    (24327885140992009 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1459 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1459_leftExp
    (by norm_num : (0 : ℝ) ≤ (61950463691 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1459_product_upper :
    Real.pi * Real.exp (73 / 40 : ℝ) ≤ (12179160882970991 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1459_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1459_endpointLower :
    (151953 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1459 / 1600 : ℝ) (73 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24327885140992009 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1459 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1459_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 40 : ℝ) - (1459 / 3200 : ℝ)) ≤
      (115031467982358591 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1459_denomUpper
    linarith [hpThetaJensenCell1459_product_upper]
  have hi : (1 / (115031467982358591 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 40 : ℝ) - (1459 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (115031467982358591 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (115031467982358591 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1459 / 3200 : ℝ) - Real.pi * Real.exp (73 / 40 : ℝ)) := by
    rw [show (1459 / 3200 : ℝ) - Real.pi * Real.exp (73 / 40 : ℝ) =
      -(Real.pi * Real.exp (73 / 40 : ℝ) - (1459 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1459 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1459 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1459_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (115031467982358591 / 625000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1459_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1459 / 1600 : ℝ) (73 / 80 : ℝ) ≤ (31313 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 40 : ℝ)) (12179160882970991 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1459_product_upper
  have hD : (1795668486991853341 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1459 / 800 : ℝ) - (73 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell1459_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1459_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1459 / 800 : ℝ) - (73 / 160 : ℝ)) ≤
      (1 / (1795668486991853341 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1795668486991853341 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 160 : ℝ) - Real.pi * Real.exp (1459 / 800 : ℝ)) ≤
      (2 / (1795668486991853341 / 10000000000 : ℝ) : ℝ) := by
    rw [show (73 / 160 : ℝ) - Real.pi * Real.exp (1459 / 800 : ℝ) =
      -(Real.pi * Real.exp (1459 / 800 : ℝ) - (73 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12179160882970991 / 625000000000000 : ℝ) ^ 2 - 6 *
      (12179160882970991 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1459_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1459 / 1600 : ℝ) (73 / 80 : ℝ)) :
    (151953 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (31313 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1459_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1459_endpointUpper

def hpThetaJensenCellsBatch072Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2839 / 125000000 : ℝ)
  | 1 => (222427 / 10000000000 : ℝ)
  | 2 => (6807 / 312500000 : ℝ)
  | 3 => (213309 / 10000000000 : ℝ)
  | 4 => (104441 / 5000000000 : ℝ)
  | 5 => (204541 / 10000000000 : ℝ)
  | 6 => (50071 / 2500000000 : ℝ)
  | 7 => (19611 / 1000000000 : ℝ)
  | 8 => (192017 / 10000000000 : ℝ)
  | 9 => (47001 / 2500000000 : ℝ)
  | 10 => (184069 / 10000000000 : ℝ)
  | 11 => (18021 / 1000000000 : ℝ)
  | 12 => (44107 / 2500000000 : ℝ)
  | 13 => (2159 / 125000000 : ℝ)
  | 14 => (42271 / 2500000000 : ℝ)
  | 15 => (2069 / 125000000 : ℝ)
  | 16 => (81013 / 5000000000 : ℝ)
  | 17 => (158601 / 10000000000 : ℝ)
  | 18 => (38811 / 2500000000 : ℝ)
  | 19 => (151953 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch072Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (233881 / 10000000000 : ℝ)
  | 1 => (114527 / 5000000000 : ℝ)
  | 2 => (224321 / 10000000000 : ℝ)
  | 3 => (109839 / 5000000000 : ℝ)
  | 4 => (107563 / 5000000000 : ℝ)
  | 5 => (210661 / 10000000000 : ℝ)
  | 6 => (206283 / 10000000000 : ℝ)
  | 7 => (20199 / 1000000000 : ℝ)
  | 8 => (9889 / 500000000 : ℝ)
  | 9 => (48413 / 2500000000 : ℝ)
  | 10 => (47401 / 2500000000 : ℝ)
  | 11 => (46409 / 2500000000 : ℝ)
  | 12 => (36349 / 2000000000 : ℝ)
  | 13 => (17793 / 1000000000 : ℝ)
  | 14 => (17419 / 1000000000 : ℝ)
  | 15 => (170523 / 10000000000 : ℝ)
  | 16 => (166929 / 10000000000 : ℝ)
  | 17 => (32681 / 2000000000 : ℝ)
  | 18 => (159951 / 10000000000 : ℝ)
  | 19 => (31313 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch072_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch072Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch072Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1440_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1441_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1442_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1443_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1444_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1445_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1446_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1447_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1448_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1449_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1450_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1451_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1452_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1453_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1454_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1455_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1456_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1457_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1458_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1459_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper] at h ⊢
    exact h

end HodgeProofHP
