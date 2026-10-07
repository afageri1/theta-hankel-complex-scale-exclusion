import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1420_leftExp :
    (59002811361 / 10000000000 : ℝ) ≤ Real.exp (71 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (71 / 40 : ℝ) (1057035984181 / 1000000000000 : ℝ)
    (59002811361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1420_rightExp :
    Real.exp (1421 / 800 : ℝ) ≤ (29538305497 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1421 / 800 : ℝ) (1057077275457 / 1000000000000 : ℝ)
    (29538305497 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1420_denomUpper :
    Real.exp (90578583781236721 / 5000000000000000 : ℝ) ≤ (36857496019379889 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (90578583781236721 / 5000000000000000 : ℝ) (1761412684317
    / 1000000000000 : ℝ) (36857496019379889 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1420_denomLower :
    (360013261887100507 / 5000000000 : ℝ) ≤ Real.exp (22615266893653339 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22615266893653339 / 1250000000000000 : ℝ) (1760119443443
    / 1000000000000 : ℝ) (360013261887100507 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1420_product_lower :
    (23170345018653339 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (71 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1420_leftExp
    (by norm_num : (0 : ℝ) ≤ (59002811361 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1420_product_upper :
    Real.pi * Real.exp (1421 / 800 : ℝ) ≤ (92797333781236721 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1420_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1420_endpointLower :
    (342713 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 80 : ℝ) (1421 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23170345018653339 / 1250000000000000 : ℝ) (Real.pi * Real.exp (71 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1420_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1421 / 800 : ℝ) - (71 / 160 : ℝ)) ≤
      (36857496019379889 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1420_denomUpper
    linarith [hpThetaJensenCell1420_product_upper]
  have hi : (1 / (36857496019379889 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1421 / 800 : ℝ) - (71 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (36857496019379889 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (36857496019379889 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((71 / 160 : ℝ) - Real.pi * Real.exp (1421 / 800 : ℝ)) := by
    rw [show (71 / 160 : ℝ) - Real.pi * Real.exp (1421 / 800 : ℝ) =
      -(Real.pi * Real.exp (1421 / 800 : ℝ) - (71 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (71 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (71 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1420_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (36857496019379889 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1420_endpointUpper :
    hpThetaJensenKernelEndpointUpper (71 / 80 : ℝ) (1421 / 1600 : ℝ) ≤ (88177 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1421 / 800 : ℝ)) (92797333781236721 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1421 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1420_product_upper
  have hD : (360013261887100507 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (71 / 40 : ℝ) - (1421 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1420_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1420_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (71 / 40 : ℝ) - (1421 / 3200 : ℝ)) ≤
      (1 / (360013261887100507 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (360013261887100507 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1421 / 3200 : ℝ) - Real.pi * Real.exp (71 / 40 : ℝ)) ≤
      (2 / (360013261887100507 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1421 / 3200 : ℝ) - Real.pi * Real.exp (71 / 40 : ℝ) =
      -(Real.pi * Real.exp (71 / 40 : ℝ) - (1421 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (92797333781236721 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (92797333781236721 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1420_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (71 / 80 : ℝ) (1421 / 1600 : ℝ)) :
    (342713 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (88177 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1420_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1420_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1421_leftExp :
    (59076610991 / 10000000000 : ℝ) ≤ Real.exp (1421 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1421 / 800 : ℝ) (16516832429 / 15625000000 : ℝ)
    (59076610991 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1421_rightExp :
    Real.exp (711 / 400 : ℝ) ≤ (5915050293 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (711 / 400 : ℝ) (132139821043 / 125000000000 : ℝ)
    (5915050293 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1421_denomUpper :
    Real.exp (18138618095136749 / 1000000000000000 : ℝ) ≤ (47139151979480787 / 625000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (18138618095136749 / 1000000000000000 : ℝ) (881336860077
    / 500000000000 : ℝ) (47139151979480787 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1421_denomLower :
    (368342496394248377 / 5000000000 : ℝ) ≤ Real.exp (22643857309554709 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22643857309554709 / 1250000000000000 : ℝ) (176137795683
    / 100000000000 : ℝ) (368342496394248377 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1421_product_lower :
    (23199326059554709 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1421 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1421_leftExp
    (by norm_num : (0 : ℝ) ≤ (59076610991 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1421_product_upper :
    Real.pi * Real.exp (711 / 400 : ℝ) ≤ (18582680595136749 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1421_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1421_endpointLower :
    (335829 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1421 / 1600 : ℝ) (711 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23199326059554709 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1421 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1421_product_lower
  have hD : Real.exp (Real.pi * Real.exp (711 / 400 : ℝ) - (1421 / 3200 : ℝ)) ≤
      (47139151979480787 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1421_denomUpper
    linarith [hpThetaJensenCell1421_product_upper]
  have hi : (1 / (47139151979480787 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (711 / 400 : ℝ) - (1421 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (47139151979480787 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (47139151979480787 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1421 / 3200 : ℝ) - Real.pi * Real.exp (711 / 400 : ℝ)) := by
    rw [show (1421 / 3200 : ℝ) - Real.pi * Real.exp (711 / 400 : ℝ) =
      -(Real.pi * Real.exp (711 / 400 : ℝ) - (1421 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1421 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1421 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1421_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (47139151979480787 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1421_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1421 / 1600 : ℝ) (711 / 800 : ℝ) ≤ (345633 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (711 / 400 : ℝ)) (18582680595136749 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (711 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1421_product_upper
  have hD : (368342496394248377 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1421 / 800 : ℝ) - (711 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1421_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1421_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1421 / 800 : ℝ) - (711 / 1600 : ℝ)) ≤
      (1 / (368342496394248377 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (368342496394248377 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((711 / 1600 : ℝ) - Real.pi * Real.exp (1421 / 800 : ℝ)) ≤
      (2 / (368342496394248377 / 5000000000 : ℝ) : ℝ) := by
    rw [show (711 / 1600 : ℝ) - Real.pi * Real.exp (1421 / 800 : ℝ) =
      -(Real.pi * Real.exp (1421 / 800 : ℝ) - (711 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18582680595136749 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (18582680595136749 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1421_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1421 / 1600 : ℝ) (711 / 800 : ℝ)) :
    (335829 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (345633 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1421_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1421_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1422_leftExp :
    (59150502927 / 10000000000 : ℝ) ≤ Real.exp (711 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (711 / 400 : ℝ) (1057118568343 / 1000000000000 : ℝ)
    (59150502927 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1422_rightExp :
    Real.exp (1423 / 800 : ℝ) ≤ (5922448729 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1423 / 800 : ℝ) (211431972569 / 200000000000 : ℝ)
    (5922448729 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1422_denomUpper :
    Real.exp (18161548469885297 / 1000000000000000 : ℝ) ≤ (771720937639488941 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (18161548469885297 / 1000000000000000 : ℝ) (88196862967 /
    50000000000 : ℝ) (771720937639488941 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1422_denomLower :
    (94218841023105213 / 1250000000 : ℝ) ≤ Real.exp (22672483973929973 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22672483973929973 / 1250000000000000 : ℝ) (881319483699
    / 500000000000 : ℝ) (94218841023105213 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1422_product_lower :
    (23228343348929973 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (711 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1422_leftExp
    (by norm_num : (0 : ℝ) ≤ (59150502927 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1422_product_upper :
    Real.pi * Real.exp (1423 / 800 : ℝ) ≤ (18605923469885297 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1422_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1422_endpointLower :
    (164537 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (711 / 800 : ℝ) (1423 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23228343348929973 / 1250000000000000 : ℝ) (Real.pi * Real.exp (711 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1422_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1423 / 800 : ℝ) - (711 / 1600 : ℝ)) ≤
      (771720937639488941 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1422_denomUpper
    linarith [hpThetaJensenCell1422_product_upper]
  have hi : (1 / (771720937639488941 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1423 / 800 : ℝ) - (711 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (771720937639488941 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (771720937639488941 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((711 / 1600 : ℝ) - Real.pi * Real.exp (1423 / 800 : ℝ)) := by
    rw [show (711 / 1600 : ℝ) - Real.pi * Real.exp (1423 / 800 : ℝ) =
      -(Real.pi * Real.exp (1423 / 800 : ℝ) - (711 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (711 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (711 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1422_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (771720937639488941 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1422_endpointUpper :
    hpThetaJensenKernelEndpointUpper (711 / 800 : ℝ) (1423 / 1600 : ℝ) ≤ (33869 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1423 / 800 : ℝ)) (18605923469885297 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1423 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1422_product_upper
  have hD : (94218841023105213 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (711 / 400 : ℝ) - (1423 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1422_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1422_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (711 / 400 : ℝ) - (1423 / 3200 : ℝ)) ≤
      (1 / (94218841023105213 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (94218841023105213 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1423 / 3200 : ℝ) - Real.pi * Real.exp (711 / 400 : ℝ)) ≤
      (2 / (94218841023105213 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1423 / 3200 : ℝ) - Real.pi * Real.exp (711 / 400 : ℝ) =
      -(Real.pi * Real.exp (711 / 400 : ℝ) - (1423 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18605923469885297 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (18605923469885297 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1422_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (711 / 800 : ℝ) (1423 / 1600 : ℝ)) :
    (164537 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (33869 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1422_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1422_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1423_leftExp :
    (59224487287 / 10000000000 : ℝ) ≤ Real.exp (1423 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1423 / 800 : ℝ) (264289965711 / 250000000000 : ℝ)
    (59224487287 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1423_rightExp :
    Real.exp (89 / 50 : ℝ) ≤ (14824641047 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89 / 50 : ℝ) (1057201158959 / 1000000000000 : ℝ)
    (14824641047 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1423_denomUpper :
    Real.exp (45461269790767871 / 2500000000000000 : ℝ) ≤ (394822094901477647 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (45461269790767871 / 2500000000000000 : ℝ) (882601653969
    / 500000000000 : ℝ) (394822094901477647 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1423_denomLower :
    (192808548589625259 / 2500000000 : ℝ) ≤ Real.exp (22701146933117613 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22701146933117613 / 1250000000000000 : ℝ) (110243905079
    / 62500000000 : ℝ) (192808548589625259 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1423_product_lower :
    (23257396933117613 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1423 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1423_leftExp
    (by norm_num : (0 : ℝ) ≤ (59224487287 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1423_product_upper :
    Real.pi * Real.exp (89 / 50 : ℝ) ≤ (46572988540767871 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1423_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1423_endpointLower :
    (64489 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1423 / 1600 : ℝ) (89 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23257396933117613 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1423 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1423_product_lower
  have hD : Real.exp (Real.pi * Real.exp (89 / 50 : ℝ) - (1423 / 3200 : ℝ)) ≤
      (394822094901477647 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1423_denomUpper
    linarith [hpThetaJensenCell1423_product_upper]
  have hi : (1 / (394822094901477647 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (89 / 50 : ℝ) - (1423 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (394822094901477647 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (394822094901477647 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1423 / 3200 : ℝ) - Real.pi * Real.exp (89 / 50 : ℝ)) := by
    rw [show (1423 / 3200 : ℝ) - Real.pi * Real.exp (89 / 50 : ℝ) =
      -(Real.pi * Real.exp (89 / 50 : ℝ) - (1423 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1423 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1423 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1423_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (394822094901477647 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1423_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1423 / 1600 : ℝ) (89 / 100 : ℝ) ≤ (331877 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (89 / 50 : ℝ)) (46572988540767871 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (89 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1423_product_upper
  have hD : (192808548589625259 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1423 / 800 : ℝ) - (89 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1423_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1423_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1423 / 800 : ℝ) - (89 / 200 : ℝ)) ≤
      (1 / (192808548589625259 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (192808548589625259 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((89 / 200 : ℝ) - Real.pi * Real.exp (1423 / 800 : ℝ)) ≤
      (2 / (192808548589625259 / 2500000000 : ℝ) : ℝ) := by
    rw [show (89 / 200 : ℝ) - Real.pi * Real.exp (1423 / 800 : ℝ) =
      -(Real.pi * Real.exp (1423 / 800 : ℝ) - (89 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46572988540767871 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (46572988540767871 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1423_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1423 / 1600 : ℝ) (89 / 100 : ℝ)) :
    (64489 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (331877 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1423_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1423_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1424_leftExp :
    (11859712837 / 2000000000 : ℝ) ≤ Real.exp (89 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (89 / 50 : ℝ) (528600579479 / 500000000000 : ℝ)
    (11859712837 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1424_rightExp :
    Real.exp (57 / 32 : ℝ) ≤ (2968636687 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 32 : ℝ) (528621228343 / 500000000000 : ℝ)
    (2968636687 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1424_denomUpper :
    Real.exp (9103748235422391 / 500000000000000 : ℝ) ≤ (808007229505581343 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (9103748235422391 / 500000000000000 : ℝ) (1766471872063 /
    1000000000000 : ℝ) (808007229505581343 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1424_denomLower :
    (789146136045906247 / 10000000000 : ℝ) ≤ Real.exp (4545969246377063 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4545969246377063 / 250000000000000 : ℝ) (441292126123 /
    250000000000 : ℝ) (789146136045906247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1424_product_lower :
    (4657297371377063 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (89 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1424_leftExp
    (by norm_num : (0 : ℝ) ≤ (11859712837 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1424_product_upper :
    Real.pi * Real.exp (57 / 32 : ℝ) ≤ (9326248235422391 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1424_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1424_endpointLower :
    (15797 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 100 : ℝ) (57 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4657297371377063 / 250000000000000 : ℝ) (Real.pi * Real.exp (89 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1424_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 32 : ℝ) - (89 / 200 : ℝ)) ≤
      (808007229505581343 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1424_denomUpper
    linarith [hpThetaJensenCell1424_product_upper]
  have hi : (1 / (808007229505581343 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 32 : ℝ) - (89 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (808007229505581343 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (808007229505581343 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((89 / 200 : ℝ) - Real.pi * Real.exp (57 / 32 : ℝ)) := by
    rw [show (89 / 200 : ℝ) - Real.pi * Real.exp (57 / 32 : ℝ) =
      -(Real.pi * Real.exp (57 / 32 : ℝ) - (89 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (89 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (89 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1424_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (808007229505581343 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1424_endpointUpper :
    hpThetaJensenKernelEndpointUpper (89 / 100 : ℝ) (57 / 64 : ℝ) ≤ (40649 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 32 : ℝ)) (9326248235422391 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1424_product_upper
  have hD : (789146136045906247 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (89 / 50 : ℝ) - (57 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1424_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1424_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (89 / 50 : ℝ) - (57 / 128 : ℝ)) ≤
      (1 / (789146136045906247 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (789146136045906247 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 128 : ℝ) - Real.pi * Real.exp (89 / 50 : ℝ)) ≤
      (2 / (789146136045906247 / 10000000000 : ℝ) : ℝ) := by
    rw [show (57 / 128 : ℝ) - Real.pi * Real.exp (89 / 50 : ℝ) =
      -(Real.pi * Real.exp (89 / 50 : ℝ) - (57 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9326248235422391 / 500000000000000 : ℝ) ^ 2 - 6 *
      (9326248235422391 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1424_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (89 / 100 : ℝ) (57 / 64 : ℝ)) :
    (15797 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (40649 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1424_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1424_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1425_leftExp :
    (59372733737 / 10000000000 : ℝ) ≤ Real.exp (57 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 32 : ℝ) (211448491337 / 200000000000 : ℝ)
    (59372733737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1425_rightExp :
    Real.exp (713 / 400 : ℝ) ≤ (59446996061 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (713 / 400 : ℝ) (528641878013 / 500000000000 : ℝ)
    (59446996061 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1425_denomUpper :
    Real.exp (182305141696265173 / 10000000000000000 : ℝ) ≤ (826821395256733023 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (182305141696265173 / 10000000000000000 : ℝ)
    (883871478913 / 500000000000 : ℝ) (826821395256733023 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1425_denomLower :
    (25234299612626261 / 312500000 : ℝ) ≤ Real.exp (22758581915786163 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22758581915786163 / 1250000000000000 : ℝ) (441609260799
    / 250000000000 : ℝ) (25234299612626261 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1425_product_lower :
    (23315613165786163 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1425_leftExp
    (by norm_num : (0 : ℝ) ≤ (59372733737 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1425_product_upper :
    Real.pi * Real.exp (713 / 400 : ℝ) ≤ (186758266696265173 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1425_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1425_endpointLower :
    (154779 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 64 : ℝ) (713 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23315613165786163 / 1250000000000000 : ℝ) (Real.pi * Real.exp (57 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1425_product_lower
  have hD : Real.exp (Real.pi * Real.exp (713 / 400 : ℝ) - (57 / 128 : ℝ)) ≤
      (826821395256733023 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1425_denomUpper
    linarith [hpThetaJensenCell1425_product_upper]
  have hi : (1 / (826821395256733023 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (713 / 400 : ℝ) - (57 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (826821395256733023 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (826821395256733023 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 128 : ℝ) - Real.pi * Real.exp (713 / 400 : ℝ)) := by
    rw [show (57 / 128 : ℝ) - Real.pi * Real.exp (713 / 400 : ℝ) =
      -(Real.pi * Real.exp (713 / 400 : ℝ) - (57 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1425_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (826821395256733023 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1425_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 64 : ℝ) (713 / 800 : ℝ) ≤ (39829 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (713 / 400 : ℝ)) (186758266696265173 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (713 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1425_product_upper
  have hD : (25234299612626261 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 32 : ℝ) - (713 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1425_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1425_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 32 : ℝ) - (713 / 1600 : ℝ)) ≤
      (1 / (25234299612626261 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (25234299612626261 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((713 / 1600 : ℝ) - Real.pi * Real.exp (57 / 32 : ℝ)) ≤
      (2 / (25234299612626261 / 312500000 : ℝ) : ℝ) := by
    rw [show (713 / 1600 : ℝ) - Real.pi * Real.exp (57 / 32 : ℝ) =
      -(Real.pi * Real.exp (57 / 32 : ℝ) - (713 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (186758266696265173 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (186758266696265173 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1425_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 64 : ℝ) (713 / 800 : ℝ)) :
    (154779 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (39829 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1425_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1425_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1426_leftExp :
    (29723498029 / 5000000000 : ℝ) ≤ Real.exp (713 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (713 / 400 : ℝ) (42291350241 / 40000000000 : ℝ)
    (29723498029 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1426_rightExp :
    Real.exp (1427 / 800 : ℝ) ≤ (14880337817 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1427 / 800 : ℝ) (1057325056979 / 1000000000000 : ℝ)
    (14880337817 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1426_denomUpper :
    Real.exp (45633902623522481 / 2500000000000000 : ℝ) ≤ (846098331937856357 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (45633902623522481 / 2500000000000000 : ℝ) (3455110491 /
    1953125000 : ℝ) (846098331937856357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1426_denomLower :
    (165259976079351871 / 2000000000 : ℝ) ≤ Real.exp (11393677014990271 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11393677014990271 / 625000000000000 : ℝ) (27620439117 /
    15625000000 : ℝ) (165259976079351871 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1426_product_lower :
    (11672387952490271 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (713 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1426_leftExp
    (by norm_num : (0 : ℝ) ≤ (29723498029 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1426_product_upper :
    Real.pi * Real.exp (1427 / 800 : ℝ) ≤ (46747965123522481 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1426_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1426_endpointLower :
    (60659 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (713 / 800 : ℝ) (1427 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11672387952490271 / 625000000000000 : ℝ) (Real.pi * Real.exp (713 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1426_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1427 / 800 : ℝ) - (713 / 1600 : ℝ)) ≤
      (846098331937856357 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1426_denomUpper
    linarith [hpThetaJensenCell1426_product_upper]
  have hi : (1 / (846098331937856357 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1427 / 800 : ℝ) - (713 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (846098331937856357 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (846098331937856357 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((713 / 1600 : ℝ) - Real.pi * Real.exp (1427 / 800 : ℝ)) := by
    rw [show (713 / 1600 : ℝ) - Real.pi * Real.exp (1427 / 800 : ℝ) =
      -(Real.pi * Real.exp (1427 / 800 : ℝ) - (713 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (713 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (713 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1426_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (846098331937856357 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1426_endpointUpper :
    hpThetaJensenKernelEndpointUpper (713 / 800 : ℝ) (1427 / 1600 : ℝ) ≤ (62439 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1427 / 800 : ℝ)) (46747965123522481 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1427 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1426_product_upper
  have hD : (165259976079351871 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (713 / 400 : ℝ) - (1427 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1426_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1426_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (713 / 400 : ℝ) - (1427 / 3200 : ℝ)) ≤
      (1 / (165259976079351871 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (165259976079351871 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1427 / 3200 : ℝ) - Real.pi * Real.exp (713 / 400 : ℝ)) ≤
      (2 / (165259976079351871 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1427 / 3200 : ℝ) - Real.pi * Real.exp (713 / 400 : ℝ) =
      -(Real.pi * Real.exp (713 / 400 : ℝ) - (1427 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46747965123522481 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (46747965123522481 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1426_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (713 / 800 : ℝ) (1427 / 1600 : ℝ)) :
    (60659 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (62439 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1426_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1426_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1427_leftExp :
    (11904270253 / 2000000000 : ℝ) ≤ Real.exp (1427 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1427 / 800 : ℝ) (528662528489 / 500000000000 : ℝ)
    (11904270253 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1427_rightExp :
    Real.exp (357 / 200 : ℝ) ≤ (29797899739 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (357 / 200 : ℝ) (528683179773 / 500000000000 : ℝ)
    (29797899739 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1427_denomUpper :
    Real.exp (91383185734744227 / 5000000000000000 : ℝ) ≤ (216462499693466849 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (91383185734744227 / 5000000000000000 : ℝ) (221286589867
    / 125000000000 : ℝ) (216462499693466849 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1427_denomLower :
    (211391162976682201 / 2500000000 : ℝ) ≤ Real.exp (4563232524082847 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4563232524082847 / 250000000000000 : ℝ) (176898169153 /
    100000000000 : ℝ) (211391162976682201 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1427_product_lower :
    (4674795024082847 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1427 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1427_leftExp
    (by norm_num : (0 : ℝ) ≤ (11904270253 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1427_product_upper :
    Real.pi * Real.exp (357 / 200 : ℝ) ≤ (93612873234744227 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1427_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1427_endpointLower :
    (297151 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1427 / 1600 : ℝ) (357 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4674795024082847 / 250000000000000 : ℝ) (Real.pi * Real.exp (1427 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1427_product_lower
  have hD : Real.exp (Real.pi * Real.exp (357 / 200 : ℝ) - (1427 / 3200 : ℝ)) ≤
      (216462499693466849 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1427_denomUpper
    linarith [hpThetaJensenCell1427_product_upper]
  have hi : (1 / (216462499693466849 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (357 / 200 : ℝ) - (1427 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (216462499693466849 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (216462499693466849 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1427 / 3200 : ℝ) - Real.pi * Real.exp (357 / 200 : ℝ)) := by
    rw [show (1427 / 3200 : ℝ) - Real.pi * Real.exp (357 / 200 : ℝ) =
      -(Real.pi * Real.exp (357 / 200 : ℝ) - (1427 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1427 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1427 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1427_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (216462499693466849 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1427_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1427 / 1600 : ℝ) (357 / 400 : ℝ) ≤ (305879 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (357 / 200 : ℝ)) (93612873234744227 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (357 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1427_product_upper
  have hD : (211391162976682201 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1427 / 800 : ℝ) - (357 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1427_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1427_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1427 / 800 : ℝ) - (357 / 800 : ℝ)) ≤
      (1 / (211391162976682201 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (211391162976682201 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((357 / 800 : ℝ) - Real.pi * Real.exp (1427 / 800 : ℝ)) ≤
      (2 / (211391162976682201 / 2500000000 : ℝ) : ℝ) := by
    rw [show (357 / 800 : ℝ) - Real.pi * Real.exp (1427 / 800 : ℝ) =
      -(Real.pi * Real.exp (1427 / 800 : ℝ) - (357 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (93612873234744227 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (93612873234744227 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1427_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1427 / 1600 : ℝ) (357 / 400 : ℝ)) :
    (297151 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (305879 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1427_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1427_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1428_leftExp :
    (2383831979 / 400000000 : ℝ) ≤ Real.exp (357 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (357 / 200 : ℝ) (211473271909 / 200000000000 : ℝ)
    (2383831979 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1428_rightExp :
    Real.exp (1429 / 800 : ℝ) ≤ (11934068161 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1429 / 800 : ℝ) (528703831863 / 500000000000 : ℝ)
    (11934068161 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1428_denomUpper :
    Real.exp (36599484996120473 / 2000000000000000 : ℝ) ≤ (443044338765326993 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (36599484996120473 / 2000000000000000 : ℝ) (1771571406603
    / 1000000000000 : ℝ) (443044338765326993 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1428_denomLower :
    (138448616618719 / 1600000 : ℝ) ≤ Real.exp (913800309321321 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (913800309321321 / 50000000000000 : ℝ) (1770257813501 /
    1000000000000 : ℝ) (138448616618719 / 1600000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1428_product_lower :
    (936128434321321 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (357 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1428_leftExp
    (by norm_num : (0 : ℝ) ≤ (2383831979 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1428_product_upper :
    Real.pi * Real.exp (1429 / 800 : ℝ) ≤ (37491984996120473 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1428_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1428_endpointLower :
    (145561 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (357 / 400 : ℝ) (1429 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (936128434321321 / 50000000000000 : ℝ) (Real.pi * Real.exp (357 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1428_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1429 / 800 : ℝ) - (357 / 800 : ℝ)) ≤
      (443044338765326993 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1428_denomUpper
    linarith [hpThetaJensenCell1428_product_upper]
  have hi : (1 / (443044338765326993 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1429 / 800 : ℝ) - (357 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (443044338765326993 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (443044338765326993 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((357 / 800 : ℝ) - Real.pi * Real.exp (1429 / 800 : ℝ)) := by
    rw [show (357 / 800 : ℝ) - Real.pi * Real.exp (1429 / 800 : ℝ) =
      -(Real.pi * Real.exp (1429 / 800 : ℝ) - (357 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (357 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (357 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1428_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (443044338765326993 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1428_endpointUpper :
    hpThetaJensenKernelEndpointUpper (357 / 400 : ℝ) (1429 / 1600 : ℝ) ≤ (149841 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1429 / 800 : ℝ)) (37491984996120473 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1429 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1428_product_upper
  have hD : (138448616618719 / 1600000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (357 / 200 : ℝ) - (1429 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1428_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1428_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (357 / 200 : ℝ) - (1429 / 3200 : ℝ)) ≤
      (1 / (138448616618719 / 1600000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (138448616618719 / 1600000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1429 / 3200 : ℝ) - Real.pi * Real.exp (357 / 200 : ℝ)) ≤
      (2 / (138448616618719 / 1600000 : ℝ) : ℝ) := by
    rw [show (1429 / 3200 : ℝ) - Real.pi * Real.exp (357 / 200 : ℝ) =
      -(Real.pi * Real.exp (357 / 200 : ℝ) - (1429 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (37491984996120473 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (37491984996120473 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1428_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (357 / 400 : ℝ) (1429 / 1600 : ℝ)) :
    (145561 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (149841 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1428_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1428_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1429_leftExp :
    (59670340803 / 10000000000 : ℝ) ≤ Real.exp (1429 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1429 / 800 : ℝ) (42296306549 / 40000000000 : ℝ)
    (59670340803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1429_rightExp :
    Real.exp (143 / 80 : ℝ) ≤ (59744975369 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (143 / 80 : ℝ) (13218112119 / 12500000000 : ℝ)
    (59744975369 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1429_denomUpper :
    Real.exp (183228771404422817 / 10000000000000000 : ℝ) ≤ (906826983911521577 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (183228771404422817 / 10000000000000000 : ℝ)
    (1772852640653 / 1000000000000 : ℝ) (906826983911521577 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1429_denomLower :
    (35421190420537109 / 400000000 : ℝ) ≤ Real.exp (22873889412997297 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22873889412997297 / 1250000000000000 : ℝ) (44288411889 /
    25000000000 : ℝ) (35421190420537109 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1429_product_lower :
    (23432483162997297 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1429 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1429_leftExp
    (by norm_num : (0 : ℝ) ≤ (59670340803 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1429_product_upper :
    Real.pi * Real.exp (143 / 80 : ℝ) ≤ (187694396404422817 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1429_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1429_endpointLower :
    (35651 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1429 / 1600 : ℝ) (143 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23432483162997297 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1429 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1429_product_lower
  have hD : Real.exp (Real.pi * Real.exp (143 / 80 : ℝ) - (1429 / 3200 : ℝ)) ≤
      (906826983911521577 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1429_denomUpper
    linarith [hpThetaJensenCell1429_product_upper]
  have hi : (1 / (906826983911521577 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (143 / 80 : ℝ) - (1429 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (906826983911521577 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (906826983911521577 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1429 / 3200 : ℝ) - Real.pi * Real.exp (143 / 80 : ℝ)) := by
    rw [show (1429 / 3200 : ℝ) - Real.pi * Real.exp (143 / 80 : ℝ) =
      -(Real.pi * Real.exp (143 / 80 : ℝ) - (1429 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1429 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1429 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1429_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (906826983911521577 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1429_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1429 / 1600 : ℝ) (143 / 160 : ℝ) ≤ (146801 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (143 / 80 : ℝ)) (187694396404422817 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (143 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1429_product_upper
  have hD : (35421190420537109 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1429 / 800 : ℝ) - (143 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1429_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1429_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1429 / 800 : ℝ) - (143 / 320 : ℝ)) ≤
      (1 / (35421190420537109 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35421190420537109 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((143 / 320 : ℝ) - Real.pi * Real.exp (1429 / 800 : ℝ)) ≤
      (2 / (35421190420537109 / 400000000 : ℝ) : ℝ) := by
    rw [show (143 / 320 : ℝ) - Real.pi * Real.exp (1429 / 800 : ℝ) =
      -(Real.pi * Real.exp (1429 / 800 : ℝ) - (143 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (187694396404422817 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (187694396404422817 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1429_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1429 / 1600 : ℝ) (143 / 160 : ℝ)) :
    (35651 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (146801 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1429_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1429_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1430_leftExp :
    (29872487683 / 5000000000 : ℝ) ≤ Real.exp (143 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (143 / 80 : ℝ) (1057448969519 / 1000000000000 : ℝ)
    (29872487683 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1430_rightExp :
    Real.exp (1431 / 800 : ℝ) ≤ (59819703283 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1431 / 800 : ℝ) (1057490276927 / 1000000000000 : ℝ)
    (59819703283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1430_denomUpper :
    Real.exp (183460411095949819 / 10000000000000000 : ℝ) ≤ (928077873460750809 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (183460411095949819 / 10000000000000000 : ℝ)
    (1774136427243 / 1000000000000 : ℝ) (928077873460750809 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1430_denomLower :
    (453127489390992921 / 5000000000 : ℝ) ≤ Real.exp (11451403853126417 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11451403853126417 / 625000000000000 : ℝ) (1772817683917
    / 1000000000000 : ℝ) (453127489390992921 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1430_product_lower :
    (11730896040626417 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (143 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1430_leftExp
    (by norm_num : (0 : ℝ) ≤ (29872487683 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1430_product_upper :
    Real.pi * Real.exp (1431 / 800 : ℝ) ≤ (187929161095949819 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1430_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1430_endpointLower :
    (55881 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (143 / 160 : ℝ) (1431 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11730896040626417 / 625000000000000 : ℝ) (Real.pi * Real.exp (143 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1430_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1431 / 800 : ℝ) - (143 / 320 : ℝ)) ≤
      (928077873460750809 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1430_denomUpper
    linarith [hpThetaJensenCell1430_product_upper]
  have hi : (1 / (928077873460750809 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1431 / 800 : ℝ) - (143 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (928077873460750809 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (928077873460750809 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((143 / 320 : ℝ) - Real.pi * Real.exp (1431 / 800 : ℝ)) := by
    rw [show (143 / 320 : ℝ) - Real.pi * Real.exp (1431 / 800 : ℝ) =
      -(Real.pi * Real.exp (1431 / 800 : ℝ) - (143 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (143 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (143 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1430_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (928077873460750809 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1430_endpointUpper :
    hpThetaJensenKernelEndpointUpper (143 / 160 : ℝ) (1431 / 1600 : ℝ) ≤ (287637 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1431 / 800 : ℝ)) (187929161095949819 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1431 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1430_product_upper
  have hD : (453127489390992921 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (143 / 80 : ℝ) - (1431 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1430_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1430_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (143 / 80 : ℝ) - (1431 / 3200 : ℝ)) ≤
      (1 / (453127489390992921 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (453127489390992921 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1431 / 3200 : ℝ) - Real.pi * Real.exp (143 / 80 : ℝ)) ≤
      (2 / (453127489390992921 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1431 / 3200 : ℝ) - Real.pi * Real.exp (143 / 80 : ℝ) =
      -(Real.pi * Real.exp (143 / 80 : ℝ) - (1431 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (187929161095949819 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (187929161095949819 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1430_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (143 / 160 : ℝ) (1431 / 1600 : ℝ)) :
    (55881 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (287637 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1430_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1430_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1431_leftExp :
    (747746291 / 125000000 : ℝ) ≤ Real.exp (1431 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1431 / 800 : ℝ) (528745138463 / 500000000000 : ℝ)
    (747746291 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1431_rightExp :
    Real.exp (179 / 100 : ℝ) ≤ (7486815583 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (179 / 100 : ℝ) (1057531585947 / 1000000000000 : ℝ)
    (7486815583 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1431_denomUpper :
    Real.exp (22961543052843719 / 1250000000000000 : ℝ) ≤ (474927327103969573 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (22961543052843719 / 1250000000000000 : ℝ) (355084554523
    / 200000000000 : ℝ) (474927327103969573 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1431_denomLower :
    (927492456834527141 / 10000000000 : ℝ) ≤ Real.exp (286647033229409 / 15625000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (286647033229409 / 15625000000000 : ℝ) (1774101444779 /
    1000000000000 : ℝ) (927492456834527141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1431_product_lower :
    (293639220729409 / 15625000000000 : ℝ) ≤ Real.pi * Real.exp (1431 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1431_leftExp
    (by norm_num : (0 : ℝ) ≤ (747746291 / 125000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1431_product_upper :
    Real.pi * Real.exp (179 / 100 : ℝ) ≤ (23520527427843719 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1431_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1431_endpointLower :
    (17107 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (1431 / 1600 : ℝ) (179 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (293639220729409 / 15625000000000 : ℝ) (Real.pi * Real.exp (1431 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1431_product_lower
  have hD : Real.exp (Real.pi * Real.exp (179 / 100 : ℝ) - (1431 / 3200 : ℝ)) ≤
      (474927327103969573 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1431_denomUpper
    linarith [hpThetaJensenCell1431_product_upper]
  have hi : (1 / (474927327103969573 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (179 / 100 : ℝ) - (1431 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (474927327103969573 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (474927327103969573 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1431 / 3200 : ℝ) - Real.pi * Real.exp (179 / 100 : ℝ)) := by
    rw [show (1431 / 3200 : ℝ) - Real.pi * Real.exp (179 / 100 : ℝ) =
      -(Real.pi * Real.exp (179 / 100 : ℝ) - (1431 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1431 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1431 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1431_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (474927327103969573 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1431_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1431 / 1600 : ℝ) (179 / 200 : ℝ) ≤ (56357 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (179 / 100 : ℝ)) (23520527427843719 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (179 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1431_product_upper
  have hD : (927492456834527141 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1431 / 800 : ℝ) - (179 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1431_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1431_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1431 / 800 : ℝ) - (179 / 400 : ℝ)) ≤
      (1 / (927492456834527141 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (927492456834527141 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((179 / 400 : ℝ) - Real.pi * Real.exp (1431 / 800 : ℝ)) ≤
      (2 / (927492456834527141 / 10000000000 : ℝ) : ℝ) := by
    rw [show (179 / 400 : ℝ) - Real.pi * Real.exp (1431 / 800 : ℝ) =
      -(Real.pi * Real.exp (1431 / 800 : ℝ) - (179 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23520527427843719 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (23520527427843719 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1431_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1431 / 1600 : ℝ) (179 / 200 : ℝ)) :
    (17107 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (56357 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1431_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1431_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1432_leftExp :
    (29947262331 / 5000000000 : ℝ) ≤ Real.exp (179 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (179 / 100 : ℝ) (528765792973 / 500000000000 : ℝ)
    (29947262331 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1432_rightExp :
    Real.exp (1433 / 800 : ℝ) ≤ (59969439633 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1433 / 800 : ℝ) (528786448291 / 500000000000 : ℝ)
    (59969439633 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1432_denomUpper :
    Real.exp (183924571764955369 / 10000000000000000 : ℝ) ≤ (972170996709177871 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (183924571764955369 / 10000000000000000 : ℝ)
    (355342336619 / 200000000000 : ℝ) (972170996709177871 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1432_denomLower :
    (474627747165778567 / 5000000000 : ℝ) ≤ Real.exp (11480377157621369 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11480377157621369 / 625000000000000 : ℝ) (1775387764389
    / 1000000000000 : ℝ) (474627747165778567 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1432_product_lower :
    (11760259970121369 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (179 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1432_leftExp
    (by norm_num : (0 : ℝ) ≤ (29947262331 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1432_product_upper :
    Real.pi * Real.exp (1433 / 800 : ℝ) ≤ (188399571764955369 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1432_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1432_endpointLower :
    (8379 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (179 / 200 : ℝ) (1433 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11760259970121369 / 625000000000000 : ℝ) (Real.pi * Real.exp (179 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1432_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1433 / 800 : ℝ) - (179 / 400 : ℝ)) ≤
      (972170996709177871 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1432_denomUpper
    linarith [hpThetaJensenCell1432_product_upper]
  have hi : (1 / (972170996709177871 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1433 / 800 : ℝ) - (179 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (972170996709177871 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (972170996709177871 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((179 / 400 : ℝ) - Real.pi * Real.exp (1433 / 800 : ℝ)) := by
    rw [show (179 / 400 : ℝ) - Real.pi * Real.exp (1433 / 800 : ℝ) =
      -(Real.pi * Real.exp (1433 / 800 : ℝ) - (179 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (179 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (179 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1432_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (972170996709177871 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1432_endpointUpper :
    hpThetaJensenKernelEndpointUpper (179 / 200 : ℝ) (1433 / 1600 : ℝ) ≤ (69011 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1433 / 800 : ℝ)) (188399571764955369 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1433 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1432_product_upper
  have hD : (474627747165778567 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (179 / 100 : ℝ) - (1433 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1432_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1432_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (179 / 100 : ℝ) - (1433 / 3200 : ℝ)) ≤
      (1 / (474627747165778567 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (474627747165778567 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1433 / 3200 : ℝ) - Real.pi * Real.exp (179 / 100 : ℝ)) ≤
      (2 / (474627747165778567 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1433 / 3200 : ℝ) - Real.pi * Real.exp (179 / 100 : ℝ) =
      -(Real.pi * Real.exp (179 / 100 : ℝ) - (1433 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (188399571764955369 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (188399571764955369 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1432_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (179 / 200 : ℝ) (1433 / 1600 : ℝ)) :
    (8379 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (69011 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1432_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1432_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1433_leftExp :
    (59969439631 / 10000000000 : ℝ) ≤ Real.exp (1433 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1433 / 800 : ℝ) (1057572896581 / 1000000000000 : ℝ)
    (59969439631 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1433_rightExp :
    Real.exp (717 / 400 : ℝ) ≤ (60044448303 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (717 / 400 : ℝ) (105761420883 / 100000000000 : ℝ)
    (60044448303 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1433_denomUpper :
    Real.exp (184157093477566679 / 10000000000000000 : ℝ) ≤ (995040940751258357 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (184157093477566679 / 10000000000000000 : ℝ)
    (1778003164889 / 1000000000000 : ℝ) (995040940751258357 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1433_denomLower :
    (242889438150919013 / 2500000000 : ℝ) ≤ Real.exp (22989782723654069 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (22989782723654069 / 1250000000000000 : ℝ) (888338324519
    / 500000000000 : ℝ) (242889438150919013 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1433_product_lower :
    (23549938973654069 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1433 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1433_leftExp
    (by norm_num : (0 : ℝ) ≤ (59969439631 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1433_product_upper :
    Real.pi * Real.exp (717 / 400 : ℝ) ≤ (188635218477566679 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1433_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1433_endpointLower :
    (262649 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1433 / 1600 : ℝ) (717 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23549938973654069 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1433 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1433_product_lower
  have hD : Real.exp (Real.pi * Real.exp (717 / 400 : ℝ) - (1433 / 3200 : ℝ)) ≤
      (995040940751258357 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1433_denomUpper
    linarith [hpThetaJensenCell1433_product_upper]
  have hi : (1 / (995040940751258357 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (717 / 400 : ℝ) - (1433 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (995040940751258357 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (995040940751258357 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1433 / 3200 : ℝ) - Real.pi * Real.exp (717 / 400 : ℝ)) := by
    rw [show (1433 / 3200 : ℝ) - Real.pi * Real.exp (717 / 400 : ℝ) =
      -(Real.pi * Real.exp (717 / 400 : ℝ) - (1433 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1433 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1433 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1433_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (995040940751258357 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1433_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1433 / 1600 : ℝ) (717 / 800 : ℝ) ≤ (270411 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (717 / 400 : ℝ)) (188635218477566679 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (717 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1433_product_upper
  have hD : (242889438150919013 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1433 / 800 : ℝ) - (717 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1433_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1433_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1433 / 800 : ℝ) - (717 / 1600 : ℝ)) ≤
      (1 / (242889438150919013 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (242889438150919013 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((717 / 1600 : ℝ) - Real.pi * Real.exp (1433 / 800 : ℝ)) ≤
      (2 / (242889438150919013 / 2500000000 : ℝ) : ℝ) := by
    rw [show (717 / 1600 : ℝ) - Real.pi * Real.exp (1433 / 800 : ℝ) =
      -(Real.pi * Real.exp (1433 / 800 : ℝ) - (717 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (188635218477566679 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (188635218477566679 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1433_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1433 / 1600 : ℝ) (717 / 800 : ℝ)) :
    (262649 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (270411 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1433_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1433_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1434_leftExp :
    (60044448301 / 10000000000 : ℝ) ≤ Real.exp (717 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (717 / 400 : ℝ) (1057614208829 / 1000000000000 : ℝ)
    (60044448301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1434_rightExp :
    Real.exp (287 / 160 : ℝ) ≤ (60119550793 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (287 / 160 : ℝ) (264413880673 / 250000000000 : ℝ)
    (60119550793 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1434_denomUpper :
    Real.exp (184389909934433249 / 10000000000000000 : ℝ) ≤ (127309863742971499 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (184389909934433249 / 10000000000000000 : ℝ) (2780151913
    / 1562500000 : ℝ) (127309863742971499 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1434_denomLower :
    (124301657856855187 / 1250000000 : ℝ) ≤ Real.exp (23018847928354399 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23018847928354399 / 1250000000000000 : ℝ) (1777968104949
    / 1000000000000 : ℝ) (124301657856855187 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1434_product_lower :
    (23579394803354399 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (717 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1434_leftExp
    (by norm_num : (0 : ℝ) ≤ (60044448301 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1434_product_upper :
    Real.pi * Real.exp (287 / 160 : ℝ) ≤ (188871159934433249 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1434_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1434_endpointLower :
    (10291 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (717 / 800 : ℝ) (287 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23579394803354399 / 1250000000000000 : ℝ) (Real.pi * Real.exp (717 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1434_product_lower
  have hD : Real.exp (Real.pi * Real.exp (287 / 160 : ℝ) - (717 / 1600 : ℝ)) ≤
      (127309863742971499 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1434_denomUpper
    linarith [hpThetaJensenCell1434_product_upper]
  have hi : (1 / (127309863742971499 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (287 / 160 : ℝ) - (717 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (127309863742971499 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (127309863742971499 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((717 / 1600 : ℝ) - Real.pi * Real.exp (287 / 160 : ℝ)) := by
    rw [show (717 / 1600 : ℝ) - Real.pi * Real.exp (287 / 160 : ℝ) =
      -(Real.pi * Real.exp (287 / 160 : ℝ) - (717 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (717 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (717 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1434_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (127309863742971499 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1434_endpointUpper :
    hpThetaJensenKernelEndpointUpper (717 / 800 : ℝ) (287 / 320 : ℝ) ≤ (132443 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (287 / 160 : ℝ)) (188871159934433249 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (287 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1434_product_upper
  have hD : (124301657856855187 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (717 / 400 : ℝ) - (287 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1434_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1434_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (717 / 400 : ℝ) - (287 / 640 : ℝ)) ≤
      (1 / (124301657856855187 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (124301657856855187 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((287 / 640 : ℝ) - Real.pi * Real.exp (717 / 400 : ℝ)) ≤
      (2 / (124301657856855187 / 1250000000 : ℝ) : ℝ) := by
    rw [show (287 / 640 : ℝ) - Real.pi * Real.exp (717 / 400 : ℝ) =
      -(Real.pi * Real.exp (717 / 400 : ℝ) - (287 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (188871159934433249 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (188871159934433249 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1434_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (717 / 800 : ℝ) (287 / 320 : ℝ)) :
    (10291 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (132443 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1434_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1434_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1435_leftExp :
    (6011955079 / 1000000000 : ℝ) ≤ Real.exp (287 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (287 / 160 : ℝ) (1057655522691 / 1000000000000 : ℝ)
    (6011955079 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1435_rightExp :
    Real.exp (359 / 200 : ℝ) ≤ (3009737361 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (359 / 200 : ℝ) (132212104771 / 125000000000 : ℝ)
    (3009737361 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1435_denomUpper :
    Real.exp (9231151075156073 / 500000000000000 : ℝ) ≤ (521249860141226813 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (9231151075156073 / 500000000000000 : ℝ) (111287116731 /
    62500000000 : ℝ) (521249860141226813 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1435_denomLower :
    (203567287854773967 / 2000000000 : ℝ) ≤ Real.exp (2304794997568221 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2304794997568221 / 125000000000000 : ℝ) (444815534607 /
    250000000000 : ℝ) (203567287854773967 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1435_product_lower :
    (2360888747568221 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (287 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1435_leftExp
    (by norm_num : (0 : ℝ) ≤ (6011955079 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1435_product_upper :
    Real.pi * Real.exp (359 / 200 : ℝ) ≤ (9455369825156073 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1435_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1435_endpointLower :
    (252003 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (287 / 320 : ℝ) (359 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2360888747568221 / 125000000000000 : ℝ) (Real.pi * Real.exp (287 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1435_product_lower
  have hD : Real.exp (Real.pi * Real.exp (359 / 200 : ℝ) - (287 / 640 : ℝ)) ≤
      (521249860141226813 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1435_denomUpper
    linarith [hpThetaJensenCell1435_product_upper]
  have hi : (1 / (521249860141226813 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (359 / 200 : ℝ) - (287 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (521249860141226813 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (521249860141226813 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((287 / 640 : ℝ) - Real.pi * Real.exp (359 / 200 : ℝ)) := by
    rw [show (287 / 640 : ℝ) - Real.pi * Real.exp (359 / 200 : ℝ) =
      -(Real.pi * Real.exp (359 / 200 : ℝ) - (287 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (287 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (287 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1435_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (521249860141226813 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1435_endpointUpper :
    hpThetaJensenKernelEndpointUpper (287 / 320 : ℝ) (359 / 400 : ℝ) ≤ (129733 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (359 / 200 : ℝ)) (9455369825156073 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (359 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1435_product_upper
  have hD : (203567287854773967 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (287 / 160 : ℝ) - (359 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1435_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1435_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (287 / 160 : ℝ) - (359 / 800 : ℝ)) ≤
      (1 / (203567287854773967 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (203567287854773967 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((359 / 800 : ℝ) - Real.pi * Real.exp (287 / 160 : ℝ)) ≤
      (2 / (203567287854773967 / 2000000000 : ℝ) : ℝ) := by
    rw [show (359 / 800 : ℝ) - Real.pi * Real.exp (287 / 160 : ℝ) =
      -(Real.pi * Real.exp (287 / 160 : ℝ) - (359 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9455369825156073 / 500000000000000 : ℝ) ^ 2 - 6 *
      (9455369825156073 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1435_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (287 / 320 : ℝ) (359 / 400 : ℝ)) :
    (252003 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (129733 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1435_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1435_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1436_leftExp :
    (60194747217 / 10000000000 : ℝ) ≤ Real.exp (359 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (359 / 200 : ℝ) (1057696838167 / 1000000000000 : ℝ)
    (60194747217 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1436_rightExp :
    Real.exp (1437 / 800 : ℝ) ≤ (60270037699 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1437 / 800 : ℝ) (1057738155257 / 1000000000000 : ℝ)
    (60270037699 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1436_denomUpper :
    Real.exp (184856428544914507 / 10000000000000000 : ℝ) ≤ (213423718216668541 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (184856428544914507 / 10000000000000000 : ℝ)
    (890946550651 / 500000000000 : ℝ) (213423718216668541 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1436_denomLower :
    (104184208909569147 / 1000000000 : ℝ) ≤ Real.exp (23077088912368683 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23077088912368683 / 1250000000000000 : ℝ) (222569844477
    / 125000000000 : ℝ) (104184208909569147 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1436_product_lower :
    (23638417037368683 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (359 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1436_leftExp
    (by norm_num : (0 : ℝ) ≤ (60194747217 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1436_product_upper :
    Real.pi * Real.exp (1437 / 800 : ℝ) ≤ (189343928544914507 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1436_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1436_endpointLower :
    (15427 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (359 / 400 : ℝ) (1437 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23638417037368683 / 1250000000000000 : ℝ) (Real.pi * Real.exp (359 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1436_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1437 / 800 : ℝ) - (359 / 800 : ℝ)) ≤
      (213423718216668541 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1436_denomUpper
    linarith [hpThetaJensenCell1436_product_upper]
  have hi : (1 / (213423718216668541 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1437 / 800 : ℝ) - (359 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (213423718216668541 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (213423718216668541 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((359 / 800 : ℝ) - Real.pi * Real.exp (1437 / 800 : ℝ)) := by
    rw [show (359 / 800 : ℝ) - Real.pi * Real.exp (1437 / 800 : ℝ) =
      -(Real.pi * Real.exp (1437 / 800 : ℝ) - (359 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (359 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (359 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1436_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (213423718216668541 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1436_endpointUpper :
    hpThetaJensenKernelEndpointUpper (359 / 400 : ℝ) (1437 / 1600 : ℝ) ≤ (5083 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1437 / 800 : ℝ)) (189343928544914507 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1437 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1436_product_upper
  have hD : (104184208909569147 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (359 / 200 : ℝ) - (1437 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1436_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1436_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (359 / 200 : ℝ) - (1437 / 3200 : ℝ)) ≤
      (1 / (104184208909569147 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (104184208909569147 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1437 / 3200 : ℝ) - Real.pi * Real.exp (359 / 200 : ℝ)) ≤
      (2 / (104184208909569147 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1437 / 3200 : ℝ) - Real.pi * Real.exp (359 / 200 : ℝ) =
      -(Real.pi * Real.exp (359 / 200 : ℝ) - (1437 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (189343928544914507 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (189343928544914507 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1436_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (359 / 400 : ℝ) (1437 / 1600 : ℝ)) :
    (15427 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5083 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1436_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1436_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1437_leftExp :
    (60270037697 / 10000000000 : ℝ) ≤ Real.exp (1437 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1437 / 800 : ℝ) (132217269407 / 125000000000 : ℝ)
    (60270037697 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1437_rightExp :
    Real.exp (719 / 400 : ℝ) ≤ (60345422353 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (719 / 400 : ℝ) (1057779473961 / 1000000000000 : ℝ)
    (60345422353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1437_denomUpper :
    Real.exp (185090131446228329 / 10000000000000000 : ℝ) ≤ (546175579981960819 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (185090131446228329 / 10000000000000000 : ℝ)
    (1783194931583 / 1000000000000 : ℝ) (546175579981960819 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1437_denomLower :
    (213289084420354813 / 2000000000 : ℝ) ≤ Real.exp (23106264783574203 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23106264783574203 / 1250000000000000 : ℝ) (1781857963401
    / 1000000000000 : ℝ) (213289084420354813 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1437_product_lower :
    (23667983533574203 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1437 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1437_leftExp
    (by norm_num : (0 : ℝ) ≤ (60270037697 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1437_product_upper :
    Real.pi * Real.exp (719 / 400 : ℝ) ≤ (189580756446228329 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1437_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1437_endpointLower :
    (1511 / 62500000 : ℝ) ≤ hpThetaTraceEndpointLower (1437 / 1600 : ℝ) (719 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23667983533574203 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1437 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1437_product_lower
  have hD : Real.exp (Real.pi * Real.exp (719 / 400 : ℝ) - (1437 / 3200 : ℝ)) ≤
      (546175579981960819 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1437_denomUpper
    linarith [hpThetaJensenCell1437_product_upper]
  have hi : (1 / (546175579981960819 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (719 / 400 : ℝ) - (1437 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (546175579981960819 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (546175579981960819 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1437 / 3200 : ℝ) - Real.pi * Real.exp (719 / 400 : ℝ)) := by
    rw [show (1437 / 3200 : ℝ) - Real.pi * Real.exp (719 / 400 : ℝ) =
      -(Real.pi * Real.exp (719 / 400 : ℝ) - (1437 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1437 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1437 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1437_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (546175579981960819 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1437_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1437 / 1600 : ℝ) (719 / 800 : ℝ) ≤ (124467 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (719 / 400 : ℝ)) (189580756446228329 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (719 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1437_product_upper
  have hD : (213289084420354813 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1437 / 800 : ℝ) - (719 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1437_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1437_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1437 / 800 : ℝ) - (719 / 1600 : ℝ)) ≤
      (1 / (213289084420354813 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (213289084420354813 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((719 / 1600 : ℝ) - Real.pi * Real.exp (1437 / 800 : ℝ)) ≤
      (2 / (213289084420354813 / 2000000000 : ℝ) : ℝ) := by
    rw [show (719 / 1600 : ℝ) - Real.pi * Real.exp (1437 / 800 : ℝ) =
      -(Real.pi * Real.exp (1437 / 800 : ℝ) - (719 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (189580756446228329 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (189580756446228329 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1437_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1437 / 1600 : ℝ) (719 / 800 : ℝ)) :
    (1511 / 62500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (124467 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1437_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1437_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1438_leftExp :
    (1206908447 / 200000000 : ℝ) ≤ Real.exp (719 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (719 / 400 : ℝ) (26444486849 / 25000000000 : ℝ)
    (1206908447 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1438_rightExp :
    Real.exp (1439 / 800 : ℝ) ≤ (3776306331 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1439 / 800 : ℝ) (1057820794279 / 1000000000000 : ℝ)
    (3776306331 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1438_denomUpper :
    Real.exp (11582758160325283 / 625000000000000 : ℝ) ≤ (1118213488884820803 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (11582758160325283 / 625000000000000 : ℝ) (44612484121 /
    25000000000 : ℝ) (1118213488884820803 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1438_denomLower :
    (1091662064980930441 / 10000000000 : ℝ) ≤ Real.exp (462709552728453 / 25000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (462709552728453 / 25000000000000 : ℝ) (1783159767573 /
    1000000000000 : ℝ) (1091662064980930441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1438_product_lower :
    (473951740228453 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (719 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1438_leftExp
    (by norm_num : (0 : ℝ) ≤ (1206908447 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1438_product_upper :
    Real.pi * Real.exp (1439 / 800 : ℝ) ≤ (11863617535325283 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1438_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1438_endpointLower :
    (47357 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (719 / 800 : ℝ) (1439 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (473951740228453 / 25000000000000 : ℝ) (Real.pi * Real.exp (719 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1438_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1439 / 800 : ℝ) - (719 / 1600 : ℝ)) ≤
      (1118213488884820803 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1438_denomUpper
    linarith [hpThetaJensenCell1438_product_upper]
  have hi : (1 / (1118213488884820803 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1439 / 800 : ℝ) - (719 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1118213488884820803 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1118213488884820803 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((719 / 1600 : ℝ) - Real.pi * Real.exp (1439 / 800 : ℝ)) := by
    rw [show (719 / 1600 : ℝ) - Real.pi * Real.exp (1439 / 800 : ℝ) =
      -(Real.pi * Real.exp (1439 / 800 : ℝ) - (719 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (719 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (719 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1438_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1118213488884820803 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1438_endpointUpper :
    hpThetaJensenKernelEndpointUpper (719 / 800 : ℝ) (1439 / 1600 : ℝ) ≤ (243819 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1439 / 800 : ℝ)) (11863617535325283 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1439 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1438_product_upper
  have hD : (1091662064980930441 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (719 / 400 : ℝ) - (1439 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1438_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1438_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (719 / 400 : ℝ) - (1439 / 3200 : ℝ)) ≤
      (1 / (1091662064980930441 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1091662064980930441 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1439 / 3200 : ℝ) - Real.pi * Real.exp (719 / 400 : ℝ)) ≤
      (2 / (1091662064980930441 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1439 / 3200 : ℝ) - Real.pi * Real.exp (719 / 400 : ℝ) =
      -(Real.pi * Real.exp (719 / 400 : ℝ) - (1439 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11863617535325283 / 625000000000000 : ℝ) ^ 2 - 6 *
      (11863617535325283 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1438_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (719 / 800 : ℝ) (1439 / 1600 : ℝ)) :
    (47357 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (243819 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1438_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1438_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1439_leftExp :
    (60420901293 / 10000000000 : ℝ) ≤ Real.exp (1439 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1439 / 800 : ℝ) (528910397139 / 500000000000 : ℝ)
    (60420901293 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1439_rightExp :
    Real.exp (9 / 5 : ℝ) ≤ (30248237323 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 5 : ℝ) (1057862116211 / 1000000000000 : ℝ)
    (30248237323 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1439_denomUpper :
    Real.exp (92779213136275539 / 5000000000000000 : ℝ) ≤ (572361040379912143 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (92779213136275539 / 5000000000000000 : ℝ) (223225800933
    / 125000000000 : ℝ) (572361040379912143 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1439_denomLower :
    (1117508070583840209 / 10000000000 : ℝ) ≤ Real.exp (23164727516859807 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (23164727516859807 / 1250000000000000 : ℝ) (1784464174687
    / 1000000000000 : ℝ) (1117508070583840209 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1439_product_lower :
    (23727227516859807 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1439 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1439_leftExp
    (by norm_num : (0 : ℝ) ≤ (60420901293 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1439_product_upper :
    Real.pi * Real.exp (9 / 5 : ℝ) ≤ (95027650636275539 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1439_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1439_endpointLower :
    (115953 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1439 / 1600 : ℝ) (9 / 10 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (23727227516859807 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1439 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1439_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 5 : ℝ) - (1439 / 3200 : ℝ)) ≤
      (572361040379912143 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1439_denomUpper
    linarith [hpThetaJensenCell1439_product_upper]
  have hi : (1 / (572361040379912143 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 5 : ℝ) - (1439 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (572361040379912143 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (572361040379912143 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1439 / 3200 : ℝ) - Real.pi * Real.exp (9 / 5 : ℝ)) := by
    rw [show (1439 / 3200 : ℝ) - Real.pi * Real.exp (9 / 5 : ℝ) =
      -(Real.pi * Real.exp (9 / 5 : ℝ) - (1439 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1439 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1439 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1439_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (572361040379912143 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1439_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1439 / 1600 : ℝ) (9 / 10 : ℝ) ≤ (119401 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 5 : ℝ)) (95027650636275539 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 10 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1439_product_upper
  have hD : (1117508070583840209 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1439 / 800 : ℝ) - (9 / 20 : ℝ)) := by
    apply le_trans hpThetaJensenCell1439_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1439_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1439 / 800 : ℝ) - (9 / 20 : ℝ)) ≤
      (1 / (1117508070583840209 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1117508070583840209 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 20 : ℝ) - Real.pi * Real.exp (1439 / 800 : ℝ)) ≤
      (2 / (1117508070583840209 / 10000000000 : ℝ) : ℝ) := by
    rw [show (9 / 20 : ℝ) - Real.pi * Real.exp (1439 / 800 : ℝ) =
      -(Real.pi * Real.exp (1439 / 800 : ℝ) - (9 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (95027650636275539 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (95027650636275539 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1439_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1439 / 1600 : ℝ) (9 / 10 : ℝ)) :
    (115953 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (119401 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1439_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1439_endpointUpper

def hpThetaJensenCellsBatch071Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (342713 / 10000000000 : ℝ)
  | 1 => (335829 / 10000000000 : ℝ)
  | 2 => (164537 / 5000000000 : ℝ)
  | 3 => (64489 / 2000000000 : ℝ)
  | 4 => (15797 / 500000000 : ℝ)
  | 5 => (154779 / 5000000000 : ℝ)
  | 6 => (60659 / 2000000000 : ℝ)
  | 7 => (297151 / 10000000000 : ℝ)
  | 8 => (145561 / 5000000000 : ℝ)
  | 9 => (35651 / 1250000000 : ℝ)
  | 10 => (55881 / 2000000000 : ℝ)
  | 11 => (17107 / 625000000 : ℝ)
  | 12 => (8379 / 312500000 : ℝ)
  | 13 => (262649 / 10000000000 : ℝ)
  | 14 => (10291 / 400000000 : ℝ)
  | 15 => (252003 / 10000000000 : ℝ)
  | 16 => (15427 / 625000000 : ℝ)
  | 17 => (1511 / 62500000 : ℝ)
  | 18 => (47357 / 2000000000 : ℝ)
  | 19 => (115953 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch071Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (88177 / 2500000000 : ℝ)
  | 1 => (345633 / 10000000000 : ℝ)
  | 2 => (33869 / 1000000000 : ℝ)
  | 3 => (331877 / 10000000000 : ℝ)
  | 4 => (40649 / 1250000000 : ℝ)
  | 5 => (39829 / 1250000000 : ℝ)
  | 6 => (62439 / 2000000000 : ℝ)
  | 7 => (305879 / 10000000000 : ℝ)
  | 8 => (149841 / 5000000000 : ℝ)
  | 9 => (146801 / 5000000000 : ℝ)
  | 10 => (287637 / 10000000000 : ℝ)
  | 11 => (56357 / 2000000000 : ℝ)
  | 12 => (69011 / 2500000000 : ℝ)
  | 13 => (270411 / 10000000000 : ℝ)
  | 14 => (132443 / 5000000000 : ℝ)
  | 15 => (129733 / 5000000000 : ℝ)
  | 16 => (5083 / 200000000 : ℝ)
  | 17 => (124467 / 5000000000 : ℝ)
  | 18 => (243819 / 10000000000 : ℝ)
  | 19 => (119401 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch071_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch071Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch071Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1420_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1421_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1422_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1423_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1424_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1425_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1426_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1427_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1428_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1429_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1430_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1431_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1432_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1433_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1434_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1435_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1436_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1437_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1438_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1439_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper] at h ⊢
    exact h

end HodgeProofHP
