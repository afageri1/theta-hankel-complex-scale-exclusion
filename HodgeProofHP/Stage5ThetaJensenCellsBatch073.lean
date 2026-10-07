import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1460_leftExp :
    (6202795019 / 1000000000 : ℝ) ≤ Real.exp (73 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 40 : ℝ) (529344446953 / 500000000000 : ℝ)
    (6202795019 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1460_rightExp :
    Real.exp (1461 / 800 : ℝ) ≤ (6210553361 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1461 / 800 : ℝ) (4234920999 / 4000000000 : ℝ)
    (6210553361 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1460_denomUpper :
    Real.exp (19054780965044073 / 1000000000000000 : ℝ) ≤ (1885325002402161311 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (19054780965044073 / 1000000000000000 : ℝ) (906934293373
    / 500000000000 : ℝ) (1885325002402161311 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1460_denomLower :
    (114958882624478081 / 625000000 : ℝ) ≤ Real.exp (2378761088666281 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2378761088666281 / 125000000000000 : ℝ) (1812469485763 /
    1000000000000 : ℝ) (114958882624478081 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1460_product_lower :
    (2435831401166281 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1460_leftExp
    (by norm_num : (0 : ℝ) ≤ (6202795019 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1460_product_upper :
    Real.pi * Real.exp (1461 / 800 : ℝ) ≤ (19511030965044073 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1460_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1460_endpointLower :
    (148727 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 80 : ℝ) (1461 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2435831401166281 / 125000000000000 : ℝ) (Real.pi * Real.exp (73 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1460_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1461 / 800 : ℝ) - (73 / 160 : ℝ)) ≤
      (1885325002402161311 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1460_denomUpper
    linarith [hpThetaJensenCell1460_product_upper]
  have hi : (1 / (1885325002402161311 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1461 / 800 : ℝ) - (73 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1885325002402161311 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1885325002402161311 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 160 : ℝ) - Real.pi * Real.exp (1461 / 800 : ℝ)) := by
    rw [show (73 / 160 : ℝ) - Real.pi * Real.exp (1461 / 800 : ℝ) =
      -(Real.pi * Real.exp (1461 / 800 : ℝ) - (73 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1460_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1885325002402161311 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1460_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 80 : ℝ) (1461 / 1600 : ℝ) ≤ (76623 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1461 / 800 : ℝ)) (19511030965044073 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1461 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1460_product_upper
  have hD : (114958882624478081 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 40 : ℝ) - (1461 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1460_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1460_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 40 : ℝ) - (1461 / 3200 : ℝ)) ≤
      (1 / (114958882624478081 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (114958882624478081 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1461 / 3200 : ℝ) - Real.pi * Real.exp (73 / 40 : ℝ)) ≤
      (2 / (114958882624478081 / 625000000 : ℝ) : ℝ) := by
    rw [show (1461 / 3200 : ℝ) - Real.pi * Real.exp (73 / 40 : ℝ) =
      -(Real.pi * Real.exp (73 / 40 : ℝ) - (1461 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19511030965044073 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (19511030965044073 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1460_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 80 : ℝ) (1461 / 1600 : ℝ)) :
    (148727 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (76623 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1460_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1460_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1461_leftExp :
    (7763191701 / 1250000000 : ℝ) ≤ Real.exp (1461 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1461 / 800 : ℝ) (1058730249749 / 1000000000000 : ℝ)
    (7763191701 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1461_rightExp :
    Real.exp (731 / 400 : ℝ) ≤ (62183214067 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (731 / 400 : ℝ) (132346450901 / 125000000000 : ℝ)
    (62183214067 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1461_denomUpper :
    Real.exp (190788725030388731 / 10000000000000000 : ℝ) ≤ (193129692500376243 / 1000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (190788725030388731 / 10000000000000000 : ℝ)
    (1815234691049 / 1000000000000 : ℝ) (193129692500376243 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1461_denomLower :
    (1884135339510829029 / 10000000000 : ℝ) ≤ Real.exp (2977210899040999 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2977210899040999 / 156250000000000 : ℝ) (906916403951 /
    500000000000 : ℝ) (1884135339510829029 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1461_product_lower :
    (3048597617790999 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (1461 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1461_leftExp
    (by norm_num : (0 : ℝ) ≤ (7763191701 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1461_product_upper :
    Real.pi * Real.exp (731 / 400 : ℝ) ≤ (195354350030388731 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1461_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1461_endpointLower :
    (29113 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1461 / 1600 : ℝ) (731 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3048597617790999 / 156250000000000 : ℝ) (Real.pi * Real.exp (1461 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1461_product_lower
  have hD : Real.exp (Real.pi * Real.exp (731 / 400 : ℝ) - (1461 / 3200 : ℝ)) ≤
      (193129692500376243 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1461_denomUpper
    linarith [hpThetaJensenCell1461_product_upper]
  have hi : (1 / (193129692500376243 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (731 / 400 : ℝ) - (1461 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (193129692500376243 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (193129692500376243 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1461 / 3200 : ℝ) - Real.pi * Real.exp (731 / 400 : ℝ)) := by
    rw [show (1461 / 3200 : ℝ) - Real.pi * Real.exp (731 / 400 : ℝ) =
      -(Real.pi * Real.exp (731 / 400 : ℝ) - (1461 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1461 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1461 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1461_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (193129692500376243 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1461_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1461 / 1600 : ℝ) (731 / 800 : ℝ) ≤ (149993 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (731 / 400 : ℝ)) (195354350030388731 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (731 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1461_product_upper
  have hD : (1884135339510829029 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1461 / 800 : ℝ) - (731 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1461_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1461_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1461 / 800 : ℝ) - (731 / 1600 : ℝ)) ≤
      (1 / (1884135339510829029 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1884135339510829029 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((731 / 1600 : ℝ) - Real.pi * Real.exp (1461 / 800 : ℝ)) ≤
      (2 / (1884135339510829029 / 10000000000 : ℝ) : ℝ) := by
    rw [show (731 / 1600 : ℝ) - Real.pi * Real.exp (1461 / 800 : ℝ) =
      -(Real.pi * Real.exp (1461 / 800 : ℝ) - (731 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (195354350030388731 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (195354350030388731 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1461_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1461 / 1600 : ℝ) (731 / 800 : ℝ)) :
    (29113 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (149993 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1461_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1461_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1462_leftExp :
    (3886450879 / 625000000 : ℝ) ≤ Real.exp (731 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (731 / 400 : ℝ) (1058771607207 / 1000000000000 : ℝ)
    (3886450879 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1462_rightExp :
    Real.exp (1463 / 800 : ℝ) ≤ (12452198337 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1463 / 800 : ℝ) (1058812966281 / 1000000000000 : ℝ)
    (12452198337 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1462_denomUpper :
    Real.exp (38205989130130841 / 2000000000000000 : ℝ) ≤ (1978450220133373763 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (38205989130130841 / 2000000000000000 : ℝ) (908301778519
    / 500000000000 : ℝ) (1978450220133373763 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1462_denomLower :
    (482519559410637943 / 2500000000 : ℝ) ≤ Real.exp (1490487600294921 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1490487600294921 / 78125000000000 : ℝ) (1815198884799 /
    1000000000000 : ℝ) (482519559410637943 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1462_product_lower :
    (1526205373732421 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (731 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1462_leftExp
    (by norm_num : (0 : ℝ) ≤ (3886450879 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1462_product_upper :
    Real.pi * Real.exp (1463 / 800 : ℝ) ≤ (39119739130130841 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1462_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1462_endpointLower :
    (142467 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (731 / 800 : ℝ) (1463 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1526205373732421 / 78125000000000 : ℝ) (Real.pi * Real.exp (731 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1462_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1463 / 800 : ℝ) - (731 / 1600 : ℝ)) ≤
      (1978450220133373763 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1462_denomUpper
    linarith [hpThetaJensenCell1462_product_upper]
  have hi : (1 / (1978450220133373763 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1463 / 800 : ℝ) - (731 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1978450220133373763 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1978450220133373763 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((731 / 1600 : ℝ) - Real.pi * Real.exp (1463 / 800 : ℝ)) := by
    rw [show (731 / 1600 : ℝ) - Real.pi * Real.exp (1463 / 800 : ℝ) =
      -(Real.pi * Real.exp (1463 / 800 : ℝ) - (731 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (731 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (731 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1462_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1978450220133373763 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1462_endpointUpper :
    hpThetaJensenKernelEndpointUpper (731 / 800 : ℝ) (1463 / 1600 : ℝ) ≤ (36701 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1463 / 800 : ℝ)) (39119739130130841 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1463 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1462_product_upper
  have hD : (482519559410637943 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (731 / 400 : ℝ) - (1463 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1462_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1462_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (731 / 400 : ℝ) - (1463 / 3200 : ℝ)) ≤
      (1 / (482519559410637943 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (482519559410637943 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1463 / 3200 : ℝ) - Real.pi * Real.exp (731 / 400 : ℝ)) ≤
      (2 / (482519559410637943 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1463 / 3200 : ℝ) - Real.pi * Real.exp (731 / 400 : ℝ) =
      -(Real.pi * Real.exp (731 / 400 : ℝ) - (1463 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39119739130130841 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (39119739130130841 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1462_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (731 / 800 : ℝ) (1463 / 1600 : ℝ)) :
    (142467 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (36701 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1462_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1462_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1463_leftExp :
    (31130495841 / 5000000000 : ℝ) ≤ Real.exp (1463 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1463 / 800 : ℝ) (26470324157 / 25000000000 : ℝ)
    (31130495841 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1463_rightExp :
    Real.exp (183 / 100 : ℝ) ≤ (62338866587 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (183 / 100 : ℝ) (1058854326971 / 1000000000000 : ℝ)
    (62338866587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1463_denomUpper :
    Real.exp (191271471897653091 / 10000000000000000 : ℝ) ≤ (253352090449797167 / 1250000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (191271471897653091 / 10000000000000000 : ℝ)
    (363595038321 / 200000000000 : ℝ) (253352090449797167 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1463_denomLower :
    (1977201762746278743 / 10000000000 : ℝ) ≤ Real.exp (11938977086264859 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (11938977086264859 / 625000000000000 : ℝ) (908283861673 /
    500000000000 : ℝ) (1977201762746278743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1463_product_lower :
    (12224914586264859 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1463 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1463_leftExp
    (by norm_num : (0 : ℝ) ≤ (31130495841 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1463_product_upper :
    Real.pi * Real.exp (183 / 100 : ℝ) ≤ (195843346897653091 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1463_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1463_endpointLower :
    (139429 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1463 / 1600 : ℝ) (183 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12224914586264859 / 625000000000000 : ℝ) (Real.pi * Real.exp (1463 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1463_product_lower
  have hD : Real.exp (Real.pi * Real.exp (183 / 100 : ℝ) - (1463 / 3200 : ℝ)) ≤
      (253352090449797167 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1463_denomUpper
    linarith [hpThetaJensenCell1463_product_upper]
  have hi : (1 / (253352090449797167 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (183 / 100 : ℝ) - (1463 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (253352090449797167 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (253352090449797167 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1463 / 3200 : ℝ) - Real.pi * Real.exp (183 / 100 : ℝ)) := by
    rw [show (1463 / 3200 : ℝ) - Real.pi * Real.exp (183 / 100 : ℝ) =
      -(Real.pi * Real.exp (183 / 100 : ℝ) - (1463 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1463 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1463 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1463_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (253352090449797167 / 1250000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1463_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1463 / 1600 : ℝ) (183 / 200 : ℝ) ≤ (143679 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (183 / 100 : ℝ)) (195843346897653091 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (183 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1463_product_upper
  have hD : (1977201762746278743 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1463 / 800 : ℝ) - (183 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1463_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1463_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1463 / 800 : ℝ) - (183 / 400 : ℝ)) ≤
      (1 / (1977201762746278743 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1977201762746278743 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((183 / 400 : ℝ) - Real.pi * Real.exp (1463 / 800 : ℝ)) ≤
      (2 / (1977201762746278743 / 10000000000 : ℝ) : ℝ) := by
    rw [show (183 / 400 : ℝ) - Real.pi * Real.exp (1463 / 800 : ℝ) =
      -(Real.pi * Real.exp (1463 / 800 : ℝ) - (183 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (195843346897653091 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (195843346897653091 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1463_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1463 / 1600 : ℝ) (183 / 200 : ℝ)) :
    (139429 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (143679 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1463_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1463_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1464_leftExp :
    (7792358323 / 1250000000 : ℝ) ≤ Real.exp (183 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (183 / 100 : ℝ) (105885432697 / 100000000000 : ℝ)
    (7792358323 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1464_rightExp :
    Real.exp (293 / 160 : ℝ) ≤ (62416838893 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (293 / 160 : ℝ) (264723922319 / 250000000000 : ℝ)
    (62416838893 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1464_denomUpper :
    Real.exp (191513304148376549 / 10000000000000000 : ℝ) ≤ (415285833036303371 / 2000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (191513304148376549 / 10000000000000000 : ℝ)
    (363869920321 / 200000000000 : ℝ) (415285833036303371 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1464_denomLower :
    (2025537729814753011 / 10000000000 : ℝ) ≤ Real.exp (2988518117958777 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2988518117958777 / 156250000000000 : ℝ) (908969665207 /
    500000000000 : ℝ) (2025537729814753011 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1464_product_lower :
    (3060051321083777 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (183 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1464_leftExp
    (by norm_num : (0 : ℝ) ≤ (7792358323 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1464_product_upper :
    Real.pi * Real.exp (293 / 160 : ℝ) ≤ (196088304148376549 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1464_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1464_endpointLower :
    (136453 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (183 / 200 : ℝ) (293 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3060051321083777 / 156250000000000 : ℝ) (Real.pi * Real.exp (183 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1464_product_lower
  have hD : Real.exp (Real.pi * Real.exp (293 / 160 : ℝ) - (183 / 400 : ℝ)) ≤
      (415285833036303371 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1464_denomUpper
    linarith [hpThetaJensenCell1464_product_upper]
  have hi : (1 / (415285833036303371 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (293 / 160 : ℝ) - (183 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (415285833036303371 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (415285833036303371 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((183 / 400 : ℝ) - Real.pi * Real.exp (293 / 160 : ℝ)) := by
    rw [show (183 / 400 : ℝ) - Real.pi * Real.exp (293 / 160 : ℝ) =
      -(Real.pi * Real.exp (293 / 160 : ℝ) - (183 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (183 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (183 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1464_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (415285833036303371 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1464_endpointUpper :
    hpThetaJensenKernelEndpointUpper (183 / 200 : ℝ) (293 / 320 : ℝ) ≤ (17577 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (293 / 160 : ℝ)) (196088304148376549 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (293 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1464_product_upper
  have hD : (2025537729814753011 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (183 / 100 : ℝ) - (293 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1464_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1464_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (183 / 100 : ℝ) - (293 / 640 : ℝ)) ≤
      (1 / (2025537729814753011 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2025537729814753011 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((293 / 640 : ℝ) - Real.pi * Real.exp (183 / 100 : ℝ)) ≤
      (2 / (2025537729814753011 / 10000000000 : ℝ) : ℝ) := by
    rw [show (293 / 640 : ℝ) - Real.pi * Real.exp (183 / 100 : ℝ) =
      -(Real.pi * Real.exp (183 / 100 : ℝ) - (293 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (196088304148376549 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (196088304148376549 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1464_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (183 / 200 : ℝ) (293 / 320 : ℝ)) :
    (136453 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17577 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1464_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1464_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1465_leftExp :
    (6241683889 / 1000000000 : ℝ) ≤ Real.exp (293 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (293 / 160 : ℝ) (42355827571 / 40000000000 : ℝ)
    (6241683889 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1465_rightExp :
    Real.exp (733 / 400 : ℝ) ≤ (2499796349 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (733 / 400 : ℝ) (1058937053197 / 1000000000000 : ℝ)
    (2499796349 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1465_denomUpper :
    Real.exp (7670217711443957 / 400000000000000 : ℝ) ≤ (2127321197973200011 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (7670217711443957 / 400000000000000 : ℝ) (364145358789 /
    200000000000 : ℝ) (2127321197973200011 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1465_denomLower :
    (259389855993651787 / 1250000000 : ℝ) ≤ Real.exp (2393837396526411 / 125000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (2393837396526411 / 125000000000000 : ℝ) (909656856429 /
    500000000000 : ℝ) (259389855993651787 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1465_product_lower :
    (2451103021526411 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (293 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1465_leftExp
    (by norm_num : (0 : ℝ) ≤ (6241683889 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1465_product_upper :
    Real.pi * Real.exp (733 / 400 : ℝ) ≤ (7853342711443957 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1465_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1465_endpointLower :
    (4173 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (293 / 320 : ℝ) (733 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2451103021526411 / 125000000000000 : ℝ) (Real.pi * Real.exp (293 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1465_product_lower
  have hD : Real.exp (Real.pi * Real.exp (733 / 400 : ℝ) - (293 / 640 : ℝ)) ≤
      (2127321197973200011 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1465_denomUpper
    linarith [hpThetaJensenCell1465_product_upper]
  have hi : (1 / (2127321197973200011 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (733 / 400 : ℝ) - (293 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2127321197973200011 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2127321197973200011 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((293 / 640 : ℝ) - Real.pi * Real.exp (733 / 400 : ℝ)) := by
    rw [show (293 / 640 : ℝ) - Real.pi * Real.exp (733 / 400 : ℝ) =
      -(Real.pi * Real.exp (733 / 400 : ℝ) - (293 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (293 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (293 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1465_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2127321197973200011 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1465_endpointUpper :
    hpThetaJensenKernelEndpointUpper (293 / 320 : ℝ) (733 / 800 : ℝ) ≤ (68807 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (733 / 400 : ℝ)) (7853342711443957 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (733 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1465_product_upper
  have hD : (259389855993651787 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (293 / 160 : ℝ) - (733 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1465_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1465_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (293 / 160 : ℝ) - (733 / 1600 : ℝ)) ≤
      (1 / (259389855993651787 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (259389855993651787 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((733 / 1600 : ℝ) - Real.pi * Real.exp (293 / 160 : ℝ)) ≤
      (2 / (259389855993651787 / 1250000000 : ℝ) : ℝ) := by
    rw [show (733 / 1600 : ℝ) - Real.pi * Real.exp (293 / 160 : ℝ) =
      -(Real.pi * Real.exp (293 / 160 : ℝ) - (733 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7853342711443957 / 400000000000000 : ℝ) ^ 2 - 6 *
      (7853342711443957 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1465_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (293 / 320 : ℝ) (733 / 800 : ℝ)) :
    (4173 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (68807 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1465_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1465_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1466_leftExp :
    (62494908723 / 10000000000 : ℝ) ≤ Real.exp (733 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (733 / 400 : ℝ) (264734263299 / 250000000000 : ℝ)
    (62494908723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1466_rightExp :
    Real.exp (1467 / 800 : ℝ) ≤ (12514615241 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1467 / 800 : ℝ) (1058978418733 / 1000000000000 : ℝ)
    (12514615241 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1466_denomUpper :
    Real.exp (38399577638818913 / 2000000000000000 : ℝ) ≤ (544881856081586679 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (38399577638818913 / 2000000000000000 : ℝ) (444850287 /
    244140625 : ℝ) (544881856081586679 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1466_denomLower :
    (53149468743062631 / 250000000 : ℝ) ≤ Real.exp (23968641285613377 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (23968641285613377 / 1250000000000000 : ℝ) (364138175521
    / 200000000000 : ℝ) (53149468743062631 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1466_product_lower :
    (24541688160613377 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (733 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1466_leftExp
    (by norm_num : (0 : ℝ) ≤ (62494908723 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1466_product_upper :
    Real.pi * Real.exp (1467 / 800 : ℝ) ≤ (39315827638818913 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1466_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1466_endpointLower :
    (130677 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (733 / 800 : ℝ) (1467 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24541688160613377 / 1250000000000000 : ℝ) (Real.pi * Real.exp (733 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1466_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1467 / 800 : ℝ) - (733 / 1600 : ℝ)) ≤
      (544881856081586679 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1466_denomUpper
    linarith [hpThetaJensenCell1466_product_upper]
  have hi : (1 / (544881856081586679 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1467 / 800 : ℝ) - (733 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (544881856081586679 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (544881856081586679 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((733 / 1600 : ℝ) - Real.pi * Real.exp (1467 / 800 : ℝ)) := by
    rw [show (733 / 1600 : ℝ) - Real.pi * Real.exp (1467 / 800 : ℝ) =
      -(Real.pi * Real.exp (1467 / 800 : ℝ) - (733 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (733 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (733 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1466_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (544881856081586679 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1466_endpointUpper :
    hpThetaJensenKernelEndpointUpper (733 / 800 : ℝ) (1467 / 1600 : ℝ) ≤ (8417 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1467 / 800 : ℝ)) (39315827638818913 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1467 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1466_product_upper
  have hD : (53149468743062631 / 250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (733 / 400 : ℝ) - (1467 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1466_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1466_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (733 / 400 : ℝ) - (1467 / 3200 : ℝ)) ≤
      (1 / (53149468743062631 / 250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (53149468743062631 / 250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1467 / 3200 : ℝ) - Real.pi * Real.exp (733 / 400 : ℝ)) ≤
      (2 / (53149468743062631 / 250000000 : ℝ) : ℝ) := by
    rw [show (1467 / 3200 : ℝ) - Real.pi * Real.exp (733 / 400 : ℝ) =
      -(Real.pi * Real.exp (733 / 400 : ℝ) - (1467 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39315827638818913 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (39315827638818913 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1466_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (733 / 800 : ℝ) (1467 / 1600 : ℝ)) :
    (130677 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8417 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1466_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1466_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1467_leftExp :
    (31286538101 / 5000000000 : ℝ) ≤ Real.exp (1467 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1467 / 800 : ℝ) (264744604683 / 250000000000 : ℝ)
    (31286538101 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1467_rightExp :
    Real.exp (367 / 200 : ℝ) ≤ (62651341457 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (367 / 200 : ℝ) (529509892943 / 500000000000 : ℝ)
    (62651341457 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1467_denomUpper :
    Real.exp (192240640761921001 / 10000000000000000 : ℝ) ≤ (2233083425095265251 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (192240640761921001 / 10000000000000000 : ℝ) (1780751517
    / 976562500 : ℝ) (2233083425095265251 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1467_denomLower :
    (1089076006805230583 / 5000000000 : ℝ) ≤ Real.exp (11999473475724599 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11999473475724599 / 625000000000000 : ℝ) (227758853941 /
    125000000000 : ℝ) (1089076006805230583 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1467_product_lower :
    (12286192225724599 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1467 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1467_leftExp
    (by norm_num : (0 : ℝ) ≤ (31286538101 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1467_product_upper :
    Real.pi * Real.exp (367 / 200 : ℝ) ≤ (196825015761921001 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1467_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1467_endpointLower :
    (1023 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (1467 / 1600 : ℝ) (367 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12286192225724599 / 625000000000000 : ℝ) (Real.pi * Real.exp (1467 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1467_product_lower
  have hD : Real.exp (Real.pi * Real.exp (367 / 200 : ℝ) - (1467 / 3200 : ℝ)) ≤
      (2233083425095265251 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1467_denomUpper
    linarith [hpThetaJensenCell1467_product_upper]
  have hi : (1 / (2233083425095265251 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (367 / 200 : ℝ) - (1467 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2233083425095265251 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2233083425095265251 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1467 / 3200 : ℝ) - Real.pi * Real.exp (367 / 200 : ℝ)) := by
    rw [show (1467 / 3200 : ℝ) - Real.pi * Real.exp (367 / 200 : ℝ) =
      -(Real.pi * Real.exp (367 / 200 : ℝ) - (1467 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1467 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1467 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1467_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2233083425095265251 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1467_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1467 / 1600 : ℝ) (367 / 400 : ℝ) ≤ (131789 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (367 / 200 : ℝ)) (196825015761921001 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (367 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1467_product_upper
  have hD : (1089076006805230583 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1467 / 800 : ℝ) - (367 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1467_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1467_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1467 / 800 : ℝ) - (367 / 800 : ℝ)) ≤
      (1 / (1089076006805230583 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1089076006805230583 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((367 / 800 : ℝ) - Real.pi * Real.exp (1467 / 800 : ℝ)) ≤
      (2 / (1089076006805230583 / 5000000000 : ℝ) : ℝ) := by
    rw [show (367 / 800 : ℝ) - Real.pi * Real.exp (1467 / 800 : ℝ) =
      -(Real.pi * Real.exp (1467 / 800 : ℝ) - (367 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (196825015761921001 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (196825015761921001 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1467_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1467 / 1600 : ℝ) (367 / 400 : ℝ)) :
    (1023 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (131789 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1467_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1467_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1468_leftExp :
    (31325670727 / 5000000000 : ℝ) ≤ Real.exp (367 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (367 / 200 : ℝ) (211803957177 / 200000000000 : ℝ)
    (31325670727 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1468_rightExp :
    Real.exp (1469 / 800 : ℝ) ≤ (313648523 / 50000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1469 / 800 : ℝ) (529530577327 / 500000000000 : ℝ)
    (313648523 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1468_denomUpper :
    Real.exp (962418504317139 / 50000000000000 : ℝ) ≤ (1144012891669783667 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (962418504317139 / 50000000000000 : ℝ) (1824875134421 /
    1000000000000 : ℝ) (1144012891669783667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1468_denomLower :
    (2231674199890346237 / 10000000000 : ℝ) ≤ Real.exp (12014645506322173 / 625000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (12014645506322173 / 625000000000000 : ℝ) (91172679083 /
    50000000000 : ℝ) (2231674199890346237 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1468_product_lower :
    (12301559568822173 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (367 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1468_leftExp
    (by norm_num : (0 : ℝ) ≤ (31325670727 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1468_product_upper :
    Real.pi * Real.exp (1469 / 800 : ℝ) ≤ (985356004317139 / 50000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1468_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1468_endpointLower :
    (12513 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (367 / 400 : ℝ) (1469 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12301559568822173 / 625000000000000 : ℝ) (Real.pi * Real.exp (367 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1468_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1469 / 800 : ℝ) - (367 / 800 : ℝ)) ≤
      (1144012891669783667 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1468_denomUpper
    linarith [hpThetaJensenCell1468_product_upper]
  have hi : (1 / (1144012891669783667 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1469 / 800 : ℝ) - (367 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1144012891669783667 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1144012891669783667 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((367 / 800 : ℝ) - Real.pi * Real.exp (1469 / 800 : ℝ)) := by
    rw [show (367 / 800 : ℝ) - Real.pi * Real.exp (1469 / 800 : ℝ) =
      -(Real.pi * Real.exp (1469 / 800 : ℝ) - (367 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (367 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (367 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1468_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1144012891669783667 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1468_endpointUpper :
    hpThetaJensenKernelEndpointUpper (367 / 400 : ℝ) (1469 / 1600 : ℝ) ≤ (32241 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1469 / 800 : ℝ)) (985356004317139 / 50000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1469 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1468_product_upper
  have hD : (2231674199890346237 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (367 / 200 : ℝ) - (1469 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1468_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1468_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (367 / 200 : ℝ) - (1469 / 3200 : ℝ)) ≤
      (1 / (2231674199890346237 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2231674199890346237 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1469 / 3200 : ℝ) - Real.pi * Real.exp (367 / 200 : ℝ)) ≤
      (2 / (2231674199890346237 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1469 / 3200 : ℝ) - Real.pi * Real.exp (367 / 200 : ℝ) =
      -(Real.pi * Real.exp (367 / 200 : ℝ) - (1469 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (985356004317139 / 50000000000000 : ℝ) ^ 2 - 6 *
      (985356004317139 / 50000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1468_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (367 / 400 : ℝ) (1469 / 1600 : ℝ)) :
    (12513 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32241 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1468_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1468_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1469_leftExp :
    (62729704597 / 10000000000 : ℝ) ≤ Real.exp (1469 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1469 / 800 : ℝ) (1059061154653 / 1000000000000 : ℝ)
    (62729704597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1469_rightExp :
    Real.exp (147 / 80 : ℝ) ≤ (31404082879 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (147 / 80 : ℝ) (529551262519 / 500000000000 : ℝ)
    (31404082879 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1469_denomUpper :
    Real.exp (96363534444086247 / 5000000000000000 : ℝ) ≤ (2344392121073944407 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (96363534444086247 / 5000000000000000 : ℝ) (182626352561
    / 100000000000 : ℝ) (2344392121073944407 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1469_denomLower :
    (228658186791066971 / 1000000000 : ℝ) ≤ Real.exp (24059673515537303 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (24059673515537303 / 1250000000000000 : ℝ) (1824839134893
    / 1000000000000 : ℝ) (228658186791066971 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1469_product_lower :
    (24633892265537303 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1469 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1469_leftExp
    (by norm_num : (0 : ℝ) ≤ (62729704597 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1469_product_upper :
    Real.pi * Real.exp (147 / 80 : ℝ) ≤ (98658846944086247 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1469_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1469_endpointLower :
    (3061 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (1469 / 1600 : ℝ) (147 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24633892265537303 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1469 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1469_product_lower
  have hD : Real.exp (Real.pi * Real.exp (147 / 80 : ℝ) - (1469 / 3200 : ℝ)) ≤
      (2344392121073944407 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1469_denomUpper
    linarith [hpThetaJensenCell1469_product_upper]
  have hi : (1 / (2344392121073944407 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (147 / 80 : ℝ) - (1469 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2344392121073944407 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2344392121073944407 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1469 / 3200 : ℝ) - Real.pi * Real.exp (147 / 80 : ℝ)) := by
    rw [show (1469 / 3200 : ℝ) - Real.pi * Real.exp (147 / 80 : ℝ) =
      -(Real.pi * Real.exp (147 / 80 : ℝ) - (1469 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1469 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1469 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1469_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2344392121073944407 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1469_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1469 / 1600 : ℝ) (147 / 160 : ℝ) ≤ (25239 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (147 / 80 : ℝ)) (98658846944086247 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (147 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1469_product_upper
  have hD : (228658186791066971 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1469 / 800 : ℝ) - (147 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1469_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1469_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1469 / 800 : ℝ) - (147 / 320 : ℝ)) ≤
      (1 / (228658186791066971 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (228658186791066971 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((147 / 320 : ℝ) - Real.pi * Real.exp (1469 / 800 : ℝ)) ≤
      (2 / (228658186791066971 / 1000000000 : ℝ) : ℝ) := by
    rw [show (147 / 320 : ℝ) - Real.pi * Real.exp (1469 / 800 : ℝ) =
      -(Real.pi * Real.exp (1469 / 800 : ℝ) - (147 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (98658846944086247 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (98658846944086247 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1469_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1469 / 1600 : ℝ) (147 / 160 : ℝ)) :
    (3061 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (25239 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1469_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1469_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1470_leftExp :
    (12561633151 / 2000000000 : ℝ) ≤ Real.exp (147 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (147 / 80 : ℝ) (1059102525037 / 1000000000000 : ℝ)
    (12561633151 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1470_rightExp :
    Real.exp (1471 / 800 : ℝ) ≤ (12577345011 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1471 / 800 : ℝ) (1059143897039 / 1000000000000 : ℝ)
    (12577345011 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1470_denomUpper :
    Real.exp (38594149045142523 / 2000000000000000 : ℝ) ≤ (120111056312108107 / 500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (38594149045142523 / 2000000000000000 : ℝ) (1827654734011
    / 1000000000000 : ℝ) (120111056312108107 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1470_denomLower :
    (2342912615875602181 / 10000000000 : ℝ) ≤ Real.exp (4818018901764549 / 250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (4818018901764549 / 250000000000000 : ℝ) (365245499649 /
    200000000000 : ℝ) (2342912615875602181 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1470_product_lower :
    (4932940776764549 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (147 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1470_leftExp
    (by norm_num : (0 : ℝ) ≤ (12561633151 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1470_product_upper :
    Real.pi * Real.exp (1471 / 800 : ℝ) ≤ (39512899045142523 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1470_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1470_endpointLower :
    (29951 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (147 / 160 : ℝ) (1471 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4932940776764549 / 250000000000000 : ℝ) (Real.pi * Real.exp (147 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1470_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1471 / 800 : ℝ) - (147 / 320 : ℝ)) ≤
      (120111056312108107 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1470_denomUpper
    linarith [hpThetaJensenCell1470_product_upper]
  have hi : (1 / (120111056312108107 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1471 / 800 : ℝ) - (147 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (120111056312108107 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (120111056312108107 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((147 / 320 : ℝ) - Real.pi * Real.exp (1471 / 800 : ℝ)) := by
    rw [show (147 / 320 : ℝ) - Real.pi * Real.exp (1471 / 800 : ℝ) =
      -(Real.pi * Real.exp (1471 / 800 : ℝ) - (147 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (147 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (147 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1470_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (120111056312108107 / 500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1470_endpointUpper :
    hpThetaJensenKernelEndpointUpper (147 / 160 : ℝ) (1471 / 1600 : ℝ) ≤ (61741 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1471 / 800 : ℝ)) (39512899045142523 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1471 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1470_product_upper
  have hD : (2342912615875602181 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (147 / 80 : ℝ) - (1471 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1470_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1470_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (147 / 80 : ℝ) - (1471 / 3200 : ℝ)) ≤
      (1 / (2342912615875602181 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2342912615875602181 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1471 / 3200 : ℝ) - Real.pi * Real.exp (147 / 80 : ℝ)) ≤
      (2 / (2342912615875602181 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1471 / 3200 : ℝ) - Real.pi * Real.exp (147 / 80 : ℝ) =
      -(Real.pi * Real.exp (147 / 80 : ℝ) - (1471 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39512899045142523 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (39512899045142523 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1470_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (147 / 160 : ℝ) (1471 / 1600 : ℝ)) :
    (29951 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (61741 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1470_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1470_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1471_leftExp :
    (15721681263 / 2500000000 : ℝ) ≤ Real.exp (1471 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1471 / 800 : ℝ) (529571948519 / 500000000000 : ℝ)
    (15721681263 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1471_rightExp :
    Real.exp (46 / 25 : ℝ) ≤ (62965382611 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (46 / 25 : ℝ) (211837054131 / 200000000000 : ℝ)
    (62965382611 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1471_denomUpper :
    Real.exp (193214730253039323 / 10000000000000000 : ℝ) ≤ (246155258103597771 / 1000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (193214730253039323 / 10000000000000000 : ℝ)
    (365809753321 / 200000000000 : ℝ) (246155258103597771 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1471_denomLower :
    (2400705107283186189 / 10000000000 : ℝ) ≤ Real.exp (6030138510298837 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6030138510298837 / 312500000000000 : ℝ) (57113083711 /
    31250000000 : ℝ) (2400705107283186189 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1471_product_lower :
    (6173888510298837 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1471 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1471_leftExp
    (by norm_num : (0 : ℝ) ≤ (15721681263 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1471_product_upper :
    Real.pi * Real.exp (46 / 25 : ℝ) ≤ (197811605253039323 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1471_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1471_endpointLower :
    (117221 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1471 / 1600 : ℝ) (23 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6173888510298837 / 312500000000000 : ℝ) (Real.pi * Real.exp (1471 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1471_product_lower
  have hD : Real.exp (Real.pi * Real.exp (46 / 25 : ℝ) - (1471 / 3200 : ℝ)) ≤
      (246155258103597771 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1471_denomUpper
    linarith [hpThetaJensenCell1471_product_upper]
  have hi : (1 / (246155258103597771 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (46 / 25 : ℝ) - (1471 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (246155258103597771 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (246155258103597771 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1471 / 3200 : ℝ) - Real.pi * Real.exp (46 / 25 : ℝ)) := by
    rw [show (1471 / 3200 : ℝ) - Real.pi * Real.exp (46 / 25 : ℝ) =
      -(Real.pi * Real.exp (46 / 25 : ℝ) - (1471 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1471 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1471 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1471_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (246155258103597771 / 1000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1471_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1471 / 1600 : ℝ) (23 / 25 : ℝ) ≤ (120823 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (46 / 25 : ℝ)) (197811605253039323 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1471_product_upper
  have hD : (2400705107283186189 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1471 / 800 : ℝ) - (23 / 50 : ℝ)) := by
    apply le_trans hpThetaJensenCell1471_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1471_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1471 / 800 : ℝ) - (23 / 50 : ℝ)) ≤
      (1 / (2400705107283186189 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2400705107283186189 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 50 : ℝ) - Real.pi * Real.exp (1471 / 800 : ℝ)) ≤
      (2 / (2400705107283186189 / 10000000000 : ℝ) : ℝ) := by
    rw [show (23 / 50 : ℝ) - Real.pi * Real.exp (1471 / 800 : ℝ) =
      -(Real.pi * Real.exp (1471 / 800 : ℝ) - (23 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (197811605253039323 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (197811605253039323 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1471_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1471 / 1600 : ℝ) (23 / 25 : ℝ)) :
    (117221 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (120823 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1471_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1471_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1472_leftExp :
    (3935336413 / 625000000 : ℝ) ≤ Real.exp (46 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (46 / 25 : ℝ) (529592635327 / 500000000000 : ℝ)
    (3935336413 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1472_rightExp :
    Real.exp (1473 / 800 : ℝ) ≤ (7880517319 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1473 / 800 : ℝ) (8275208171 / 7812500000 : ℝ)
    (7880517319 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1472_denomUpper :
    Real.exp (24182378045749167 / 1250000000000000 : ℝ) ≤ (504485480403596477 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (24182378045749167 / 1250000000000000 : ℝ) (915222815251
    / 500000000000 : ℝ) (504485480403596477 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1472_denomLower :
    (307499887403886821 / 1250000000 : ℝ) ≤ Real.exp (1509440759986187 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1509440759986187 / 78125000000000 : ℝ) (457253170849 /
    250000000000 : ℝ) (307499887403886821 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1472_product_lower :
    (1545402674048687 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (46 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1472_leftExp
    (by norm_num : (0 : ℝ) ≤ (3935336413 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1472_product_upper :
    Real.pi * Real.exp (1473 / 800 : ℝ) ≤ (24757378045749167 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1472_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1472_endpointLower :
    (11469 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 25 : ℝ) (1473 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1545402674048687 / 78125000000000 : ℝ) (Real.pi * Real.exp (46 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1472_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1473 / 800 : ℝ) - (23 / 50 : ℝ)) ≤
      (504485480403596477 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1472_denomUpper
    linarith [hpThetaJensenCell1472_product_upper]
  have hi : (1 / (504485480403596477 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1473 / 800 : ℝ) - (23 / 50 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (504485480403596477 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (504485480403596477 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 50 : ℝ) - Real.pi * Real.exp (1473 / 800 : ℝ)) := by
    rw [show (23 / 50 : ℝ) - Real.pi * Real.exp (1473 / 800 : ℝ) =
      -(Real.pi * Real.exp (1473 / 800 : ℝ) - (23 / 50 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (46 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (46 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1472_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (504485480403596477 / 2000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1472_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 25 : ℝ) (1473 / 1600 : ℝ) ≤ (59109 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1473 / 800 : ℝ)) (24757378045749167 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1473 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1472_product_upper
  have hD : (307499887403886821 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (46 / 25 : ℝ) - (1473 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1472_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1472_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (46 / 25 : ℝ) - (1473 / 3200 : ℝ)) ≤
      (1 / (307499887403886821 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (307499887403886821 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1473 / 3200 : ℝ) - Real.pi * Real.exp (46 / 25 : ℝ)) ≤
      (2 / (307499887403886821 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1473 / 3200 : ℝ) - Real.pi * Real.exp (46 / 25 : ℝ) =
      -(Real.pi * Real.exp (46 / 25 : ℝ) - (1473 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24757378045749167 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (24757378045749167 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1472_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 25 : ℝ) (1473 / 1600 : ℝ)) :
    (11469 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (59109 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1472_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1472_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1473_leftExp :
    (63044138549 / 10000000000 : ℝ) ≤ Real.exp (1473 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1473 / 800 : ℝ) (1059226645887 / 1000000000000 : ℝ)
    (63044138549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1473_rightExp :
    Real.exp (737 / 400 : ℝ) ≤ (63122992999 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (737 / 400 : ℝ) (1059268022737 / 1000000000000 : ℝ)
    (63122992999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1473_denomUpper :
    Real.exp (193703627944707407 / 10000000000000000 : ℝ) ≤ (2584887664990071129 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (193703627944707407 / 10000000000000000 : ℝ) (91592266637
    / 50000000000 : ℝ) (2584887664990071129 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1473_denomLower :
    (504167096468633023 / 2000000000 : ℝ) ≤ Real.exp (24181588914053751 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (24181588914053751 / 1250000000000000 : ℝ) (366081903857
    / 200000000000 : ℝ) (504167096468633023 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1473_product_lower :
    (24757370164053751 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1473 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1473_leftExp
    (by norm_num : (0 : ℝ) ≤ (63044138549 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1473_product_upper :
    Real.pi * Real.exp (737 / 400 : ℝ) ≤ (198306752944707407 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1473_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1473_endpointLower :
    (11221 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1473 / 1600 : ℝ) (737 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24757370164053751 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1473 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1473_product_lower
  have hD : Real.exp (Real.pi * Real.exp (737 / 400 : ℝ) - (1473 / 3200 : ℝ)) ≤
      (2584887664990071129 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1473_denomUpper
    linarith [hpThetaJensenCell1473_product_upper]
  have hi : (1 / (2584887664990071129 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (737 / 400 : ℝ) - (1473 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2584887664990071129 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2584887664990071129 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1473 / 3200 : ℝ) - Real.pi * Real.exp (737 / 400 : ℝ)) := by
    rw [show (1473 / 3200 : ℝ) - Real.pi * Real.exp (737 / 400 : ℝ) =
      -(Real.pi * Real.exp (737 / 400 : ℝ) - (1473 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1473 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1473 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1473_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2584887664990071129 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1473_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1473 / 1600 : ℝ) (737 / 800 : ℝ) ≤ (57833 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (737 / 400 : ℝ)) (198306752944707407 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (737 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1473_product_upper
  have hD : (504167096468633023 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1473 / 800 : ℝ) - (737 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1473_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1473_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1473 / 800 : ℝ) - (737 / 1600 : ℝ)) ≤
      (1 / (504167096468633023 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (504167096468633023 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((737 / 1600 : ℝ) - Real.pi * Real.exp (1473 / 800 : ℝ)) ≤
      (2 / (504167096468633023 / 2000000000 : ℝ) : ℝ) := by
    rw [show (737 / 1600 : ℝ) - Real.pi * Real.exp (1473 / 800 : ℝ) =
      -(Real.pi * Real.exp (1473 / 800 : ℝ) - (737 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (198306752944707407 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (198306752944707407 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1473_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1473 / 1600 : ℝ) (737 / 800 : ℝ)) :
    (11221 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (57833 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1473_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1473_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1474_leftExp :
    (15780748249 / 2500000000 : ℝ) ≤ Real.exp (737 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (737 / 400 : ℝ) (66204251421 / 62500000000 : ℝ)
    (15780748249 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1474_rightExp :
    Real.exp (59 / 32 : ℝ) ≤ (2528077843 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 32 : ℝ) (529654700601 / 500000000000 : ℝ)
    (2528077843 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1474_denomUpper :
    Real.exp (7757941655023899 / 400000000000000 : ℝ) ≤ (16556104029629823 / 62500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7757941655023899 / 400000000000000 : ℝ) (1833247880411 /
    1000000000000 : ℝ) (16556104029629823 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1474_denomLower :
    (2583256305877168271 / 10000000000 : ℝ) ≤ Real.exp (6053041087884051 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6053041087884051 / 312500000000000 : ℝ) (915904596729 /
    500000000000 : ℝ) (2583256305877168271 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1474_product_lower :
    (6197084056634051 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (737 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1474_leftExp
    (by norm_num : (0 : ℝ) ≤ (15780748249 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1474_product_upper :
    Real.pi * Real.exp (59 / 32 : ℝ) ≤ (7942191655023899 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1474_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1474_endpointLower :
    (109781 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (737 / 800 : ℝ) (59 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6197084056634051 / 312500000000000 : ℝ) (Real.pi * Real.exp (737 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1474_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 32 : ℝ) - (737 / 1600 : ℝ)) ≤
      (16556104029629823 / 62500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1474_denomUpper
    linarith [hpThetaJensenCell1474_product_upper]
  have hi : (1 / (16556104029629823 / 62500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 32 : ℝ) - (737 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16556104029629823 / 62500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16556104029629823 / 62500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((737 / 1600 : ℝ) - Real.pi * Real.exp (59 / 32 : ℝ)) := by
    rw [show (737 / 1600 : ℝ) - Real.pi * Real.exp (59 / 32 : ℝ) =
      -(Real.pi * Real.exp (59 / 32 : ℝ) - (737 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (737 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (737 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1474_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16556104029629823 / 62500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1474_endpointUpper :
    hpThetaJensenKernelEndpointUpper (737 / 800 : ℝ) (59 / 64 : ℝ) ≤ (22633 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 32 : ℝ)) (7942191655023899 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1474_product_upper
  have hD : (2583256305877168271 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (737 / 400 : ℝ) - (59 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1474_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1474_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (737 / 400 : ℝ) - (59 / 128 : ℝ)) ≤
      (1 / (2583256305877168271 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2583256305877168271 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 128 : ℝ) - Real.pi * Real.exp (737 / 400 : ℝ)) ≤
      (2 / (2583256305877168271 / 10000000000 : ℝ) : ℝ) := by
    rw [show (59 / 128 : ℝ) - Real.pi * Real.exp (737 / 400 : ℝ) =
      -(Real.pi * Real.exp (737 / 400 : ℝ) - (59 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7942191655023899 / 400000000000000 : ℝ) ^ 2 - 6 *
      (7942191655023899 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1474_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (737 / 800 : ℝ) (59 / 64 : ℝ)) :
    (109781 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22633 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1474_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1474_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1475_leftExp :
    (7900243259 / 1250000000 : ℝ) ≤ Real.exp (59 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 32 : ℝ) (1059309401201 / 1000000000000 : ℝ)
    (7900243259 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1475_rightExp :
    Real.exp (369 / 200 : ℝ) ≤ (31640498953 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (369 / 200 : ℝ) (264837695321 / 250000000000 : ℝ)
    (31640498953 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1475_denomUpper :
    Real.exp (97096882527252129 / 5000000000000000 : ℝ) ≤ (1357369425816198899 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (97096882527252129 / 5000000000000000 : ℝ) (1834653280681
    / 1000000000000 : ℝ) (1357369425816198899 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1475_denomLower :
    (2647304817278028733 / 10000000000 : ℝ) ≤ Real.exp (3030347315066041 / 156250000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (3030347315066041 / 156250000000000 : ℝ) (1833211713007 /
    1000000000000 : ℝ) (2647304817278028733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1475_product_lower :
    (3102417627566041 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1475_leftExp
    (by norm_num : (0 : ℝ) ≤ (7900243259 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1475_product_upper :
    Real.pi * Real.exp (369 / 200 : ℝ) ≤ (99401570027252129 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1475_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1475_endpointLower :
    (537 / 50000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 64 : ℝ) (369 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3102417627566041 / 156250000000000 : ℝ) (Real.pi * Real.exp (59 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1475_product_lower
  have hD : Real.exp (Real.pi * Real.exp (369 / 200 : ℝ) - (59 / 128 : ℝ)) ≤
      (1357369425816198899 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1475_denomUpper
    linarith [hpThetaJensenCell1475_product_upper]
  have hi : (1 / (1357369425816198899 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (369 / 200 : ℝ) - (59 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1357369425816198899 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1357369425816198899 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 128 : ℝ) - Real.pi * Real.exp (369 / 200 : ℝ)) := by
    rw [show (59 / 128 : ℝ) - Real.pi * Real.exp (369 / 200 : ℝ) =
      -(Real.pi * Real.exp (369 / 200 : ℝ) - (59 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1475_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1357369425816198899 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1475_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 64 : ℝ) (369 / 400 : ℝ) ≤ (22143 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (369 / 200 : ℝ)) (99401570027252129 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (369 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1475_product_upper
  have hD : (2647304817278028733 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 32 : ℝ) - (369 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1475_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1475_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 32 : ℝ) - (369 / 800 : ℝ)) ≤
      (1 / (2647304817278028733 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2647304817278028733 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((369 / 800 : ℝ) - Real.pi * Real.exp (59 / 32 : ℝ)) ≤
      (2 / (2647304817278028733 / 10000000000 : ℝ) : ℝ) := by
    rw [show (369 / 800 : ℝ) - Real.pi * Real.exp (59 / 32 : ℝ) =
      -(Real.pi * Real.exp (59 / 32 : ℝ) - (369 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (99401570027252129 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (99401570027252129 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1475_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 64 : ℝ) (369 / 400 : ℝ)) :
    (537 / 50000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (22143 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1475_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1475_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1476_leftExp :
    (63280997903 / 10000000000 : ℝ) ≤ Real.exp (369 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (369 / 200 : ℝ) (1059350781283 / 1000000000000 : ℝ)
    (63280997903 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1476_rightExp :
    Real.exp (1477 / 800 : ℝ) ≤ (15840037153 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1477 / 800 : ℝ) (529696081491 / 500000000000 : ℝ)
    (15840037153 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1476_denomUpper :
    Real.exp (48609824839604729 / 2500000000000000 : ℝ) ≤ (1391110030228677231 / 5000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (48609824839604729 / 2500000000000000 : ℝ) (587539693 /
    320000000 : ℝ) (1391110030228677231 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1476_denomLower :
    (1356512749368306543 / 5000000000 : ℝ) ≤ Real.exp (24273431470510197 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (24273431470510197 / 1250000000000000 : ℝ) (1834617085097
    / 1000000000000 : ℝ) (1356512749368306543 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1476_product_lower :
    (24850384595510197 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (369 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1476_leftExp
    (by norm_num : (0 : ℝ) ≤ (63280997903 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1476_product_upper :
    Real.pi * Real.exp (1477 / 800 : ℝ) ≤ (49762949839604729 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1476_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1476_endpointLower :
    (26267 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (369 / 400 : ℝ) (1477 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24850384595510197 / 1250000000000000 : ℝ) (Real.pi * Real.exp (369 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1476_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1477 / 800 : ℝ) - (369 / 800 : ℝ)) ≤
      (1391110030228677231 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1476_denomUpper
    linarith [hpThetaJensenCell1476_product_upper]
  have hi : (1 / (1391110030228677231 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1477 / 800 : ℝ) - (369 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1391110030228677231 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1391110030228677231 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((369 / 800 : ℝ) - Real.pi * Real.exp (1477 / 800 : ℝ)) := by
    rw [show (369 / 800 : ℝ) - Real.pi * Real.exp (1477 / 800 : ℝ) =
      -(Real.pi * Real.exp (1477 / 800 : ℝ) - (369 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (369 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (369 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1476_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1391110030228677231 / 5000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1476_endpointUpper :
    hpThetaJensenKernelEndpointUpper (369 / 400 : ℝ) (1477 / 1600 : ℝ) ≤ (54157 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1477 / 800 : ℝ)) (49762949839604729 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1477 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1476_product_upper
  have hD : (1356512749368306543 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (369 / 200 : ℝ) - (1477 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1476_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1476_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (369 / 200 : ℝ) - (1477 / 3200 : ℝ)) ≤
      (1 / (1356512749368306543 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1356512749368306543 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1477 / 3200 : ℝ) - Real.pi * Real.exp (369 / 200 : ℝ)) ≤
      (2 / (1356512749368306543 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1477 / 3200 : ℝ) - Real.pi * Real.exp (369 / 200 : ℝ) =
      -(Real.pi * Real.exp (369 / 200 : ℝ) - (1477 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49762949839604729 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (49762949839604729 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1476_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (369 / 400 : ℝ) (1477 / 1600 : ℝ)) :
    (26267 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (54157 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1476_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1476_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1477_leftExp :
    (63360148609 / 10000000000 : ℝ) ≤ Real.exp (1477 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1477 / 800 : ℝ) (1059392162981 / 1000000000000 : ℝ)
    (63360148609 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1477_rightExp :
    Real.exp (739 / 400 : ℝ) ≤ (63439398319 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (739 / 400 : ℝ) (1059433546297 / 1000000000000 : ℝ)
    (63439398319 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1477_denomUpper :
    Real.exp (194685144683182167 / 10000000000000000 : ℝ) ≤ (2851467358403337141 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (194685144683182167 / 10000000000000000 : ℝ)
    (1837472667447 / 1000000000000 : ℝ) (2851467358403337141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1477_denomLower :
    (1390232048059444023 / 5000000000 : ℝ) ≤ Real.exp (24304123248605691 / 1250000000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_lower_scaled32 (24304123248605691 / 1250000000000000 : ℝ) (1836025316803
    / 1000000000000 : ℝ) (1390232048059444023 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1477_product_lower :
    (24881466998605691 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1477 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1477_leftExp
    (by norm_num : (0 : ℝ) ≤ (63360148609 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1477_product_upper :
    Real.pi * Real.exp (739 / 400 : ℝ) ≤ (199300769683182167 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1477_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1477_endpointLower :
    (803 / 78125000 : ℝ) ≤ hpThetaTraceEndpointLower (1477 / 1600 : ℝ) (739 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (24881466998605691 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1477 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1477_product_lower
  have hD : Real.exp (Real.pi * Real.exp (739 / 400 : ℝ) - (1477 / 3200 : ℝ)) ≤
      (2851467358403337141 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1477_denomUpper
    linarith [hpThetaJensenCell1477_product_upper]
  have hi : (1 / (2851467358403337141 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (739 / 400 : ℝ) - (1477 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2851467358403337141 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2851467358403337141 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1477 / 3200 : ℝ) - Real.pi * Real.exp (739 / 400 : ℝ)) := by
    rw [show (1477 / 3200 : ℝ) - Real.pi * Real.exp (739 / 400 : ℝ) =
      -(Real.pi * Real.exp (739 / 400 : ℝ) - (1477 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1477 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1477 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1477_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2851467358403337141 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1477_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1477 / 1600 : ℝ) (739 / 800 : ℝ) ≤ (105963 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (739 / 400 : ℝ)) (199300769683182167 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (739 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1477_product_upper
  have hD : (1390232048059444023 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1477 / 800 : ℝ) - (739 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1477_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1477_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1477 / 800 : ℝ) - (739 / 1600 : ℝ)) ≤
      (1 / (1390232048059444023 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1390232048059444023 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((739 / 1600 : ℝ) - Real.pi * Real.exp (1477 / 800 : ℝ)) ≤
      (2 / (1390232048059444023 / 5000000000 : ℝ) : ℝ) := by
    rw [show (739 / 1600 : ℝ) - Real.pi * Real.exp (1477 / 800 : ℝ) =
      -(Real.pi * Real.exp (1477 / 800 : ℝ) - (739 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (199300769683182167 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (199300769683182167 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1477_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1477 / 1600 : ℝ) (739 / 800 : ℝ)) :
    (803 / 78125000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (105963 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1477_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1477_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1478_leftExp :
    (15859849579 / 2500000000 : ℝ) ≤ Real.exp (739 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (739 / 400 : ℝ) (132429193287 / 125000000000 : ℝ)
    (15859849579 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1478_rightExp :
    Real.exp (1479 / 800 : ℝ) ≤ (63518747149 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1479 / 800 : ℝ) (264868732807 / 250000000000 : ℝ)
    (63518747149 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1478_denomUpper :
    Real.exp (194931301412068357 / 10000000000000000 : ℝ) ≤ (2922529175164991851 / 10000000000 :
      ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (194931301412068357 / 10000000000000000 : ℝ)
    (229860833537 / 125000000000 : ℝ) (2922529175164991851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1478_denomLower :
    (2849667666906592891 / 10000000000 : ℝ) ≤ Real.exp (6083713476073721 / 312500000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (6083713476073721 / 312500000000000 : ℝ) (183743641533 /
    100000000000 : ℝ) (2849667666906592891 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1478_product_lower :
    (6228147069823721 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (739 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1478_leftExp
    (by norm_num : (0 : ℝ) ≤ (15859849579 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1478_product_upper :
    Real.pi * Real.exp (1479 / 800 : ℝ) ≤ (199550051412068357 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1478_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1478_endpointLower :
    (50273 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (739 / 800 : ℝ) (1479 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6228147069823721 / 312500000000000 : ℝ) (Real.pi * Real.exp (739 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1478_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1479 / 800 : ℝ) - (739 / 1600 : ℝ)) ≤
      (2922529175164991851 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1478_denomUpper
    linarith [hpThetaJensenCell1478_product_upper]
  have hi : (1 / (2922529175164991851 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1479 / 800 : ℝ) - (739 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2922529175164991851 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2922529175164991851 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((739 / 1600 : ℝ) - Real.pi * Real.exp (1479 / 800 : ℝ)) := by
    rw [show (739 / 1600 : ℝ) - Real.pi * Real.exp (1479 / 800 : ℝ) =
      -(Real.pi * Real.exp (1479 / 800 : ℝ) - (739 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (739 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (739 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1478_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2922529175164991851 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1478_endpointUpper :
    hpThetaJensenKernelEndpointUpper (739 / 800 : ℝ) (1479 / 1600 : ℝ) ≤ (103659 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1479 / 800 : ℝ)) (199550051412068357 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1479 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1478_product_upper
  have hD : (2849667666906592891 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (739 / 400 : ℝ) - (1479 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1478_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1478_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (739 / 400 : ℝ) - (1479 / 3200 : ℝ)) ≤
      (1 / (2849667666906592891 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2849667666906592891 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1479 / 3200 : ℝ) - Real.pi * Real.exp (739 / 400 : ℝ)) ≤
      (2 / (2849667666906592891 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1479 / 3200 : ℝ) - Real.pi * Real.exp (739 / 400 : ℝ) =
      -(Real.pi * Real.exp (739 / 400 : ℝ) - (1479 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (199550051412068357 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (199550051412068357 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1478_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (739 / 800 : ℝ) (1479 / 1600 : ℝ)) :
    (50273 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (103659 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1478_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1478_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1479_leftExp :
    (31759373573 / 5000000000 : ℝ) ≤ Real.exp (1479 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1479 / 800 : ℝ) (1059474931227 / 1000000000000 : ℝ)
    (31759373573 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1479_rightExp :
    Real.exp (37 / 20 : ℝ) ≤ (15899548807 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 20 : ℝ) (66219769861 / 62500000000 : ℝ)
    (15899548807 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1479_denomUpper :
    Real.exp (48794442485229551 / 2500000000000000 : ℝ) ≤ (748863832572256077 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (48794442485229551 / 2500000000000000 : ℝ) (368060710083
    / 200000000000 : ℝ) (748863832572256077 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1479_denomLower :
    (1460342305071608607 / 5000000000 : ℝ) ≤ Real.exp (12182811742743527 / 625000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12182811742743527 / 625000000000000 : ℝ) (919425193913 /
    500000000000 : ℝ) (1460342305071608607 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1479_product_lower :
    (12471874242743527 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1479 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1479_leftExp
    (by norm_num : (0 : ℝ) ≤ (31759373573 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1479_product_upper :
    Real.pi * Real.exp (37 / 20 : ℝ) ≤ (49949911235229551 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1479_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1479_endpointLower :
    (49177 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1479 / 1600 : ℝ) (37 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12471874242743527 / 625000000000000 : ℝ) (Real.pi * Real.exp (1479 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1479_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 20 : ℝ) - (1479 / 3200 : ℝ)) ≤
      (748863832572256077 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1479_denomUpper
    linarith [hpThetaJensenCell1479_product_upper]
  have hi : (1 / (748863832572256077 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 20 : ℝ) - (1479 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (748863832572256077 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (748863832572256077 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1479 / 3200 : ℝ) - Real.pi * Real.exp (37 / 20 : ℝ)) := by
    rw [show (1479 / 3200 : ℝ) - Real.pi * Real.exp (37 / 20 : ℝ) =
      -(Real.pi * Real.exp (37 / 20 : ℝ) - (1479 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1479 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1479 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1479_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (748863832572256077 / 2500000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1479_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1479 / 1600 : ℝ) (37 / 40 : ℝ) ≤ (50701 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 20 : ℝ)) (49949911235229551 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1479_product_upper
  have hD : (1460342305071608607 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1479 / 800 : ℝ) - (37 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell1479_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1479_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1479 / 800 : ℝ) - (37 / 80 : ℝ)) ≤
      (1 / (1460342305071608607 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1460342305071608607 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 80 : ℝ) - Real.pi * Real.exp (1479 / 800 : ℝ)) ≤
      (2 / (1460342305071608607 / 5000000000 : ℝ) : ℝ) := by
    rw [show (37 / 80 : ℝ) - Real.pi * Real.exp (1479 / 800 : ℝ) =
      -(Real.pi * Real.exp (1479 / 800 : ℝ) - (37 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49949911235229551 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (49949911235229551 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1479_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1479 / 1600 : ℝ) (37 / 40 : ℝ)) :
    (49177 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (50701 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1479_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1479_endpointUpper

def hpThetaJensenCellsBatch073Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (148727 / 10000000000 : ℝ)
  | 1 => (29113 / 2000000000 : ℝ)
  | 2 => (142467 / 10000000000 : ℝ)
  | 3 => (139429 / 10000000000 : ℝ)
  | 4 => (136453 / 10000000000 : ℝ)
  | 5 => (4173 / 312500000 : ℝ)
  | 6 => (130677 / 10000000000 : ℝ)
  | 7 => (1023 / 80000000 : ℝ)
  | 8 => (12513 / 1000000000 : ℝ)
  | 9 => (3061 / 250000000 : ℝ)
  | 10 => (29951 / 2500000000 : ℝ)
  | 11 => (117221 / 10000000000 : ℝ)
  | 12 => (11469 / 1000000000 : ℝ)
  | 13 => (11221 / 1000000000 : ℝ)
  | 14 => (109781 / 10000000000 : ℝ)
  | 15 => (537 / 50000000 : ℝ)
  | 16 => (26267 / 2500000000 : ℝ)
  | 17 => (803 / 78125000 : ℝ)
  | 18 => (50273 / 5000000000 : ℝ)
  | 19 => (49177 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch073Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (76623 / 5000000000 : ℝ)
  | 1 => (149993 / 10000000000 : ℝ)
  | 2 => (36701 / 2500000000 : ℝ)
  | 3 => (143679 / 10000000000 : ℝ)
  | 4 => (17577 / 1250000000 : ℝ)
  | 5 => (68807 / 5000000000 : ℝ)
  | 6 => (8417 / 625000000 : ℝ)
  | 7 => (131789 / 10000000000 : ℝ)
  | 8 => (32241 / 2500000000 : ℝ)
  | 9 => (25239 / 2000000000 : ℝ)
  | 10 => (61741 / 5000000000 : ℝ)
  | 11 => (120823 / 10000000000 : ℝ)
  | 12 => (59109 / 5000000000 : ℝ)
  | 13 => (57833 / 5000000000 : ℝ)
  | 14 => (22633 / 2000000000 : ℝ)
  | 15 => (22143 / 2000000000 : ℝ)
  | 16 => (54157 / 5000000000 : ℝ)
  | 17 => (105963 / 10000000000 : ℝ)
  | 18 => (103659 / 10000000000 : ℝ)
  | 19 => (50701 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch073_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch073Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch073Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1460_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1461_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1462_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1463_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1464_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1465_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1466_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1467_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1468_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1469_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1470_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1471_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1472_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1473_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1474_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1475_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1476_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1477_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1478_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1479_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper] at h ⊢
    exact h

end HodgeProofHP
