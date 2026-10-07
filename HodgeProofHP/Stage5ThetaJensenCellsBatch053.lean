import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1060_leftExp :
    (37621853549 / 10000000000 : ℝ) ≤ Real.exp (53 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 40 : ℝ) (260568860987 / 250000000000 : ℝ)
    (37621853549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1060_rightExp :
    Real.exp (1061 / 800 : ℝ) ≤ (588576723 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1061 / 800 : ℝ) (260579039657 / 250000000000 : ℝ)
    (588576723 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1060_denomUpper :
    Real.exp (1797310700439739 / 156250000000000 : ℝ) ≤ (989914223885517 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1797310700439739 / 156250000000000 : ℝ) (1432558691417 /
    1000000000000 : ℝ) (989914223885517 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1060_denomLower :
    (975079228283377 / 10000000000 : ℝ) ≤ Real.exp (14359611141838751 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14359611141838751 / 1250000000000000 : ℝ) (17898536019 /
    12500000000 : ℝ) (975079228283377 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1060_product_lower :
    (14774064266838751 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1060_leftExp
    (by norm_num : (0 : ℝ) ≤ (37621853549 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1060_product_upper :
    Real.pi * Real.exp (1061 / 800 : ℝ) ≤ (1849068512939739 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1060_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1060_endpointLower :
    (98566783 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 80 : ℝ) (1061 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14774064266838751 / 1250000000000000 : ℝ) (Real.pi * Real.exp (53 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1060_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1061 / 800 : ℝ) - (53 / 160 : ℝ)) ≤
      (989914223885517 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1060_denomUpper
    linarith [hpThetaJensenCell1060_product_upper]
  have hi : (1 / (989914223885517 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1061 / 800 : ℝ) - (53 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (989914223885517 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (989914223885517 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 160 : ℝ) - Real.pi * Real.exp (1061 / 800 : ℝ)) := by
    rw [show (53 / 160 : ℝ) - Real.pi * Real.exp (1061 / 800 : ℝ) =
      -(Real.pi * Real.exp (1061 / 800 : ℝ) - (53 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1060_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (989914223885517 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1060_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 80 : ℝ) (1061 / 1600 : ℝ) ≤ (100599393 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1061 / 800 : ℝ)) (1849068512939739 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1061 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1060_product_upper
  have hD : (975079228283377 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 40 : ℝ) - (1061 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1060_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1060_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 40 : ℝ) - (1061 / 3200 : ℝ)) ≤
      (1 / (975079228283377 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (975079228283377 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1061 / 3200 : ℝ) - Real.pi * Real.exp (53 / 40 : ℝ)) ≤
      (2 / (975079228283377 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1061 / 3200 : ℝ) - Real.pi * Real.exp (53 / 40 : ℝ) =
      -(Real.pi * Real.exp (53 / 40 : ℝ) - (1061 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1849068512939739 / 156250000000000 : ℝ) ^ 2 - 6 *
      (1849068512939739 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1060_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 80 : ℝ) (1061 / 1600 : ℝ)) :
    (98566783 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (100599393 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1060_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1060_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1061_leftExp :
    (3766891027 / 1000000000 : ℝ) ≤ Real.exp (1061 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1061 / 800 : ℝ) (1042316158627 / 1000000000000 : ℝ)
    (3766891027 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1061_rightExp :
    Real.exp (531 / 400 : ℝ) ≤ (9429006463 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (531 / 400 : ℝ) (1042356874899 / 1000000000000 : ℝ)
    (9429006463 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1061_denomUpper :
    Real.exp (28793194451115559 / 2500000000000000 : ℝ) ≤ (125545225072191 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (28793194451115559 / 2500000000000000 : ℝ) (143320748733
    / 100000000000 : ℝ) (125545225072191 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1061_denomLower :
    (247322998396193 / 2500000000 : ℝ) ≤ Real.exp (1437769964411873 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1437769964411873 / 125000000000000 : ℝ) (179066317921 /
    125000000000 : ℝ) (247322998396193 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1061_product_lower :
    (1479254339411873 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1061 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1061_leftExp
    (by norm_num : (0 : ℝ) ≤ (3766891027 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1061_product_upper :
    Real.pi * Real.exp (531 / 400 : ℝ) ≤ (29622100701115559 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1061_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1061_endpointLower :
    (48704889 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1061 / 1600 : ℝ) (531 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1479254339411873 / 125000000000000 : ℝ) (Real.pi * Real.exp (1061 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1061_product_lower
  have hD : Real.exp (Real.pi * Real.exp (531 / 400 : ℝ) - (1061 / 3200 : ℝ)) ≤
      (125545225072191 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1061_denomUpper
    linarith [hpThetaJensenCell1061_product_upper]
  have hi : (1 / (125545225072191 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (531 / 400 : ℝ) - (1061 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (125545225072191 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (125545225072191 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1061 / 3200 : ℝ) - Real.pi * Real.exp (531 / 400 : ℝ)) := by
    rw [show (1061 / 3200 : ℝ) - Real.pi * Real.exp (531 / 400 : ℝ) =
      -(Real.pi * Real.exp (531 / 400 : ℝ) - (1061 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1061 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1061 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1061_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (125545225072191 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1061_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1061 / 1600 : ℝ) (531 / 800 : ℝ) ≤ (99420341 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (531 / 400 : ℝ)) (29622100701115559 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (531 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1061_product_upper
  have hD : (247322998396193 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1061 / 800 : ℝ) - (531 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1061_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1061_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1061 / 800 : ℝ) - (531 / 1600 : ℝ)) ≤
      (1 / (247322998396193 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (247322998396193 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((531 / 1600 : ℝ) - Real.pi * Real.exp (1061 / 800 : ℝ)) ≤
      (2 / (247322998396193 / 2500000000 : ℝ) : ℝ) := by
    rw [show (531 / 1600 : ℝ) - Real.pi * Real.exp (1061 / 800 : ℝ) =
      -(Real.pi * Real.exp (1061 / 800 : ℝ) - (531 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (29622100701115559 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (29622100701115559 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1061_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1061 / 1600 : ℝ) (531 / 800 : ℝ)) :
    (48704889 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (99420341 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1061_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1061_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1062_leftExp :
    (754320517 / 200000000 : ℝ) ≤ Real.exp (531 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (531 / 400 : ℝ) (521178437449 / 500000000000 : ℝ)
    (754320517 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1062_rightExp :
    Real.exp (1063 / 800 : ℝ) ≤ (37763200361 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1063 / 800 : ℝ) (1042397592759 / 1000000000000 : ℝ)
    (37763200361 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1062_denomUpper :
    Real.exp (115317855911715073 / 10000000000000000 : ℝ) ≤ (1019039101778687 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (115317855911715073 / 10000000000000000 : ℝ)
    (358464351653 / 250000000000 : ℝ) (1019039101778687 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1062_denomLower :
    (2509326210593 / 25000000 : ℝ) ≤ Real.exp (287916225205383 / 25000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (287916225205383 / 25000000000000 : ℝ) (716589663161 /
    500000000000 : ℝ) (2509326210593 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1062_product_lower :
    (296220912705383 / 25000000000000 : ℝ) ≤ Real.pi * Real.exp (531 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1062_leftExp
    (by norm_num : (0 : ℝ) ≤ (754320517 / 200000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1062_product_upper :
    Real.pi * Real.exp (1063 / 800 : ℝ) ≤ (118636605911715073 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1062_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1062_endpointLower :
    (48132273 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (531 / 800 : ℝ) (1063 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (296220912705383 / 25000000000000 : ℝ) (Real.pi * Real.exp (531 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1062_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1063 / 800 : ℝ) - (531 / 1600 : ℝ)) ≤
      (1019039101778687 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1062_denomUpper
    linarith [hpThetaJensenCell1062_product_upper]
  have hi : (1 / (1019039101778687 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1063 / 800 : ℝ) - (531 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1019039101778687 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1019039101778687 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((531 / 1600 : ℝ) - Real.pi * Real.exp (1063 / 800 : ℝ)) := by
    rw [show (531 / 1600 : ℝ) - Real.pi * Real.exp (1063 / 800 : ℝ) =
      -(Real.pi * Real.exp (1063 / 800 : ℝ) - (531 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (531 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (531 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1062_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1019039101778687 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1062_endpointUpper :
    hpThetaJensenKernelEndpointUpper (531 / 800 : ℝ) (1063 / 1600 : ℝ) ≤ (19650653 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1063 / 800 : ℝ)) (118636605911715073 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1063 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1062_product_upper
  have hD : (2509326210593 / 25000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (531 / 400 : ℝ) - (1063 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1062_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1062_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (531 / 400 : ℝ) - (1063 / 3200 : ℝ)) ≤
      (1 / (2509326210593 / 25000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2509326210593 / 25000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1063 / 3200 : ℝ) - Real.pi * Real.exp (531 / 400 : ℝ)) ≤
      (2 / (2509326210593 / 25000000 : ℝ) : ℝ) := by
    rw [show (1063 / 3200 : ℝ) - Real.pi * Real.exp (531 / 400 : ℝ) =
      -(Real.pi * Real.exp (531 / 400 : ℝ) - (1063 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (118636605911715073 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (118636605911715073 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1062_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (531 / 800 : ℝ) (1063 / 1600 : ℝ)) :
    (48132273 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (19650653 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1062_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1062_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1063_leftExp :
    (37763200359 / 10000000000 : ℝ) ≤ Real.exp (1063 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1063 / 800 : ℝ) (521198796379 / 500000000000 : ℝ)
    (37763200359 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1063_rightExp :
    Real.exp (133 / 100 : ℝ) ≤ (37810433877 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (133 / 100 : ℝ) (1042438312211 / 1000000000000 : ℝ)
    (37810433877 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1063_denomUpper :
    Real.exp (115463119394946061 / 10000000000000000 : ℝ) ≤ (129243757175621 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (115463119394946061 / 10000000000000000 : ℝ)
    (717254225813 / 500000000000 : ℝ) (129243757175621 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1063_denomLower :
    (1018398554868693 / 10000000000 : ℝ) ≤ Real.exp (14413946017778941 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14413946017778941 / 1250000000000000 : ℝ) (1433829232623
    / 1000000000000 : ℝ) (1018398554868693 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1063_product_lower :
    (14829571017778941 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1063 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1063_leftExp
    (by norm_num : (0 : ℝ) ≤ (37763200359 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1063_product_upper :
    Real.pi * Real.exp (133 / 100 : ℝ) ≤ (118784994394946061 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1063_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1063_endpointLower :
    (95130991 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1063 / 1600 : ℝ) (133 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14829571017778941 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1063 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1063_product_lower
  have hD : Real.exp (Real.pi * Real.exp (133 / 100 : ℝ) - (1063 / 3200 : ℝ)) ≤
      (129243757175621 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1063_denomUpper
    linarith [hpThetaJensenCell1063_product_upper]
  have hi : (1 / (129243757175621 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (133 / 100 : ℝ) - (1063 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (129243757175621 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (129243757175621 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1063 / 3200 : ℝ) - Real.pi * Real.exp (133 / 100 : ℝ)) := by
    rw [show (1063 / 3200 : ℝ) - Real.pi * Real.exp (133 / 100 : ℝ) =
      -(Real.pi * Real.exp (133 / 100 : ℝ) - (1063 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1063 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1063 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1063_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (129243757175621 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1063_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1063 / 1600 : ℝ) (133 / 200 : ℝ) ≤ (97098067 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (133 / 100 : ℝ)) (118784994394946061 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (133 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1063_product_upper
  have hD : (1018398554868693 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1063 / 800 : ℝ) - (133 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1063_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1063_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1063 / 800 : ℝ) - (133 / 400 : ℝ)) ≤
      (1 / (1018398554868693 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1018398554868693 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((133 / 400 : ℝ) - Real.pi * Real.exp (1063 / 800 : ℝ)) ≤
      (2 / (1018398554868693 / 10000000000 : ℝ) : ℝ) := by
    rw [show (133 / 400 : ℝ) - Real.pi * Real.exp (1063 / 800 : ℝ) =
      -(Real.pi * Real.exp (1063 / 800 : ℝ) - (133 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (118784994394946061 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (118784994394946061 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1063_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1063 / 1600 : ℝ) (133 / 200 : ℝ)) :
    (95130991 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (97098067 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1063_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1063_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1064_leftExp :
    (302483471 / 80000000 : ℝ) ≤ Real.exp (133 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (133 / 100 : ℝ) (104243831221 / 100000000000 : ℝ)
    (302483471 / 80000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1064_rightExp :
    Real.exp (213 / 160 : ℝ) ≤ (3785772647 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (213 / 160 : ℝ) (260619758313 / 250000000000 : ℝ)
    (3785772647 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1064_denomUpper :
    Real.exp (11560856847406671 / 1000000000000000 : ℝ) ≤ (262274666569507 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11560856847406671 / 1000000000000000 : ℝ) (717580312311
    / 500000000000 : ℝ) (262274666569507 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1064_denomLower :
    (206660026575387 / 2000000000 : ℝ) ≤ Real.exp (115456831578229 / 10000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (115456831578229 / 10000000000000 : ℝ) (179310033079 /
    125000000000 : ℝ) (206660026575387 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1064_product_lower :
    (118784956578229 / 10000000000000 : ℝ) ≤ Real.pi * Real.exp (133 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1064_leftExp
    (by norm_num : (0 : ℝ) ≤ (302483471 / 80000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1064_product_upper :
    Real.pi * Real.exp (213 / 160 : ℝ) ≤ (11893356847406671 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1064_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1064_endpointLower :
    (18801803 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (133 / 200 : ℝ) (213 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (118784956578229 / 10000000000000 : ℝ) (Real.pi * Real.exp (133 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1064_product_lower
  have hD : Real.exp (Real.pi * Real.exp (213 / 160 : ℝ) - (133 / 400 : ℝ)) ≤
      (262274666569507 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1064_denomUpper
    linarith [hpThetaJensenCell1064_product_upper]
  have hi : (1 / (262274666569507 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (213 / 160 : ℝ) - (133 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (262274666569507 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (262274666569507 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((133 / 400 : ℝ) - Real.pi * Real.exp (213 / 160 : ℝ)) := by
    rw [show (133 / 400 : ℝ) - Real.pi * Real.exp (213 / 160 : ℝ) =
      -(Real.pi * Real.exp (213 / 160 : ℝ) - (133 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (133 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (133 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1064_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (262274666569507 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1064_endpointUpper :
    hpThetaJensenKernelEndpointUpper (133 / 200 : ℝ) (213 / 320 : ℝ) ≤ (11994331 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (213 / 160 : ℝ)) (11893356847406671 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (213 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1064_product_upper
  have hD : (206660026575387 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (133 / 100 : ℝ) - (213 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1064_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1064_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (133 / 100 : ℝ) - (213 / 640 : ℝ)) ≤
      (1 / (206660026575387 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (206660026575387 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((213 / 640 : ℝ) - Real.pi * Real.exp (133 / 100 : ℝ)) ≤
      (2 / (206660026575387 / 2000000000 : ℝ) : ℝ) := by
    rw [show (213 / 640 : ℝ) - Real.pi * Real.exp (133 / 100 : ℝ) =
      -(Real.pi * Real.exp (133 / 100 : ℝ) - (213 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11893356847406671 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (11893356847406671 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1064_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (133 / 200 : ℝ) (213 / 320 : ℝ)) :
    (18801803 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11994331 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1064_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1064_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1065_leftExp :
    (9464431617 / 2500000000 : ℝ) ≤ Real.exp (213 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (213 / 160 : ℝ) (1042479033251 / 1000000000000 : ℝ)
    (9464431617 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1065_rightExp :
    Real.exp (533 / 400 : ℝ) ≤ (18952539109 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (533 / 400 : ℝ) (208503951177 / 200000000000 : ℝ)
    (18952539109 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1065_denomUpper :
    Real.exp (57877101697060637 / 5000000000000000 : ℝ) ≤ (1064489002816197 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (57877101697060637 / 5000000000000000 : ℝ) (1435813927969
    / 1000000000000 : ℝ) (1064489002816197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1065_denomLower :
    (209687842922563 / 2000000000 : ℝ) ≤ Real.exp (3612571269064283 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3612571269064283 / 312500000000000 : ℝ) (1435132424601 /
    1000000000000 : ℝ) (209687842922563 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1065_product_lower :
    (3716672831564283 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (213 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1065_leftExp
    (by norm_num : (0 : ℝ) ≤ (9464431617 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1065_product_upper :
    Real.pi * Real.exp (533 / 400 : ℝ) ≤ (59541164197060637 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1065_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1065_endpointLower :
    (2322463 / 250000000 : ℝ) ≤ hpThetaTraceEndpointLower (213 / 320 : ℝ) (533 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3716672831564283 / 312500000000000 : ℝ) (Real.pi * Real.exp (213 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1065_product_lower
  have hD : Real.exp (Real.pi * Real.exp (533 / 400 : ℝ) - (213 / 640 : ℝ)) ≤
      (1064489002816197 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1065_denomUpper
    linarith [hpThetaJensenCell1065_product_upper]
  have hi : (1 / (1064489002816197 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (533 / 400 : ℝ) - (213 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1064489002816197 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1064489002816197 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((213 / 640 : ℝ) - Real.pi * Real.exp (533 / 400 : ℝ)) := by
    rw [show (213 / 640 : ℝ) - Real.pi * Real.exp (533 / 400 : ℝ) =
      -(Real.pi * Real.exp (533 / 400 : ℝ) - (213 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (213 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (213 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1065_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1064489002816197 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1065_endpointUpper :
    hpThetaJensenKernelEndpointUpper (213 / 320 : ℝ) (533 / 800 : ℝ) ≤ (94822909 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (533 / 400 : ℝ)) (59541164197060637 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (533 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1065_product_upper
  have hD : (209687842922563 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (213 / 160 : ℝ) - (533 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1065_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1065_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (213 / 160 : ℝ) - (533 / 1600 : ℝ)) ≤
      (1 / (209687842922563 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (209687842922563 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((533 / 1600 : ℝ) - Real.pi * Real.exp (213 / 160 : ℝ)) ≤
      (2 / (209687842922563 / 2000000000 : ℝ) : ℝ) := by
    rw [show (533 / 1600 : ℝ) - Real.pi * Real.exp (213 / 160 : ℝ) =
      -(Real.pi * Real.exp (213 / 160 : ℝ) - (533 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59541164197060637 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (59541164197060637 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1065_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (213 / 320 : ℝ) (533 / 800 : ℝ)) :
    (2322463 / 250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (94822909 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1065_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1065_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1066_leftExp :
    (7581015643 / 2000000000 : ℝ) ≤ Real.exp (533 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (533 / 400 : ℝ) (260629938971 / 250000000000 : ℝ)
    (7581015643 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1066_rightExp :
    Real.exp (1067 / 800 : ℝ) ≤ (37952489191 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1067 / 800 : ℝ) (260640120027 / 250000000000 : ℝ)
    (37952489191 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1066_denomUpper :
    Real.exp (115900024375021263 / 10000000000000000 : ℝ) ≤ (1080125213169887 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (115900024375021263 / 10000000000000000 : ℝ)
    (179558545491 / 125000000000 : ℝ) (1080125213169887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1066_denomLower :
    (531909935799833 / 5000000000 : ℝ) ≤ Real.exp (2893697886990457 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2893697886990457 / 250000000000000 : ℝ) (287157142977 /
    200000000000 : ℝ) (531909935799833 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1066_product_lower :
    (2977057261990457 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (533 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1066_leftExp
    (by norm_num : (0 : ℝ) ≤ (7581015643 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1066_product_upper :
    Real.pi * Real.exp (1067 / 800 : ℝ) ≤ (119231274375021263 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1066_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1066_endpointLower :
    (22949853 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (533 / 800 : ℝ) (1067 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2977057261990457 / 250000000000000 : ℝ) (Real.pi * Real.exp (533 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1066_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1067 / 800 : ℝ) - (533 / 1600 : ℝ)) ≤
      (1080125213169887 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1066_denomUpper
    linarith [hpThetaJensenCell1066_product_upper]
  have hi : (1 / (1080125213169887 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1067 / 800 : ℝ) - (533 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1080125213169887 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1080125213169887 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((533 / 1600 : ℝ) - Real.pi * Real.exp (1067 / 800 : ℝ)) := by
    rw [show (533 / 1600 : ℝ) - Real.pi * Real.exp (1067 / 800 : ℝ) =
      -(Real.pi * Real.exp (1067 / 800 : ℝ) - (533 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (533 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (533 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1066_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1080125213169887 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1066_endpointUpper :
    hpThetaJensenKernelEndpointUpper (533 / 800 : ℝ) (1067 / 1600 : ℝ) ≤ (2928211 / 312500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1067 / 800 : ℝ)) (119231274375021263 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1067 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1066_product_upper
  have hD : (531909935799833 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (533 / 400 : ℝ) - (1067 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1066_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1066_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (533 / 400 : ℝ) - (1067 / 3200 : ℝ)) ≤
      (1 / (531909935799833 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (531909935799833 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1067 / 3200 : ℝ) - Real.pi * Real.exp (533 / 400 : ℝ)) ≤
      (2 / (531909935799833 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1067 / 3200 : ℝ) - Real.pi * Real.exp (533 / 400 : ℝ) =
      -(Real.pi * Real.exp (533 / 400 : ℝ) - (1067 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (119231274375021263 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (119231274375021263 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1066_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (533 / 800 : ℝ) (1067 / 1600 : ℝ)) :
    (22949853 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2928211 / 312500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1066_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1066_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1067_leftExp :
    (9488122297 / 2500000000 : ℝ) ≤ Real.exp (1067 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1067 / 800 : ℝ) (1042560480107 / 1000000000000 : ℝ)
    (9488122297 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1067_rightExp :
    Real.exp (267 / 200 : ℝ) ≤ (18999979733 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (267 / 200 : ℝ) (1042601205923 / 1000000000000 : ℝ)
    (18999979733 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1067_denomUpper :
    Real.exp (58023015829334669 / 5000000000000000 : ℝ) ≤ (274002880410299 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58023015829334669 / 5000000000000000 : ℝ) (89820245929 /
    62500000000 : ℝ) (274002880410299 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1067_denomLower :
    (1079446248014801 / 10000000000 : ℝ) ≤ Real.exp (3621679262909603 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3621679262909603 / 312500000000000 : ℝ) (359110034443 /
    250000000000 : ℝ) (1079446248014801 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1067_product_lower :
    (3725976137909603 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1067 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1067_leftExp
    (by norm_num : (0 : ℝ) ≤ (9488122297 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1067_product_upper :
    Real.pi * Real.exp (267 / 200 : ℝ) ≤ (59690203329334669 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1067_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1067_endpointLower :
    (18142319 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1067 / 1600 : ℝ) (267 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3725976137909603 / 312500000000000 : ℝ) (Real.pi * Real.exp (1067 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1067_product_lower
  have hD : Real.exp (Real.pi * Real.exp (267 / 200 : ℝ) - (1067 / 3200 : ℝ)) ≤
      (274002880410299 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1067_denomUpper
    linarith [hpThetaJensenCell1067_product_upper]
  have hi : (1 / (274002880410299 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (267 / 200 : ℝ) - (1067 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (274002880410299 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (274002880410299 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1067 / 3200 : ℝ) - Real.pi * Real.exp (267 / 200 : ℝ)) := by
    rw [show (1067 / 3200 : ℝ) - Real.pi * Real.exp (267 / 200 : ℝ) =
      -(Real.pi * Real.exp (267 / 200 : ℝ) - (1067 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1067 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1067 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1067_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (274002880410299 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1067_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1067 / 1600 : ℝ) (267 / 400 : ℝ) ≤ (46297041 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (267 / 200 : ℝ)) (59690203329334669 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (267 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1067_product_upper
  have hD : (1079446248014801 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1067 / 800 : ℝ) - (267 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1067_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1067_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1067 / 800 : ℝ) - (267 / 800 : ℝ)) ≤
      (1 / (1079446248014801 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1079446248014801 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((267 / 800 : ℝ) - Real.pi * Real.exp (1067 / 800 : ℝ)) ≤
      (2 / (1079446248014801 / 10000000000 : ℝ) : ℝ) := by
    rw [show (267 / 800 : ℝ) - Real.pi * Real.exp (1067 / 800 : ℝ) =
      -(Real.pi * Real.exp (1067 / 800 : ℝ) - (267 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (59690203329334669 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (59690203329334669 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1067_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1067 / 1600 : ℝ) (267 / 400 : ℝ)) :
    (18142319 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (46297041 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1067_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1067_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1068_leftExp :
    (4749994933 / 1250000000 : ℝ) ≤ Real.exp (267 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (267 / 200 : ℝ) (521300602961 / 500000000000 : ℝ)
    (4749994933 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1068_rightExp :
    Real.exp (1069 / 800 : ℝ) ≤ (7609497823 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1069 / 800 : ℝ) (65165120833 / 62500000000 : ℝ)
    (7609497823 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1068_denomUpper :
    Real.exp (23238445094252039 / 2000000000000000 : ℝ) ≤ (1112152228036759 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (23238445094252039 / 2000000000000000 : ℝ) (1437780643073
    / 1000000000000 : ℝ) (1112152228036759 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1068_denomLower :
    (273830641379043 / 2500000000 : ℝ) ≤ Real.exp (1813120994569167 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1813120994569167 / 156250000000000 : ℝ) (1437095695627 /
    1000000000000 : ℝ) (273830641379043 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1068_product_lower :
    (1865318260194167 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (267 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1068_leftExp
    (by norm_num : (0 : ℝ) ≤ (4749994933 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1068_product_upper :
    Real.pi * Real.exp (1069 / 800 : ℝ) ≤ (23905945094252039 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1068_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1068_endpointLower :
    (89634973 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (267 / 400 : ℝ) (1069 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1865318260194167 / 156250000000000 : ℝ) (Real.pi * Real.exp (267 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1068_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1069 / 800 : ℝ) - (267 / 800 : ℝ)) ≤
      (1112152228036759 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1068_denomUpper
    linarith [hpThetaJensenCell1068_product_upper]
  have hi : (1 / (1112152228036759 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1069 / 800 : ℝ) - (267 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1112152228036759 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1112152228036759 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((267 / 800 : ℝ) - Real.pi * Real.exp (1069 / 800 : ℝ)) := by
    rw [show (267 / 800 : ℝ) - Real.pi * Real.exp (1069 / 800 : ℝ) =
      -(Real.pi * Real.exp (1069 / 800 : ℝ) - (267 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (267 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (267 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1068_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1112152228036759 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1068_endpointUpper :
    hpThetaJensenKernelEndpointUpper (267 / 400 : ℝ) (1069 / 1600 : ℝ) ≤ (91496801 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1069 / 800 : ℝ)) (23905945094252039 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1069 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1068_product_upper
  have hD : (273830641379043 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (267 / 200 : ℝ) - (1069 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1068_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1068_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (267 / 200 : ℝ) - (1069 / 3200 : ℝ)) ≤
      (1 / (273830641379043 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (273830641379043 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1069 / 3200 : ℝ) - Real.pi * Real.exp (267 / 200 : ℝ)) ≤
      (2 / (273830641379043 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1069 / 3200 : ℝ) - Real.pi * Real.exp (267 / 200 : ℝ) =
      -(Real.pi * Real.exp (267 / 200 : ℝ) - (1069 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23905945094252039 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (23905945094252039 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1068_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (267 / 400 : ℝ) (1069 / 1600 : ℝ)) :
    (89634973 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (91496801 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1068_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1068_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1069_leftExp :
    (38047489113 / 10000000000 : ℝ) ≤ Real.exp (1069 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1069 / 800 : ℝ) (1042641933327 / 1000000000000 : ℝ)
    (38047489113 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1069_rightExp :
    Real.exp (107 / 80 : ℝ) ≤ (38095078213 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (107 / 80 : ℝ) (260670665581 / 250000000000 : ℝ)
    (38095078213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1069_denomUpper :
    Real.exp (116338606048413309 / 10000000000000000 : ℝ) ≤ (1128551711997301 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (116338606048413309 / 10000000000000000 : ℝ) (14384384909
    / 10000000000 : ℝ) (1128551711997301 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1069_denomLower :
    (1111453120526533 / 10000000000 : ℝ) ≤ Real.exp (14523242177185987 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (14523242177185987 / 1250000000000000 : ℝ) (718876195359
    / 500000000000 : ℝ) (1111453120526533 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1069_product_lower :
    (14941210927185987 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1069 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1069_leftExp
    (by norm_num : (0 : ℝ) ≤ (38047489113 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1069_product_upper :
    Real.pi * Real.exp (107 / 80 : ℝ) ≤ (119679231048413309 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1069_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1069_endpointLower :
    (22142363 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1069 / 1600 : ℝ) (107 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14941210927185987 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1069 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1069_product_lower
  have hD : Real.exp (Real.pi * Real.exp (107 / 80 : ℝ) - (1069 / 3200 : ℝ)) ≤
      (1128551711997301 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1069_denomUpper
    linarith [hpThetaJensenCell1069_product_upper]
  have hi : (1 / (1128551711997301 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (107 / 80 : ℝ) - (1069 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1128551711997301 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1128551711997301 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1069 / 3200 : ℝ) - Real.pi * Real.exp (107 / 80 : ℝ)) := by
    rw [show (1069 / 3200 : ℝ) - Real.pi * Real.exp (107 / 80 : ℝ) =
      -(Real.pi * Real.exp (107 / 80 : ℝ) - (1069 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1069 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1069 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1069_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1128551711997301 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1069_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1069 / 1600 : ℝ) (107 / 160 : ℝ) ≤ (45205407 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (107 / 80 : ℝ)) (119679231048413309 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (107 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1069_product_upper
  have hD : (1111453120526533 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1069 / 800 : ℝ) - (107 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell1069_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1069_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1069 / 800 : ℝ) - (107 / 320 : ℝ)) ≤
      (1 / (1111453120526533 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1111453120526533 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((107 / 320 : ℝ) - Real.pi * Real.exp (1069 / 800 : ℝ)) ≤
      (2 / (1111453120526533 / 10000000000 : ℝ) : ℝ) := by
    rw [show (107 / 320 : ℝ) - Real.pi * Real.exp (1069 / 800 : ℝ) =
      -(Real.pi * Real.exp (1069 / 800 : ℝ) - (107 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (119679231048413309 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (119679231048413309 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1069_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1069 / 1600 : ℝ) (107 / 160 : ℝ)) :
    (22142363 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (45205407 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1069_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1069_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1070_leftExp :
    (38095078211 / 10000000000 : ℝ) ≤ Real.exp (107 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (107 / 80 : ℝ) (1042682662323 / 1000000000000 : ℝ)
    (38095078211 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1070_rightExp :
    Real.exp (1071 / 800 : ℝ) ≤ (7628545367 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1071 / 800 : ℝ) (1042723392911 / 1000000000000 : ℝ)
    (7628545367 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1070_denomUpper :
    Real.exp (23297034725149631 / 2000000000000000 : ℝ) ≤ (2863036083701 / 25000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23297034725149631 / 2000000000000000 : ℝ) (287819496139
    / 200000000000 : ℝ) (2863036083701 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1070_denomLower :
    (7049014314327 / 62500000 : ℝ) ≤ Real.exp (14541539743381489 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14541539743381489 / 1250000000000000 : ℝ) (287682045081
    / 200000000000 : ℝ) (7049014314327 / 62500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1070_product_lower :
    (14959899118381489 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (107 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1070_leftExp
    (by norm_num : (0 : ℝ) ≤ (38095078211 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1070_product_upper :
    Real.pi * Real.exp (1071 / 800 : ℝ) ≤ (23965784725149631 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1070_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1070_endpointLower :
    (43757469 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (107 / 160 : ℝ) (1071 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14959899118381489 / 1250000000000000 : ℝ) (Real.pi * Real.exp (107 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell1070_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1071 / 800 : ℝ) - (107 / 320 : ℝ)) ≤
      (2863036083701 / 25000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1070_denomUpper
    linarith [hpThetaJensenCell1070_product_upper]
  have hi : (1 / (2863036083701 / 25000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1071 / 800 : ℝ) - (107 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2863036083701 / 25000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2863036083701 / 25000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((107 / 320 : ℝ) - Real.pi * Real.exp (1071 / 800 : ℝ)) := by
    rw [show (107 / 320 : ℝ) - Real.pi * Real.exp (1071 / 800 : ℝ) =
      -(Real.pi * Real.exp (1071 / 800 : ℝ) - (107 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (107 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (107 / 80 : ℝ)) := by
    have h := hpThetaJensenCell1070_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2863036083701 / 25000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1070_endpointUpper :
    hpThetaJensenKernelEndpointUpper (107 / 160 : ℝ) (1071 / 1600 : ℝ) ≤ (3573441 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1071 / 800 : ℝ)) (23965784725149631 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1071 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1070_product_upper
  have hD : (7049014314327 / 62500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (107 / 80 : ℝ) - (1071 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1070_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1070_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (107 / 80 : ℝ) - (1071 / 3200 : ℝ)) ≤
      (1 / (7049014314327 / 62500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (7049014314327 / 62500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1071 / 3200 : ℝ) - Real.pi * Real.exp (107 / 80 : ℝ)) ≤
      (2 / (7049014314327 / 62500000 : ℝ) : ℝ) := by
    rw [show (1071 / 3200 : ℝ) - Real.pi * Real.exp (107 / 80 : ℝ) =
      -(Real.pi * Real.exp (107 / 80 : ℝ) - (1071 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23965784725149631 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (23965784725149631 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1070_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (107 / 160 : ℝ) (1071 / 1600 : ℝ)) :
    (43757469 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3573441 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1070_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1070_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1071_leftExp :
    (38142726833 / 10000000000 : ℝ) ≤ Real.exp (1071 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1071 / 800 : ℝ) (104272339291 / 100000000000 : ℝ)
    (38142726833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1071_rightExp :
    Real.exp (67 / 50 : ℝ) ≤ (7638087011 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (67 / 50 : ℝ) (1042764125089 / 1000000000000 : ℝ)
    (7638087011 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1071_denomUpper :
    Real.exp (23326385687148523 / 2000000000000000 : ℝ) ≤ (3631702918453 / 31250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23326385687148523 / 2000000000000000 : ℝ) (1439757614797
    / 1000000000000 : ℝ) (3631702918453 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1071_denomLower :
    (57224726595737 / 500000000 : ℝ) ≤ Real.exp (14559860684592267 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14559860684592267 / 1250000000000000 : ℝ) (359767300509
    / 250000000000 : ℝ) (57224726595737 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1071_product_lower :
    (14978610684592267 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1071 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1071_leftExp
    (by norm_num : (0 : ℝ) ≤ (38142726833 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1071_product_upper :
    Real.pi * Real.exp (67 / 50 : ℝ) ≤ (23995760687148523 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1071_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1071_endpointLower :
    (43235669 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1071 / 1600 : ℝ) (67 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14978610684592267 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1071 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1071_product_lower
  have hD : Real.exp (Real.pi * Real.exp (67 / 50 : ℝ) - (1071 / 3200 : ℝ)) ≤
      (3631702918453 / 31250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1071_denomUpper
    linarith [hpThetaJensenCell1071_product_upper]
  have hi : (1 / (3631702918453 / 31250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (67 / 50 : ℝ) - (1071 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3631702918453 / 31250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3631702918453 / 31250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1071 / 3200 : ℝ) - Real.pi * Real.exp (67 / 50 : ℝ)) := by
    rw [show (1071 / 3200 : ℝ) - Real.pi * Real.exp (67 / 50 : ℝ) =
      -(Real.pi * Real.exp (67 / 50 : ℝ) - (1071 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1071 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1071 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1071_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3631702918453 / 31250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1071_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1071 / 1600 : ℝ) (67 / 100 : ℝ) ≤ (88272339 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (67 / 50 : ℝ)) (23995760687148523 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (67 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1071_product_upper
  have hD : (57224726595737 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1071 / 800 : ℝ) - (67 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1071_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1071_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1071 / 800 : ℝ) - (67 / 200 : ℝ)) ≤
      (1 / (57224726595737 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57224726595737 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((67 / 200 : ℝ) - Real.pi * Real.exp (1071 / 800 : ℝ)) ≤
      (2 / (57224726595737 / 500000000 : ℝ) : ℝ) := by
    rw [show (67 / 200 : ℝ) - Real.pi * Real.exp (1071 / 800 : ℝ) =
      -(Real.pi * Real.exp (1071 / 800 : ℝ) - (67 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (23995760687148523 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (23995760687148523 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1071_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1071 / 1600 : ℝ) (67 / 100 : ℝ)) :
    (43235669 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (88272339 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1071_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1071_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1072_leftExp :
    (38190435053 / 10000000000 : ℝ) ≤ Real.exp (67 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (67 / 50 : ℝ) (32586378909 / 31250000000 : ℝ)
    (38190435053 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1072_rightExp :
    Real.exp (1073 / 800 : ℝ) ≤ (38238202947 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1073 / 800 : ℝ) (521402429429 / 500000000000 : ℝ)
    (38238202947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1072_denomUpper :
    Real.exp (116778870710874571 / 10000000000000000 : ℝ) ≤ (36854619940753 / 312500000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (116778870710874571 / 10000000000000000 : ℝ)
    (1440418895549 / 1000000000000 : ℝ) (36854619940753 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1072_denomLower :
    (232282876795927 / 2000000000 : ℝ) ≤ Real.exp (14578205029878047 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14578205029878047 / 1250000000000000 : ℝ) (1439729322951
    / 1000000000000 : ℝ) (232282876795927 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1072_product_lower :
    (14997345654878047 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (67 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1072_leftExp
    (by norm_num : (0 : ℝ) ≤ (38190435053 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1072_product_upper :
    Real.pi * Real.exp (1073 / 800 : ℝ) ≤ (120128870710874571 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1072_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1072_endpointLower :
    (533991 / 62500000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 100 : ℝ) (1073 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (14997345654878047 / 1250000000000000 : ℝ) (Real.pi * Real.exp (67 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell1072_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1073 / 800 : ℝ) - (67 / 200 : ℝ)) ≤
      (36854619940753 / 312500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1072_denomUpper
    linarith [hpThetaJensenCell1072_product_upper]
  have hi : (1 / (36854619940753 / 312500000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1073 / 800 : ℝ) - (67 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (36854619940753 / 312500000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (36854619940753 / 312500000 : ℝ) : ℝ) ≤
      2 * Real.exp ((67 / 200 : ℝ) - Real.pi * Real.exp (1073 / 800 : ℝ)) := by
    rw [show (67 / 200 : ℝ) - Real.pi * Real.exp (1073 / 800 : ℝ) =
      -(Real.pi * Real.exp (1073 / 800 : ℝ) - (67 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (67 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (67 / 50 : ℝ)) := by
    have h := hpThetaJensenCell1072_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (36854619940753 / 312500000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1072_endpointUpper :
    hpThetaJensenKernelEndpointUpper (67 / 100 : ℝ) (1073 / 1600 : ℝ) ≤ (87219663 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1073 / 800 : ℝ)) (120128870710874571 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1073 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1072_product_upper
  have hD : (232282876795927 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (67 / 50 : ℝ) - (1073 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1072_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1072_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (67 / 50 : ℝ) - (1073 / 3200 : ℝ)) ≤
      (1 / (232282876795927 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (232282876795927 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1073 / 3200 : ℝ) - Real.pi * Real.exp (67 / 50 : ℝ)) ≤
      (2 / (232282876795927 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1073 / 3200 : ℝ) - Real.pi * Real.exp (67 / 50 : ℝ) =
      -(Real.pi * Real.exp (67 / 50 : ℝ) - (1073 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (120128870710874571 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (120128870710874571 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1072_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (67 / 100 : ℝ) (1073 / 1600 : ℝ)) :
    (533991 / 62500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (87219663 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1072_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1072_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1073_leftExp :
    (7647640589 / 2000000000 : ℝ) ≤ Real.exp (1073 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1073 / 800 : ℝ) (1042804858857 / 1000000000000 : ℝ)
    (7647640589 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1073_rightExp :
    Real.exp (537 / 400 : ℝ) ≤ (38286030587 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (537 / 400 : ℝ) (521422797109 / 500000000000 : ℝ)
    (38286030587 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1073_denomUpper :
    Real.exp (116926000689905091 / 10000000000000000 : ℝ) ≤ (598413928397363 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (116926000689905091 / 10000000000000000 : ℝ)
    (144108132533 / 100000000000 : ℝ) (598413928397363 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1073_denomLower :
    (1178606468462229 / 10000000000 : ℝ) ≤ Real.exp (2919314561659711 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2919314561659711 / 250000000000000 : ℝ) (288078118099 /
    200000000000 : ℝ) (1178606468462229 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1073_product_lower :
    (3003220811659711 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1073 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1073_leftExp
    (by norm_num : (0 : ℝ) ≤ (7647640589 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1073_product_upper :
    Real.pi * Real.exp (537 / 400 : ℝ) ≤ (120279125689905091 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1073_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1073_endpointLower :
    (8441651 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1073 / 1600 : ℝ) (537 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3003220811659711 / 250000000000000 : ℝ) (Real.pi * Real.exp (1073 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1073_product_lower
  have hD : Real.exp (Real.pi * Real.exp (537 / 400 : ℝ) - (1073 / 3200 : ℝ)) ≤
      (598413928397363 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1073_denomUpper
    linarith [hpThetaJensenCell1073_product_upper]
  have hi : (1 / (598413928397363 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (537 / 400 : ℝ) - (1073 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (598413928397363 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (598413928397363 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1073 / 3200 : ℝ) - Real.pi * Real.exp (537 / 400 : ℝ)) := by
    rw [show (1073 / 3200 : ℝ) - Real.pi * Real.exp (537 / 400 : ℝ) =
      -(Real.pi * Real.exp (537 / 400 : ℝ) - (1073 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1073 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1073 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1073_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (598413928397363 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1073_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1073 / 1600 : ℝ) (537 / 800 : ℝ) ≤ (5386119 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (537 / 400 : ℝ)) (120279125689905091 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (537 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1073_product_upper
  have hD : (1178606468462229 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1073 / 800 : ℝ) - (537 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1073_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1073_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1073 / 800 : ℝ) - (537 / 1600 : ℝ)) ≤
      (1 / (1178606468462229 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1178606468462229 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((537 / 1600 : ℝ) - Real.pi * Real.exp (1073 / 800 : ℝ)) ≤
      (2 / (1178606468462229 / 10000000000 : ℝ) : ℝ) := by
    rw [show (537 / 1600 : ℝ) - Real.pi * Real.exp (1073 / 800 : ℝ) =
      -(Real.pi * Real.exp (1073 / 800 : ℝ) - (537 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (120279125689905091 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (120279125689905091 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1073_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1073 / 1600 : ℝ) (537 / 800 : ℝ)) :
    (8441651 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5386119 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1073_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1073_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1074_leftExp :
    (4785753823 / 1250000000 : ℝ) ≤ Real.exp (537 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (537 / 400 : ℝ) (1042845594217 / 1000000000000 : ℝ)
    (4785753823 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1074_rightExp :
    Real.exp (43 / 32 : ℝ) ≤ (38333918049 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 32 : ℝ) (104288633117 / 100000000000 : ℝ)
    (38333918049 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1074_denomUpper :
    Real.exp (117073318605312057 / 10000000000000000 : ℝ) ≤ (121458978659249 / 1000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (117073318605312057 / 10000000000000000 : ℝ)
    (360436226623 / 250000000000 : ℝ) (121458978659249 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1074_denomLower :
    (1196075492639351 / 10000000000 : ℝ) ≤ Real.exp (1826870506163277 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1826870506163277 / 156250000000000 : ℝ) (1441053007029 /
    1000000000000 : ℝ) (1196075492639351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1074_product_lower :
    (1879360740538277 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (537 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1074_leftExp
    (by norm_num : (0 : ℝ) ≤ (4785753823 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1074_product_upper :
    Real.pi * Real.exp (43 / 32 : ℝ) ≤ (120429568605312057 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1074_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1074_endpointLower :
    (41702549 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (537 / 800 : ℝ) (43 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1879360740538277 / 156250000000000 : ℝ) (Real.pi * Real.exp (537 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1074_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 32 : ℝ) - (537 / 1600 : ℝ)) ≤
      (121458978659249 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1074_denomUpper
    linarith [hpThetaJensenCell1074_product_upper]
  have hi : (1 / (121458978659249 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 32 : ℝ) - (537 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (121458978659249 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (121458978659249 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((537 / 1600 : ℝ) - Real.pi * Real.exp (43 / 32 : ℝ)) := by
    rw [show (537 / 1600 : ℝ) - Real.pi * Real.exp (43 / 32 : ℝ) =
      -(Real.pi * Real.exp (43 / 32 : ℝ) - (537 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (537 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (537 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1074_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (121458978659249 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1074_endpointUpper :
    hpThetaJensenKernelEndpointUpper (537 / 800 : ℝ) (43 / 64 : ℝ) ≤ (85146967 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 32 : ℝ)) (120429568605312057 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1074_product_upper
  have hD : (1196075492639351 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (537 / 400 : ℝ) - (43 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell1074_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1074_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (537 / 400 : ℝ) - (43 / 128 : ℝ)) ≤
      (1 / (1196075492639351 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1196075492639351 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 128 : ℝ) - Real.pi * Real.exp (537 / 400 : ℝ)) ≤
      (2 / (1196075492639351 / 10000000000 : ℝ) : ℝ) := by
    rw [show (43 / 128 : ℝ) - Real.pi * Real.exp (537 / 400 : ℝ) =
      -(Real.pi * Real.exp (537 / 400 : ℝ) - (43 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (120429568605312057 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (120429568605312057 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1074_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (537 / 800 : ℝ) (43 / 64 : ℝ)) :
    (41702549 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (85146967 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1074_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1074_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1075_leftExp :
    (38333918047 / 10000000000 : ℝ) ≤ Real.exp (43 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 32 : ℝ) (1042886331169 / 1000000000000 : ℝ)
    (38333918047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1075_rightExp :
    Real.exp (269 / 200 : ℝ) ≤ (38381865407 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (269 / 200 : ℝ) (1042927069713 / 1000000000000 : ℝ)
    (38381865407 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1075_denomUpper :
    Real.exp (117220824689573351 / 10000000000000000 : ℝ) ≤ (616319256257253 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (117220824689573351 / 10000000000000000 : ℝ) (90150602587
    / 62500000000 : ℝ) (616319256257253 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1075_denomLower :
    (303456562818873 / 2500000000 : ℝ) ≤ Real.exp (14633378783138853 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (14633378783138853 / 1250000000000000 : ℝ) (1441716574949
    / 1000000000000 : ℝ) (303456562818873 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1075_product_lower :
    (15053691283138853 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1075_leftExp
    (by norm_num : (0 : ℝ) ≤ (38333918047 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1075_product_upper :
    Real.pi * Real.exp (269 / 200 : ℝ) ≤ (120580199689573351 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1075_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1075_endpointLower :
    (10300529 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 64 : ℝ) (269 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (15053691283138853 / 1250000000000000 : ℝ) (Real.pi * Real.exp (43 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell1075_product_lower
  have hD : Real.exp (Real.pi * Real.exp (269 / 200 : ℝ) - (43 / 128 : ℝ)) ≤
      (616319256257253 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1075_denomUpper
    linarith [hpThetaJensenCell1075_product_upper]
  have hi : (1 / (616319256257253 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (269 / 200 : ℝ) - (43 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (616319256257253 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (616319256257253 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 128 : ℝ) - Real.pi * Real.exp (269 / 200 : ℝ)) := by
    rw [show (43 / 128 : ℝ) - Real.pi * Real.exp (269 / 200 : ℝ) =
      -(Real.pi * Real.exp (269 / 200 : ℝ) - (43 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 32 : ℝ)) := by
    have h := hpThetaJensenCell1075_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (616319256257253 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1075_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 64 : ℝ) (269 / 400 : ℝ) ≤ (2103169 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (269 / 200 : ℝ)) (120580199689573351 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (269 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1075_product_upper
  have hD : (303456562818873 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 32 : ℝ) - (269 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1075_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1075_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 32 : ℝ) - (269 / 800 : ℝ)) ≤
      (1 / (303456562818873 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (303456562818873 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((269 / 800 : ℝ) - Real.pi * Real.exp (43 / 32 : ℝ)) ≤
      (2 / (303456562818873 / 2500000000 : ℝ) : ℝ) := by
    rw [show (269 / 800 : ℝ) - Real.pi * Real.exp (43 / 32 : ℝ) =
      -(Real.pi * Real.exp (43 / 32 : ℝ) - (269 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (120580199689573351 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (120580199689573351 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1075_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 64 : ℝ) (269 / 400 : ℝ)) :
    (10300529 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2103169 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1075_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1075_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1076_leftExp :
    (7676373081 / 2000000000 : ℝ) ≤ Real.exp (269 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (269 / 200 : ℝ) (65182941857 / 62500000000 : ℝ)
    (7676373081 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1076_rightExp :
    Real.exp (1077 / 800 : ℝ) ≤ (38429872737 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1077 / 800 : ℝ) (1042967809847 / 1000000000000 : ℝ)
    (38429872737 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1076_denomUpper :
    Real.exp (117368519181450041 / 10000000000000000 : ℝ) ≤ (156372376316747 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (117368519181450041 / 10000000000000000 : ℝ)
    (721537766211 / 500000000000 : ℝ) (156372376316747 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1076_denomLower :
    (615931812599173 / 5000000000 : ℝ) ≤ Real.exp (2930363407535619 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2930363407535619 / 250000000000000 : ℝ) (144238129657 /
    100000000000 : ℝ) (615931812599173 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1076_product_lower :
    (3014504032535619 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (269 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1076_leftExp
    (by norm_num : (0 : ℝ) ≤ (7676373081 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1076_product_upper :
    Real.pi * Real.exp (1077 / 800 : ℝ) ≤ (120731019181450041 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1076_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1076_endpointLower :
    (40706911 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (269 / 400 : ℝ) (1077 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3014504032535619 / 250000000000000 : ℝ) (Real.pi * Real.exp (269 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1076_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1077 / 800 : ℝ) - (269 / 800 : ℝ)) ≤
      (156372376316747 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1076_denomUpper
    linarith [hpThetaJensenCell1076_product_upper]
  have hi : (1 / (156372376316747 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1077 / 800 : ℝ) - (269 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (156372376316747 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (156372376316747 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((269 / 800 : ℝ) - Real.pi * Real.exp (1077 / 800 : ℝ)) := by
    rw [show (269 / 800 : ℝ) - Real.pi * Real.exp (1077 / 800 : ℝ) =
      -(Real.pi * Real.exp (1077 / 800 : ℝ) - (269 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (269 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (269 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1076_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (156372376316747 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1076_endpointUpper :
    hpThetaJensenKernelEndpointUpper (269 / 400 : ℝ) (1077 / 1600 : ℝ) ≤ (83117193 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1077 / 800 : ℝ)) (120731019181450041 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1077 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1076_product_upper
  have hD : (615931812599173 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (269 / 200 : ℝ) - (1077 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1076_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1076_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (269 / 200 : ℝ) - (1077 / 3200 : ℝ)) ≤
      (1 / (615931812599173 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (615931812599173 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1077 / 3200 : ℝ) - Real.pi * Real.exp (269 / 200 : ℝ)) ≤
      (2 / (615931812599173 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1077 / 3200 : ℝ) - Real.pi * Real.exp (269 / 200 : ℝ) =
      -(Real.pi * Real.exp (269 / 200 : ℝ) - (1077 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (120731019181450041 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (120731019181450041 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1076_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (269 / 400 : ℝ) (1077 / 1600 : ℝ)) :
    (40706911 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (83117193 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1076_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1076_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1077_leftExp :
    (7685974547 / 2000000000 : ℝ) ≤ Real.exp (1077 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1077 / 800 : ℝ) (521483904923 / 500000000000 : ℝ)
    (7685974547 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1077_rightExp :
    Real.exp (539 / 400 : ℝ) ≤ (19238970057 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (539 / 400 : ℝ) (1043008551573 / 1000000000000 : ℝ)
    (19238970057 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1077_denomUpper :
    Real.exp (58758201158280801 / 5000000000000000 : ℝ) ≤ (12696163480753 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (58758201158280801 / 5000000000000000 : ℝ) (721871290981
    / 500000000000 : ℝ) (12696163480753 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1077_denomLower :
    (1250192587621873 / 10000000000 : ℝ) ≤ Real.exp (2934055768632353 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2934055768632353 / 250000000000000 : ℝ) (721523587149 /
    500000000000 : ℝ) (1250192587621873 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1077_product_lower :
    (3018274518632353 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1077 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1077_leftExp
    (by norm_num : (0 : ℝ) ≤ (7685974547 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1077_product_upper :
    Real.pi * Real.exp (539 / 400 : ℝ) ≤ (60441013658280801 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1077_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1077_endpointLower :
    (40216889 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1077 / 1600 : ℝ) (539 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3018274518632353 / 250000000000000 : ℝ) (Real.pi * Real.exp (1077 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1077_product_lower
  have hD : Real.exp (Real.pi * Real.exp (539 / 400 : ℝ) - (1077 / 3200 : ℝ)) ≤
      (12696163480753 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1077_denomUpper
    linarith [hpThetaJensenCell1077_product_upper]
  have hi : (1 / (12696163480753 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (539 / 400 : ℝ) - (1077 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (12696163480753 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (12696163480753 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1077 / 3200 : ℝ) - Real.pi * Real.exp (539 / 400 : ℝ)) := by
    rw [show (1077 / 3200 : ℝ) - Real.pi * Real.exp (539 / 400 : ℝ) =
      -(Real.pi * Real.exp (539 / 400 : ℝ) - (1077 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1077 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1077 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1077_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (12696163480753 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1077_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1077 / 1600 : ℝ) (539 / 800 : ℝ) ≤ (82118173 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (539 / 400 : ℝ)) (60441013658280801 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (539 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1077_product_upper
  have hD : (1250192587621873 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1077 / 800 : ℝ) - (539 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1077_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1077_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1077 / 800 : ℝ) - (539 / 1600 : ℝ)) ≤
      (1 / (1250192587621873 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1250192587621873 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((539 / 1600 : ℝ) - Real.pi * Real.exp (1077 / 800 : ℝ)) ≤
      (2 / (1250192587621873 / 10000000000 : ℝ) : ℝ) := by
    rw [show (539 / 1600 : ℝ) - Real.pi * Real.exp (1077 / 800 : ℝ) =
      -(Real.pi * Real.exp (1077 / 800 : ℝ) - (539 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (60441013658280801 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (60441013658280801 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1077_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1077 / 1600 : ℝ) (539 / 800 : ℝ)) :
    (40216889 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (82118173 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1077_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1077_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1078_leftExp :
    (2404871257 / 625000000 : ℝ) ≤ Real.exp (539 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (539 / 400 : ℝ) (260752137893 / 250000000000 : ℝ)
    (2404871257 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1078_rightExp :
    Real.exp (1079 / 800 : ℝ) ≤ (9631516903 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1079 / 800 : ℝ) (104304929489 / 100000000000 : ℝ)
    (9631516903 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1078_denomUpper :
    Real.exp (29416118581846479 / 2500000000000000 : ℝ) ≤ (644277842944651 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29416118581846479 / 2500000000000000 : ℝ) (22568918631 /
    15625000000 : ℝ) (644277842944651 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1078_denomLower :
    (158602275347733 / 1250000000 : ℝ) ≤ Real.exp (918047764315143 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (918047764315143 / 78125000000000 : ℝ) (1443714210513 /
    1000000000000 : ℝ) (158602275347733 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1078_product_lower :
    (944390537752643 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (539 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1078_leftExp
    (by norm_num : (0 : ℝ) ≤ (2404871257 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1078_product_upper :
    Real.pi * Real.exp (1079 / 800 : ℝ) ≤ (30258306081846479 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1078_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1078_endpointLower :
    (7946401 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (539 / 800 : ℝ) (1079 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (944390537752643 / 78125000000000 : ℝ) (Real.pi * Real.exp (539 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1078_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1079 / 800 : ℝ) - (539 / 1600 : ℝ)) ≤
      (644277842944651 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1078_denomUpper
    linarith [hpThetaJensenCell1078_product_upper]
  have hi : (1 / (644277842944651 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1079 / 800 : ℝ) - (539 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (644277842944651 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (644277842944651 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((539 / 1600 : ℝ) - Real.pi * Real.exp (1079 / 800 : ℝ)) := by
    rw [show (539 / 1600 : ℝ) - Real.pi * Real.exp (1079 / 800 : ℝ) =
      -(Real.pi * Real.exp (1079 / 800 : ℝ) - (539 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (539 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (539 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1078_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (644277842944651 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1078_endpointUpper :
    hpThetaJensenKernelEndpointUpper (539 / 800 : ℝ) (1079 / 1600 : ℝ) ≤ (81129609 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1079 / 800 : ℝ)) (30258306081846479 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1079 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1078_product_upper
  have hD : (158602275347733 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (539 / 400 : ℝ) - (1079 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1078_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1078_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (539 / 400 : ℝ) - (1079 / 3200 : ℝ)) ≤
      (1 / (158602275347733 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (158602275347733 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1079 / 3200 : ℝ) - Real.pi * Real.exp (539 / 400 : ℝ)) ≤
      (2 / (158602275347733 / 1250000000 : ℝ) : ℝ) := by
    rw [show (1079 / 3200 : ℝ) - Real.pi * Real.exp (539 / 400 : ℝ) =
      -(Real.pi * Real.exp (539 / 400 : ℝ) - (1079 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30258306081846479 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (30258306081846479 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1078_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (539 / 800 : ℝ) (1079 / 1600 : ℝ)) :
    (7946401 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (81129609 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1078_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1078_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1079_leftExp :
    (3852606761 / 1000000000 : ℝ) ≤ Real.exp (1079 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1079 / 800 : ℝ) (1043049294889 / 1000000000000 : ℝ)
    (3852606761 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1079_rightExp :
    Real.exp (27 / 20 : ℝ) ≤ (9643563827 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 20 : ℝ) (1043090039799 / 1000000000000 : ℝ)
    (9643563827 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1079_denomUpper :
    Real.exp (29453183863956411 / 2500000000000000 : ℝ) ≤ (653901140710803 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29453183863956411 / 2500000000000000 : ℝ) (722540083053
    / 500000000000 : ℝ) (653901140710803 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1079_denomLower :
    (643872814090919 / 5000000000 : ℝ) ≤ Real.exp (1470727322437939 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1470727322437939 / 125000000000000 : ℝ) (1444382407587 /
    1000000000000 : ℝ) (643872814090919 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1079_product_lower :
    (1512914822437939 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1079 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1079_leftExp
    (by norm_num : (0 : ℝ) ≤ (3852606761 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1079_product_upper :
    Real.pi * Real.exp (27 / 20 : ℝ) ≤ (30296152613956411 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1079_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1079_endpointLower :
    (78504431 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1079 / 1600 : ℝ) (27 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1512914822437939 / 125000000000000 : ℝ) (Real.pi * Real.exp (1079 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1079_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 20 : ℝ) - (1079 / 3200 : ℝ)) ≤
      (653901140710803 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1079_denomUpper
    linarith [hpThetaJensenCell1079_product_upper]
  have hi : (1 / (653901140710803 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 20 : ℝ) - (1079 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (653901140710803 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (653901140710803 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1079 / 3200 : ℝ) - Real.pi * Real.exp (27 / 20 : ℝ)) := by
    rw [show (1079 / 3200 : ℝ) - Real.pi * Real.exp (27 / 20 : ℝ) =
      -(Real.pi * Real.exp (27 / 20 : ℝ) - (1079 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1079 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1079 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1079_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (653901140710803 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1079_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1079 / 1600 : ℝ) (27 / 40 : ℝ) ≤ (20037853 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 20 : ℝ)) (30296152613956411 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1079_product_upper
  have hD : (643872814090919 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1079 / 800 : ℝ) - (27 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell1079_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1079_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1079 / 800 : ℝ) - (27 / 80 : ℝ)) ≤
      (1 / (643872814090919 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (643872814090919 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 80 : ℝ) - Real.pi * Real.exp (1079 / 800 : ℝ)) ≤
      (2 / (643872814090919 / 5000000000 : ℝ) : ℝ) := by
    rw [show (27 / 80 : ℝ) - Real.pi * Real.exp (1079 / 800 : ℝ) =
      -(Real.pi * Real.exp (1079 / 800 : ℝ) - (27 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (30296152613956411 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (30296152613956411 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1079_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1079 / 1600 : ℝ) (27 / 40 : ℝ)) :
    (78504431 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (20037853 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1079_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1079_endpointUpper

def hpThetaJensenCellsBatch053Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (98566783 / 10000000000 : ℝ)
  | 1 => (48704889 / 5000000000 : ℝ)
  | 2 => (48132273 / 5000000000 : ℝ)
  | 3 => (95130991 / 10000000000 : ℝ)
  | 4 => (18801803 / 2000000000 : ℝ)
  | 5 => (2322463 / 250000000 : ℝ)
  | 6 => (22949853 / 2500000000 : ℝ)
  | 7 => (18142319 / 2000000000 : ℝ)
  | 8 => (89634973 / 10000000000 : ℝ)
  | 9 => (22142363 / 2500000000 : ℝ)
  | 10 => (43757469 / 5000000000 : ℝ)
  | 11 => (43235669 / 5000000000 : ℝ)
  | 12 => (533991 / 62500000 : ℝ)
  | 13 => (8441651 / 1000000000 : ℝ)
  | 14 => (41702549 / 5000000000 : ℝ)
  | 15 => (10300529 / 1250000000 : ℝ)
  | 16 => (40706911 / 5000000000 : ℝ)
  | 17 => (40216889 / 5000000000 : ℝ)
  | 18 => (7946401 / 1000000000 : ℝ)
  | 19 => (78504431 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch053Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (100599393 / 10000000000 : ℝ)
  | 1 => (99420341 / 10000000000 : ℝ)
  | 2 => (19650653 / 2000000000 : ℝ)
  | 3 => (97098067 / 10000000000 : ℝ)
  | 4 => (11994331 / 1250000000 : ℝ)
  | 5 => (94822909 / 10000000000 : ℝ)
  | 6 => (2928211 / 312500000 : ℝ)
  | 7 => (46297041 / 5000000000 : ℝ)
  | 8 => (91496801 / 10000000000 : ℝ)
  | 9 => (45205407 / 5000000000 : ℝ)
  | 10 => (3573441 / 400000000 : ℝ)
  | 11 => (88272339 / 10000000000 : ℝ)
  | 12 => (87219663 / 10000000000 : ℝ)
  | 13 => (5386119 / 625000000 : ℝ)
  | 14 => (85146967 / 10000000000 : ℝ)
  | 15 => (2103169 / 250000000 : ℝ)
  | 16 => (83117193 / 10000000000 : ℝ)
  | 17 => (82118173 / 10000000000 : ℝ)
  | 18 => (81129609 / 10000000000 : ℝ)
  | 19 => (20037853 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch053_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch053Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch053Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1060_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1061_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1062_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1063_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1064_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1065_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1066_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1067_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1068_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1069_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1070_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1071_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1072_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1073_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1074_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1075_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1076_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1077_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1078_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1079_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper] at h ⊢
    exact h

end HodgeProofHP
