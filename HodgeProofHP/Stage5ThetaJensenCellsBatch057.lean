import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1140_leftExp :
    (20789289213 / 5000000000 : ℝ) ≤ Real.exp (57 / 40 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 40 : ℝ) (1045537649251 / 1000000000000 : ℝ)
    (20789289213 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1140_rightExp :
    Real.exp (1141 / 800 : ℝ) ≤ (10407646037 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1141 / 800 : ℝ) (261394622841 / 250000000000 : ℝ)
    (10407646037 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1140_denomUpper :
    Real.exp (31805962936316941 / 2500000000000000 : ℝ) ≤ (418959160781757 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (31805962936316941 / 2500000000000000 : ℝ) (297642143231
    / 200000000000 : ℝ) (418959160781757 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1140_denomLower :
    (329631431633321 / 1000000000 : ℝ) ≤ Real.exp (7941081522155887 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7941081522155887 / 625000000000000 : ℝ) (297487272529 /
    200000000000 : ℝ) (329631431633321 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1140_product_lower :
    (8163933084655887 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 40 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1140_leftExp
    (by norm_num : (0 : ℝ) ≤ (20789289213 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1140_product_upper :
    Real.pi * Real.exp (1141 / 800 : ℝ) ≤ (32696587936316941 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1140_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1140_endpointLower :
    (36048873 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 80 : ℝ) (1141 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8163933084655887 / 625000000000000 : ℝ) (Real.pi * Real.exp (57 / 40 : ℝ))
    (by norm_num) hpThetaJensenCell1140_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1141 / 800 : ℝ) - (57 / 160 : ℝ)) ≤
      (418959160781757 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1140_denomUpper
    linarith [hpThetaJensenCell1140_product_upper]
  have hi : (1 / (418959160781757 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1141 / 800 : ℝ) - (57 / 160 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (418959160781757 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (418959160781757 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 160 : ℝ) - Real.pi * Real.exp (1141 / 800 : ℝ)) := by
    rw [show (57 / 160 : ℝ) - Real.pi * Real.exp (1141 / 800 : ℝ) =
      -(Real.pi * Real.exp (1141 / 800 : ℝ) - (57 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 40 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 40 : ℝ)) := by
    have h := hpThetaJensenCell1140_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (418959160781757 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1140_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 80 : ℝ) (1141 / 1600 : ℝ) ≤ (9212201 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1141 / 800 : ℝ)) (32696587936316941 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1141 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1140_product_upper
  have hD : (329631431633321 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 40 : ℝ) - (1141 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1140_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1140_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 40 : ℝ) - (1141 / 3200 : ℝ)) ≤
      (1 / (329631431633321 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (329631431633321 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1141 / 3200 : ℝ) - Real.pi * Real.exp (57 / 40 : ℝ)) ≤
      (2 / (329631431633321 / 1000000000 : ℝ) : ℝ) := by
    rw [show (1141 / 3200 : ℝ) - Real.pi * Real.exp (57 / 40 : ℝ) =
      -(Real.pi * Real.exp (57 / 40 : ℝ) - (1141 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (32696587936316941 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (32696587936316941 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1140_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 80 : ℝ) (1141 / 1600 : ℝ)) :
    (36048873 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (9212201 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1140_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1140_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1141_leftExp :
    (20815292073 / 5000000000 : ℝ) ≤ Real.exp (1141 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1141 / 800 : ℝ) (1045578491363 / 1000000000000 : ℝ)
    (20815292073 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1141_rightExp :
    Real.exp (571 / 400 : ℝ) ≤ (41682654917 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (571 / 400 : ℝ) (32675604221 / 31250000000 : ℝ)
    (41682654917 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1141_denomUpper :
    Real.exp (127384311908662781 / 10000000000000000 : ℝ) ≤ (3405888093164341 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (127384311908662781 / 10000000000000000 : ℝ)
    (297791429741 / 200000000000 : ℝ) (3405888093164341 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1141_denomLower :
    (3349565198278519 / 10000000000 : ℝ) ≤ Real.exp (7951097506775027 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7951097506775027 / 625000000000000 : ℝ) (1488181456187 /
    1000000000000 : ℝ) (3349565198278519 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1141_product_lower :
    (8174144381775027 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (1141 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1141_leftExp
    (by norm_num : (0 : ℝ) ≤ (20815292073 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1141_product_upper :
    Real.pi * Real.exp (571 / 400 : ℝ) ≤ (130949936908662781 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1141_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1141_endpointLower :
    (3556961 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1141 / 1600 : ℝ) (571 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8174144381775027 / 625000000000000 : ℝ) (Real.pi * Real.exp (1141 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1141_product_lower
  have hD : Real.exp (Real.pi * Real.exp (571 / 400 : ℝ) - (1141 / 3200 : ℝ)) ≤
      (3405888093164341 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1141_denomUpper
    linarith [hpThetaJensenCell1141_product_upper]
  have hi : (1 / (3405888093164341 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (571 / 400 : ℝ) - (1141 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3405888093164341 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3405888093164341 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1141 / 3200 : ℝ) - Real.pi * Real.exp (571 / 400 : ℝ)) := by
    rw [show (1141 / 3200 : ℝ) - Real.pi * Real.exp (571 / 400 : ℝ) =
      -(Real.pi * Real.exp (571 / 400 : ℝ) - (1141 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1141 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1141 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1141_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3405888093164341 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1141_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1141 / 1600 : ℝ) (571 / 800 : ℝ) ≤ (36359641 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (571 / 400 : ℝ)) (130949936908662781 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (571 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1141_product_upper
  have hD : (3349565198278519 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1141 / 800 : ℝ) - (571 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1141_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1141_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1141 / 800 : ℝ) - (571 / 1600 : ℝ)) ≤
      (1 / (3349565198278519 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3349565198278519 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((571 / 1600 : ℝ) - Real.pi * Real.exp (1141 / 800 : ℝ)) ≤
      (2 / (3349565198278519 / 10000000000 : ℝ) : ℝ) := by
    rw [show (571 / 1600 : ℝ) - Real.pi * Real.exp (1141 / 800 : ℝ) =
      -(Real.pi * Real.exp (1141 / 800 : ℝ) - (571 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (130949936908662781 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (130949936908662781 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1141_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1141 / 1600 : ℝ) (571 / 800 : ℝ)) :
    (3556961 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (36359641 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1141_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1141_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1142_leftExp :
    (20841327457 / 5000000000 : ℝ) ≤ Real.exp (571 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (571 / 400 : ℝ) (1045619335071 / 1000000000000 : ℝ)
    (20841327457 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1142_rightExp :
    Real.exp (1143 / 800 : ℝ) ≤ (41734790813 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1143 / 800 : ℝ) (8365281443 / 8000000000 : ℝ)
    (41734790813 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1142_denomUpper :
    Real.exp (127544976674585109 / 10000000000000000 : ℝ) ≤ (692210132389103 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (127544976674585109 / 10000000000000000 : ℝ)
    (148970490813 / 100000000000 : ℝ) (692210132389103 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1142_denomLower :
    (3403745887181401 / 10000000000 : ℝ) ≤ Real.exp (7961126263536443 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7961126263536443 / 625000000000000 : ℝ) (297785574761 /
    200000000000 : ℝ) (3403745887181401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1142_product_lower :
    (8184368451036443 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (571 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1142_leftExp
    (by norm_num : (0 : ℝ) ≤ (20841327457 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1142_product_upper :
    Real.pi * Real.exp (1143 / 800 : ℝ) ≤ (131113726674585109 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1142_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1142_endpointLower :
    (35095993 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (571 / 800 : ℝ) (1143 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8184368451036443 / 625000000000000 : ℝ) (Real.pi * Real.exp (571 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1142_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1143 / 800 : ℝ) - (571 / 1600 : ℝ)) ≤
      (692210132389103 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1142_denomUpper
    linarith [hpThetaJensenCell1142_product_upper]
  have hi : (1 / (692210132389103 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1143 / 800 : ℝ) - (571 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (692210132389103 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (692210132389103 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((571 / 1600 : ℝ) - Real.pi * Real.exp (1143 / 800 : ℝ)) := by
    rw [show (571 / 1600 : ℝ) - Real.pi * Real.exp (1143 / 800 : ℝ) =
      -(Real.pi * Real.exp (1143 / 800 : ℝ) - (571 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (571 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (571 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1142_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (692210132389103 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1142_endpointUpper :
    hpThetaJensenKernelEndpointUpper (571 / 800 : ℝ) (1143 / 1600 : ℝ) ≤ (35876231 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1143 / 800 : ℝ)) (131113726674585109 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1143 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1142_product_upper
  have hD : (3403745887181401 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (571 / 400 : ℝ) - (1143 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1142_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1142_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (571 / 400 : ℝ) - (1143 / 3200 : ℝ)) ≤
      (1 / (3403745887181401 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3403745887181401 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1143 / 3200 : ℝ) - Real.pi * Real.exp (571 / 400 : ℝ)) ≤
      (2 / (3403745887181401 / 10000000000 : ℝ) : ℝ) := by
    rw [show (1143 / 3200 : ℝ) - Real.pi * Real.exp (571 / 400 : ℝ) =
      -(Real.pi * Real.exp (571 / 400 : ℝ) - (1143 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (131113726674585109 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (131113726674585109 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1142_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (571 / 800 : ℝ) (1143 / 1600 : ℝ)) :
    (35095993 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (35876231 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1142_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1142_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1143_leftExp :
    (41734790811 / 10000000000 : ℝ) ≤ Real.exp (1143 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1143 / 800 : ℝ) (522830090187 / 500000000000 : ℝ)
    (41734790811 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1143_rightExp :
    Real.exp (143 / 100 : ℝ) ≤ (522337399 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (143 / 100 : ℝ) (1045701027273 / 1000000000000 : ℝ)
    (522337399 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1143_denomUpper :
    Real.exp (1596323078836607 / 125000000000000 : ℝ) ≤ (1758589355588321 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1596323078836607 / 125000000000000 : ℝ) (745226998641 /
    500000000000 : ℝ) (1758589355588321 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1143_denomLower :
    (138354949733767 / 400000000 : ℝ) ≤ Real.exp (15942335616688889 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15942335616688889 / 1250000000000000 : ℝ) (14896756183 /
    10000000000 : ℝ) (138354949733767 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1143_product_lower :
    (16389210616688889 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1143 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1143_leftExp
    (by norm_num : (0 : ℝ) ≤ (41734790811 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1143_product_upper :
    Real.pi * Real.exp (143 / 100 : ℝ) ≤ (1640971516336607 / 125000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1143_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1143_endpointLower :
    (6925593 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1143 / 1600 : ℝ) (143 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16389210616688889 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1143 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1143_product_lower
  have hD : Real.exp (Real.pi * Real.exp (143 / 100 : ℝ) - (1143 / 3200 : ℝ)) ≤
      (1758589355588321 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1143_denomUpper
    linarith [hpThetaJensenCell1143_product_upper]
  have hi : (1 / (1758589355588321 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (143 / 100 : ℝ) - (1143 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1758589355588321 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1758589355588321 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1143 / 3200 : ℝ) - Real.pi * Real.exp (143 / 100 : ℝ)) := by
    rw [show (1143 / 3200 : ℝ) - Real.pi * Real.exp (143 / 100 : ℝ) =
      -(Real.pi * Real.exp (143 / 100 : ℝ) - (1143 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1143 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1143 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1143_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1758589355588321 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1143_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1143 / 1600 : ℝ) (143 / 200 : ℝ) ≤ (7079703 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (143 / 100 : ℝ)) (1640971516336607 / 125000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (143 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1143_product_upper
  have hD : (138354949733767 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1143 / 800 : ℝ) - (143 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell1143_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1143_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1143 / 800 : ℝ) - (143 / 400 : ℝ)) ≤
      (1 / (138354949733767 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (138354949733767 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((143 / 400 : ℝ) - Real.pi * Real.exp (1143 / 800 : ℝ)) ≤
      (2 / (138354949733767 / 400000000 : ℝ) : ℝ) := by
    rw [show (143 / 400 : ℝ) - Real.pi * Real.exp (1143 / 800 : ℝ) =
      -(Real.pi * Real.exp (1143 / 800 : ℝ) - (143 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1640971516336607 / 125000000000000 : ℝ) ^ 2 - 6 *
      (1640971516336607 / 125000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1143_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1143 / 1600 : ℝ) (143 / 200 : ℝ)) :
    (6925593 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7079703 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1143_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1143_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1144_leftExp :
    (20893495959 / 5000000000 : ℝ) ≤ Real.exp (143 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (143 / 100 : ℝ) (130712628409 / 125000000000 : ℝ)
    (20893495959 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1144_rightExp :
    Real.exp (229 / 160 : ℝ) ≤ (41839258319 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (229 / 160 : ℝ) (1045741875767 / 1000000000000 : ℝ)
    (41839258319 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1144_denomUpper :
    Real.exp (127866921060162167 / 10000000000000000 : ℝ) ≤ (142971612299781 / 400000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (127866921060162167 / 10000000000000000 : ℝ) (59648176759
    / 40000000000 : ℝ) (142971612299781 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1144_denomLower :
    (140598658838741 / 400000000 : ℝ) ≤ Real.exp (7981222157103341 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7981222157103341 / 625000000000000 : ℝ) (1164394291 /
    781250000 : ℝ) (140598658838741 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1144_product_lower :
    (8204854969603341 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (143 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1144_leftExp
    (by norm_num : (0 : ℝ) ≤ (20893495959 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1144_product_upper :
    Real.pi * Real.exp (229 / 160 : ℝ) ≤ (131441921060162167 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1144_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1144_endpointLower :
    (3416547 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (143 / 200 : ℝ) (229 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8204854969603341 / 625000000000000 : ℝ) (Real.pi * Real.exp (143 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell1144_product_lower
  have hD : Real.exp (Real.pi * Real.exp (229 / 160 : ℝ) - (143 / 400 : ℝ)) ≤
      (142971612299781 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1144_denomUpper
    linarith [hpThetaJensenCell1144_product_upper]
  have hi : (1 / (142971612299781 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (229 / 160 : ℝ) - (143 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (142971612299781 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (142971612299781 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((143 / 400 : ℝ) - Real.pi * Real.exp (229 / 160 : ℝ)) := by
    rw [show (143 / 400 : ℝ) - Real.pi * Real.exp (229 / 160 : ℝ) =
      -(Real.pi * Real.exp (229 / 160 : ℝ) - (143 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (143 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (143 / 100 : ℝ)) := by
    have h := hpThetaJensenCell1144_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (142971612299781 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1144_endpointUpper :
    hpThetaJensenKernelEndpointUpper (143 / 200 : ℝ) (229 / 320 : ℝ) ≤ (34926437 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (229 / 160 : ℝ)) (131441921060162167 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (229 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1144_product_upper
  have hD : (140598658838741 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (143 / 100 : ℝ) - (229 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1144_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1144_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (143 / 100 : ℝ) - (229 / 640 : ℝ)) ≤
      (1 / (140598658838741 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (140598658838741 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((229 / 640 : ℝ) - Real.pi * Real.exp (143 / 100 : ℝ)) ≤
      (2 / (140598658838741 / 400000000 : ℝ) : ℝ) := by
    rw [show (229 / 640 : ℝ) - Real.pi * Real.exp (143 / 100 : ℝ) =
      -(Real.pi * Real.exp (143 / 100 : ℝ) - (229 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (131441921060162167 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (131441921060162167 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1144_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (143 / 200 : ℝ) (229 / 320 : ℝ)) :
    (3416547 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (34926437 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1144_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1144_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1145_leftExp :
    (41839258317 / 10000000000 : ℝ) ≤ Real.exp (229 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (229 / 160 : ℝ) (522870937883 / 500000000000 : ℝ)
    (41839258317 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1145_rightExp :
    Real.exp (573 / 400 : ℝ) ≤ (41891590093 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (573 / 400 : ℝ) (1045782725857 / 1000000000000 : ℝ)
    (41891590093 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1145_denomUpper :
    Real.exp (128028201195038149 / 10000000000000000 : ℝ) ≤ (3632403878363353 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (128028201195038149 / 10000000000000000 : ℝ)
    (745978088029 / 500000000000 : ℝ) (3632403878363353 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1145_denomLower :
    (1786021063244267 / 5000000000 : ℝ) ≤ Real.exp (15982578651827583 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (15982578651827583 / 1250000000000000 : ℝ) (59647003967 /
    40000000000 : ℝ) (1786021063244267 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1145_product_lower :
    (16430234901827583 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (229 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1145_leftExp
    (by norm_num : (0 : ℝ) ≤ (41839258317 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1145_product_upper :
    Real.pi * Real.exp (573 / 400 : ℝ) ≤ (131606326195038149 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1145_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1145_endpointLower :
    (8427113 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (229 / 320 : ℝ) (573 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16430234901827583 / 1250000000000000 : ℝ) (Real.pi * Real.exp (229 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1145_product_lower
  have hD : Real.exp (Real.pi * Real.exp (573 / 400 : ℝ) - (229 / 640 : ℝ)) ≤
      (3632403878363353 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1145_denomUpper
    linarith [hpThetaJensenCell1145_product_upper]
  have hi : (1 / (3632403878363353 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (573 / 400 : ℝ) - (229 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3632403878363353 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3632403878363353 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((229 / 640 : ℝ) - Real.pi * Real.exp (573 / 400 : ℝ)) := by
    rw [show (229 / 640 : ℝ) - Real.pi * Real.exp (573 / 400 : ℝ) =
      -(Real.pi * Real.exp (573 / 400 : ℝ) - (229 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (229 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (229 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1145_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3632403878363353 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1145_endpointUpper :
    hpThetaJensenKernelEndpointUpper (229 / 320 : ℝ) (573 / 800 : ℝ) ≤ (1722997 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (573 / 400 : ℝ)) (131606326195038149 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (573 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1145_product_upper
  have hD : (1786021063244267 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (229 / 160 : ℝ) - (573 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1145_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1145_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (229 / 160 : ℝ) - (573 / 1600 : ℝ)) ≤
      (1 / (1786021063244267 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1786021063244267 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((573 / 1600 : ℝ) - Real.pi * Real.exp (229 / 160 : ℝ)) ≤
      (2 / (1786021063244267 / 5000000000 : ℝ) : ℝ) := by
    rw [show (573 / 1600 : ℝ) - Real.pi * Real.exp (229 / 160 : ℝ) =
      -(Real.pi * Real.exp (229 / 160 : ℝ) - (573 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (131606326195038149 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (131606326195038149 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1145_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (229 / 320 : ℝ) (573 / 800 : ℝ)) :
    (8427113 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1722997 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1145_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1145_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1146_leftExp :
    (41891590091 / 10000000000 : ℝ) ≤ Real.exp (573 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (573 / 400 : ℝ) (32680710183 / 31250000000 : ℝ)
    (41891590091 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1146_rightExp :
    Real.exp (1147 / 800 : ℝ) ≤ (41943987323 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1147 / 800 : ℝ) (1045823577543 / 1000000000000 : ℝ)
    (41943987323 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1146_denomUpper :
    Real.exp (128189686966025539 / 10000000000000000 : ℝ) ≤ (738307643016753 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (128189686966025539 / 10000000000000000 : ℝ)
    (373177317839 / 250000000000 : ℝ) (738307643016753 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1146_denomLower :
    (726023825138079 / 2000000000 : ℝ) ≤ Real.exp (16002738662145609 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16002738662145609 / 1250000000000000 : ℝ) (1491926841233
    / 1000000000000 : ℝ) (726023825138079 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1146_product_lower :
    (16450785537145609 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (573 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1146_leftExp
    (by norm_num : (0 : ℝ) ≤ (41891590091 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1146_product_upper :
    Real.pi * Real.exp (1147 / 800 : ℝ) ≤ (131770936966025539 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1146_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1146_endpointLower :
    (4157107 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (573 / 800 : ℝ) (1147 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16450785537145609 / 1250000000000000 : ℝ) (Real.pi * Real.exp (573 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1146_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1147 / 800 : ℝ) - (573 / 1600 : ℝ)) ≤
      (738307643016753 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1146_denomUpper
    linarith [hpThetaJensenCell1146_product_upper]
  have hi : (1 / (738307643016753 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1147 / 800 : ℝ) - (573 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (738307643016753 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (738307643016753 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((573 / 1600 : ℝ) - Real.pi * Real.exp (1147 / 800 : ℝ)) := by
    rw [show (573 / 1600 : ℝ) - Real.pi * Real.exp (1147 / 800 : ℝ) =
      -(Real.pi * Real.exp (1147 / 800 : ℝ) - (573 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (573 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (573 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1146_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (738307643016753 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1146_endpointUpper :
    hpThetaJensenKernelEndpointUpper (573 / 800 : ℝ) (1147 / 1600 : ℝ) ≤ (4249871 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1147 / 800 : ℝ)) (131770936966025539 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1147 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1146_product_upper
  have hD : (726023825138079 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (573 / 400 : ℝ) - (1147 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1146_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1146_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (573 / 400 : ℝ) - (1147 / 3200 : ℝ)) ≤
      (1 / (726023825138079 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (726023825138079 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1147 / 3200 : ℝ) - Real.pi * Real.exp (573 / 400 : ℝ)) ≤
      (2 / (726023825138079 / 2000000000 : ℝ) : ℝ) := by
    rw [show (1147 / 3200 : ℝ) - Real.pi * Real.exp (573 / 400 : ℝ) =
      -(Real.pi * Real.exp (573 / 400 : ℝ) - (1147 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (131770936966025539 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (131770936966025539 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1146_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (573 / 800 : ℝ) (1147 / 1600 : ℝ)) :
    (4157107 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4249871 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1146_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1146_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1147_leftExp :
    (1048599683 / 250000000 : ℝ) ≤ Real.exp (1147 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1147 / 800 : ℝ) (522911788771 / 500000000000 : ℝ)
    (1048599683 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1147_rightExp :
    Real.exp (287 / 200 : ℝ) ≤ (41996450089 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (287 / 200 : ℝ) (130733053853 / 125000000000 : ℝ)
    (41996450089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1147_denomUpper :
    Real.exp (128351378624451777 / 10000000000000000 : ℝ) ≤ (750342496312449 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (128351378624451777 / 10000000000000000 : ℝ)
    (746731853843 / 500000000000 : ℝ) (750342496312449 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1147_denomLower :
    (1844608123467367 / 5000000000 : ℝ) ≤ Real.exp (400573109414417 / 31250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (400573109414417 / 31250000000000 : ℝ) (298535984293 /
    200000000000 : ℝ) (1844608123467367 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1147_product_lower :
    (411784046914417 / 31250000000000 : ℝ) ≤ Real.pi * Real.exp (1147 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1147_leftExp
    (by norm_num : (0 : ℝ) ≤ (1048599683 / 250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1147_product_upper :
    Real.pi * Real.exp (287 / 200 : ℝ) ≤ (131935753624451777 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1147_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1147_endpointLower :
    (8202657 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1147 / 1600 : ℝ) (287 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (411784046914417 / 31250000000000 : ℝ) (Real.pi * Real.exp (1147 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1147_product_lower
  have hD : Real.exp (Real.pi * Real.exp (287 / 200 : ℝ) - (1147 / 3200 : ℝ)) ≤
      (750342496312449 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1147_denomUpper
    linarith [hpThetaJensenCell1147_product_upper]
  have hi : (1 / (750342496312449 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (287 / 200 : ℝ) - (1147 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (750342496312449 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (750342496312449 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1147 / 3200 : ℝ) - Real.pi * Real.exp (287 / 200 : ℝ)) := by
    rw [show (1147 / 3200 : ℝ) - Real.pi * Real.exp (287 / 200 : ℝ) =
      -(Real.pi * Real.exp (287 / 200 : ℝ) - (1147 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1147 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1147 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1147_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (750342496312449 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1147_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1147 / 1600 : ℝ) (287 / 400 : ℝ) ≤ (6708693 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (287 / 200 : ℝ)) (131935753624451777 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (287 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1147_product_upper
  have hD : (1844608123467367 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1147 / 800 : ℝ) - (287 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1147_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1147_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1147 / 800 : ℝ) - (287 / 800 : ℝ)) ≤
      (1 / (1844608123467367 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1844608123467367 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((287 / 800 : ℝ) - Real.pi * Real.exp (1147 / 800 : ℝ)) ≤
      (2 / (1844608123467367 / 5000000000 : ℝ) : ℝ) := by
    rw [show (287 / 800 : ℝ) - Real.pi * Real.exp (1147 / 800 : ℝ) =
      -(Real.pi * Real.exp (1147 / 800 : ℝ) - (287 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (131935753624451777 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (131935753624451777 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1147_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1147 / 1600 : ℝ) (287 / 400 : ℝ)) :
    (8202657 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6708693 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1147_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1147_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1148_leftExp :
    (20998225043 / 5000000000 : ℝ) ≤ Real.exp (287 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (287 / 200 : ℝ) (1045864430823 / 1000000000000 : ℝ)
    (20998225043 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1148_rightExp :
    Real.exp (1149 / 800 : ℝ) ≤ (10512244619 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1149 / 800 : ℝ) (522952642851 / 500000000000 : ℝ)
    (10512244619 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1148_denomUpper :
    Real.exp (32128319109338067 / 2500000000000000 : ℝ) ≤ (3812946229077393 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (32128319109338067 / 2500000000000000 : ℝ) (1494219487943
    / 1000000000000 : ℝ) (3812946229077393 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1148_denomLower :
    (1874676322128869 / 5000000000 : ℝ) ≤ Real.exp (8021567913661057 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (8021567913661057 / 625000000000000 : ℝ) (373358585679 /
    250000000000 : ℝ) (1874676322128869 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1148_product_lower :
    (8245981976161057 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (287 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1148_leftExp
    (by norm_num : (0 : ℝ) ≤ (20998225043 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1148_product_upper :
    Real.pi * Real.exp (1149 / 800 : ℝ) ≤ (33025194109338067 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1148_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1148_endpointLower :
    (32369711 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (287 / 400 : ℝ) (1149 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (8245981976161057 / 625000000000000 : ℝ) (Real.pi * Real.exp (287 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1148_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1149 / 800 : ℝ) - (287 / 800 : ℝ)) ≤
      (3812946229077393 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1148_denomUpper
    linarith [hpThetaJensenCell1148_product_upper]
  have hi : (1 / (3812946229077393 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1149 / 800 : ℝ) - (287 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3812946229077393 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3812946229077393 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((287 / 800 : ℝ) - Real.pi * Real.exp (1149 / 800 : ℝ)) := by
    rw [show (287 / 800 : ℝ) - Real.pi * Real.exp (1149 / 800 : ℝ) =
      -(Real.pi * Real.exp (1149 / 800 : ℝ) - (287 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (287 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (287 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1148_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3812946229077393 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1148_endpointUpper :
    hpThetaJensenKernelEndpointUpper (287 / 400 : ℝ) (1149 / 1600 : ℝ) ≤ (129271 / 39062500 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1149 / 800 : ℝ)) (33025194109338067 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1149 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1148_product_upper
  have hD : (1874676322128869 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (287 / 200 : ℝ) - (1149 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1148_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1148_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (287 / 200 : ℝ) - (1149 / 3200 : ℝ)) ≤
      (1 / (1874676322128869 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1874676322128869 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1149 / 3200 : ℝ) - Real.pi * Real.exp (287 / 200 : ℝ)) ≤
      (2 / (1874676322128869 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1149 / 3200 : ℝ) - Real.pi * Real.exp (287 / 200 : ℝ) =
      -(Real.pi * Real.exp (287 / 200 : ℝ) - (1149 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (33025194109338067 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (33025194109338067 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1148_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (287 / 400 : ℝ) (1149 / 1600 : ℝ)) :
    (32369711 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (129271 / 39062500 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1148_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1148_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1149_leftExp :
    (42048978473 / 10000000000 : ℝ) ≤ Real.exp (1149 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1149 / 800 : ℝ) (1045905285701 / 1000000000000 : ℝ)
    (42048978473 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1149_rightExp :
    Real.exp (23 / 16 : ℝ) ≤ (42101572563 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 16 : ℝ) (41837845687 / 40000000000 : ℝ)
    (42101572563 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1149_denomUpper :
    Real.exp (128675380652912859 / 10000000000000000 : ℝ) ≤ (1937629695778943 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (128675380652912859 / 10000000000000000 : ℝ)
    (1494976614941 / 1000000000000 : ℝ) (1937629695778943 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1149_denomLower :
    (952636963884229 / 2500000000 : ℝ) ≤ Real.exp (16063373047368627 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16063373047368627 / 1250000000000000 : ℝ) (1494190107867
    / 1000000000000 : ℝ) (952636963884229 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1149_product_lower :
    (16512591797368627 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1149 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1149_leftExp
    (by norm_num : (0 : ℝ) ≤ (42048978473 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1149_product_upper :
    Real.pi * Real.exp (23 / 16 : ℝ) ≤ (132266005652912859 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1149_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1149_endpointLower :
    (15967027 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1149 / 1600 : ℝ) (23 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16512591797368627 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1149 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1149_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 16 : ℝ) - (1149 / 3200 : ℝ)) ≤
      (1937629695778943 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1149_denomUpper
    linarith [hpThetaJensenCell1149_product_upper]
  have hi : (1 / (1937629695778943 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 16 : ℝ) - (1149 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1937629695778943 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1937629695778943 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1149 / 3200 : ℝ) - Real.pi * Real.exp (23 / 16 : ℝ)) := by
    rw [show (1149 / 3200 : ℝ) - Real.pi * Real.exp (23 / 16 : ℝ) =
      -(Real.pi * Real.exp (23 / 16 : ℝ) - (1149 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1149 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1149 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1149_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1937629695778943 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1149_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1149 / 1600 : ℝ) (23 / 32 : ℝ) ≤ (6529729 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 16 : ℝ)) (132266005652912859 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1149_product_upper
  have hD : (952636963884229 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1149 / 800 : ℝ) - (23 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell1149_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1149_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1149 / 800 : ℝ) - (23 / 64 : ℝ)) ≤
      (1 / (952636963884229 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (952636963884229 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 64 : ℝ) - Real.pi * Real.exp (1149 / 800 : ℝ)) ≤
      (2 / (952636963884229 / 2500000000 : ℝ) : ℝ) := by
    rw [show (23 / 64 : ℝ) - Real.pi * Real.exp (1149 / 800 : ℝ) =
      -(Real.pi * Real.exp (1149 / 800 : ℝ) - (23 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (132266005652912859 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (132266005652912859 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1149_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1149 / 1600 : ℝ) (23 / 32 : ℝ)) :
    (15967027 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (6529729 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1149_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1149_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1150_leftExp :
    (42101572561 / 10000000000 : ℝ) ≤ Real.exp (23 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 16 : ℝ) (522973071087 / 500000000000 : ℝ)
    (42101572561 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1150_rightExp :
    Real.exp (1151 / 800 : ℝ) ≤ (21077116217 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1151 / 800 : ℝ) (261496750061 / 250000000000 : ℝ)
    (21077116217 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1150_denomUpper :
    Real.exp (64418845767513681 / 5000000000000000 : ℝ) ≤ (393867230677081 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (64418845767513681 / 5000000000000000 : ℝ) (747867545787
    / 500000000000 : ℝ) (393867230677081 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1150_denomLower :
    (968205450868829 / 2500000000 : ℝ) ≤ Real.exp (16083636068132139 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16083636068132139 / 1250000000000000 : ℝ) (373736804937
    / 250000000000 : ℝ) (968205450868829 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1150_product_lower :
    (16533245443132139 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1150_leftExp
    (by norm_num : (0 : ℝ) ≤ (42101572561 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1150_product_upper :
    Real.pi * Real.exp (1151 / 800 : ℝ) ≤ (66215720767513681 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1150_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1150_endpointLower :
    (15751801 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 32 : ℝ) (1151 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16533245443132139 / 1250000000000000 : ℝ) (Real.pi * Real.exp (23 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell1150_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1151 / 800 : ℝ) - (23 / 64 : ℝ)) ≤
      (393867230677081 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1150_denomUpper
    linarith [hpThetaJensenCell1150_product_upper]
  have hi : (1 / (393867230677081 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1151 / 800 : ℝ) - (23 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (393867230677081 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (393867230677081 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 64 : ℝ) - Real.pi * Real.exp (1151 / 800 : ℝ)) := by
    rw [show (23 / 64 : ℝ) - Real.pi * Real.exp (1151 / 800 : ℝ) =
      -(Real.pi * Real.exp (1151 / 800 : ℝ) - (23 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 16 : ℝ)) := by
    have h := hpThetaJensenCell1150_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (393867230677081 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1150_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 32 : ℝ) (1151 / 1600 : ℝ) ≤ (32209219 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1151 / 800 : ℝ)) (66215720767513681 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1151 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1150_product_upper
  have hD : (968205450868829 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 16 : ℝ) - (1151 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1150_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1150_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 16 : ℝ) - (1151 / 3200 : ℝ)) ≤
      (1 / (968205450868829 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (968205450868829 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1151 / 3200 : ℝ) - Real.pi * Real.exp (23 / 16 : ℝ)) ≤
      (2 / (968205450868829 / 2500000000 : ℝ) : ℝ) := by
    rw [show (1151 / 3200 : ℝ) - Real.pi * Real.exp (23 / 16 : ℝ) =
      -(Real.pi * Real.exp (23 / 16 : ℝ) - (1151 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66215720767513681 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (66215720767513681 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1150_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 32 : ℝ) (1151 / 1600 : ℝ)) :
    (15751801 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32209219 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1150_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1150_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1151_leftExp :
    (2634639527 / 625000000 : ℝ) ≤ Real.exp (1151 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1151 / 800 : ℝ) (1045987000243 / 1000000000000 : ℝ)
    (2634639527 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1151_rightExp :
    Real.exp (36 / 25 : ℝ) ≤ (42206958171 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36 / 25 : ℝ) (1046027859909 / 1000000000000 : ℝ)
    (42206958171 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1151_denomUpper :
    Real.exp (129000209341306403 / 10000000000000000 : ℝ) ≤ (800641143219429 / 2000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (129000209341306403 / 10000000000000000 : ℝ)
    (149649492071 / 100000000000 : ℝ) (800641143219429 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1151_denomLower :
    (3936194810402191 / 10000000000 : ℝ) ≤ Real.exp (1006495307613373 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1006495307613373 / 78125000000000 : ℝ) (1495705681221 /
    1000000000000 : ℝ) (3936194810402191 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1151_product_lower :
    (1034620307613373 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (1151 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1151_leftExp
    (by norm_num : (0 : ℝ) ≤ (2634639527 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1151_product_upper :
    Real.pi * Real.exp (36 / 25 : ℝ) ≤ (132597084341306403 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1151_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1151_endpointLower :
    (15539151 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1151 / 1600 : ℝ) (18 / 25 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1034620307613373 / 78125000000000 : ℝ) (Real.pi * Real.exp (1151 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1151_product_lower
  have hD : Real.exp (Real.pi * Real.exp (36 / 25 : ℝ) - (1151 / 3200 : ℝ)) ≤
      (800641143219429 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1151_denomUpper
    linarith [hpThetaJensenCell1151_product_upper]
  have hi : (1 / (800641143219429 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (36 / 25 : ℝ) - (1151 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (800641143219429 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (800641143219429 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1151 / 3200 : ℝ) - Real.pi * Real.exp (36 / 25 : ℝ)) := by
    rw [show (1151 / 3200 : ℝ) - Real.pi * Real.exp (36 / 25 : ℝ) =
      -(Real.pi * Real.exp (36 / 25 : ℝ) - (1151 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1151 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1151 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1151_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (800641143219429 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1151_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1151 / 1600 : ℝ) (18 / 25 : ℝ) ≤ (7943761 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (36 / 25 : ℝ)) (132597084341306403 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (18 / 25 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1151_product_upper
  have hD : (3936194810402191 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1151 / 800 : ℝ) - (9 / 25 : ℝ)) := by
    apply le_trans hpThetaJensenCell1151_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1151_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1151 / 800 : ℝ) - (9 / 25 : ℝ)) ≤
      (1 / (3936194810402191 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3936194810402191 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 25 : ℝ) - Real.pi * Real.exp (1151 / 800 : ℝ)) ≤
      (2 / (3936194810402191 / 10000000000 : ℝ) : ℝ) := by
    rw [show (9 / 25 : ℝ) - Real.pi * Real.exp (1151 / 800 : ℝ) =
      -(Real.pi * Real.exp (1151 / 800 : ℝ) - (9 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (132597084341306403 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (132597084341306403 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1151_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1151 / 1600 : ℝ) (18 / 25 : ℝ)) :
    (15539151 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (7943761 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1151_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1151_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1152_leftExp :
    (42206958169 / 10000000000 : ℝ) ≤ Real.exp (36 / 25 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (36 / 25 : ℝ) (261506964977 / 250000000000 : ℝ)
    (42206958169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1152_rightExp :
    Real.exp (1153 / 800 : ℝ) ≤ (42259749857 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1153 / 800 : ℝ) (1046068721171 / 1000000000000 : ℝ)
    (42259749857 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1152_denomUpper :
    Real.exp (129162934332502201 / 10000000000000000 : ℝ) ≤ (508610097130477 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (129162934332502201 / 10000000000000000 : ℝ)
    (1497256105239 / 1000000000000 : ℝ) (508610097130477 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1152_denomLower :
    (125021487685753 / 312500000 : ℝ) ≤ Real.exp (16124239641008131 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16124239641008131 / 1250000000000000 : ℝ) (149646549517
    / 100000000000 : ℝ) (125021487685753 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1152_product_lower :
    (16574630266008131 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (36 / 25 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1152_leftExp
    (by norm_num : (0 : ℝ) ≤ (42206958169 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1152_product_upper :
    Real.pi * Real.exp (1153 / 800 : ℝ) ≤ (132762934332502201 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1152_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1152_endpointLower :
    (30658101 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (18 / 25 : ℝ) (1153 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16574630266008131 / 1250000000000000 : ℝ) (Real.pi * Real.exp (36 / 25 : ℝ))
    (by norm_num) hpThetaJensenCell1152_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1153 / 800 : ℝ) - (9 / 25 : ℝ)) ≤
      (508610097130477 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1152_denomUpper
    linarith [hpThetaJensenCell1152_product_upper]
  have hi : (1 / (508610097130477 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1153 / 800 : ℝ) - (9 / 25 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (508610097130477 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (508610097130477 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 25 : ℝ) - Real.pi * Real.exp (1153 / 800 : ℝ)) := by
    rw [show (9 / 25 : ℝ) - Real.pi * Real.exp (1153 / 800 : ℝ) =
      -(Real.pi * Real.exp (1153 / 800 : ℝ) - (9 / 25 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (36 / 25 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (36 / 25 : ℝ)) := by
    have h := hpThetaJensenCell1152_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (508610097130477 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1152_endpointUpper :
    hpThetaJensenKernelEndpointUpper (18 / 25 : ℝ) (1153 / 1600 : ℝ) ≤ (15673033 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1153 / 800 : ℝ)) (132762934332502201 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1153 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1152_product_upper
  have hD : (125021487685753 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (36 / 25 : ℝ) - (1153 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1152_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1152_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (36 / 25 : ℝ) - (1153 / 3200 : ℝ)) ≤
      (1 / (125021487685753 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (125021487685753 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1153 / 3200 : ℝ) - Real.pi * Real.exp (36 / 25 : ℝ)) ≤
      (2 / (125021487685753 / 312500000 : ℝ) : ℝ) := by
    rw [show (1153 / 3200 : ℝ) - Real.pi * Real.exp (36 / 25 : ℝ) =
      -(Real.pi * Real.exp (36 / 25 : ℝ) - (1153 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (132762934332502201 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (132762934332502201 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1152_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (18 / 25 : ℝ) (1153 / 1600 : ℝ)) :
    (30658101 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15673033 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1152_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1152_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1153_leftExp :
    (8451949971 / 2000000000 : ℝ) ≤ Real.exp (1153 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1153 / 800 : ℝ) (104606872117 / 100000000000 : ℝ)
    (8451949971 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1153_rightExp :
    Real.exp (577 / 400 : ℝ) ≤ (42312607573 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (577 / 400 : ℝ) (261527396007 / 250000000000 : ℝ)
    (42312607573 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1153_denomUpper :
    Real.exp (129325866763083789 / 10000000000000000 : ℝ) ≤ (1033929767051007 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (129325866763083789 / 10000000000000000 : ℝ)
    (1498018648029 / 1000000000000 : ℝ) (1033929767051007 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1153_denomLower :
    (4066321334285933 / 10000000000 : ℝ) ≤ Real.exp (3228916051661729 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3228916051661729 / 250000000000000 : ℝ) (299445332897 /
    200000000000 : ℝ) (4066321334285933 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1153_product_lower :
    (3319072301661729 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (1153 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1153_leftExp
    (by norm_num : (0 : ℝ) ≤ (8451949971 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1153_product_upper :
    Real.pi * Real.exp (577 / 400 : ℝ) ≤ (132928991763083789 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1153_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1153_endpointLower :
    (7560737 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1153 / 1600 : ℝ) (577 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3319072301661729 / 250000000000000 : ℝ) (Real.pi * Real.exp (1153 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1153_product_lower
  have hD : Real.exp (Real.pi * Real.exp (577 / 400 : ℝ) - (1153 / 3200 : ℝ)) ≤
      (1033929767051007 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1153_denomUpper
    linarith [hpThetaJensenCell1153_product_upper]
  have hi : (1 / (1033929767051007 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (577 / 400 : ℝ) - (1153 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1033929767051007 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1033929767051007 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1153 / 3200 : ℝ) - Real.pi * Real.exp (577 / 400 : ℝ)) := by
    rw [show (1153 / 3200 : ℝ) - Real.pi * Real.exp (577 / 400 : ℝ) =
      -(Real.pi * Real.exp (577 / 400 : ℝ) - (1153 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1153 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1153 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1153_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1033929767051007 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1153_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1153 / 1600 : ℝ) (577 / 800 : ℝ) ≤ (30922231 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (577 / 400 : ℝ)) (132928991763083789 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (577 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1153_product_upper
  have hD : (4066321334285933 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1153 / 800 : ℝ) - (577 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1153_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1153_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1153 / 800 : ℝ) - (577 / 1600 : ℝ)) ≤
      (1 / (4066321334285933 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4066321334285933 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((577 / 1600 : ℝ) - Real.pi * Real.exp (1153 / 800 : ℝ)) ≤
      (2 / (4066321334285933 / 10000000000 : ℝ) : ℝ) := by
    rw [show (577 / 1600 : ℝ) - Real.pi * Real.exp (1153 / 800 : ℝ) =
      -(Real.pi * Real.exp (1153 / 800 : ℝ) - (577 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (132928991763083789 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (132928991763083789 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1153_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1153 / 1600 : ℝ) (577 / 800 : ℝ)) :
    (7560737 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (30922231 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1153_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1153_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1154_leftExp :
    (42312607571 / 10000000000 : ℝ) ≤ Real.exp (577 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (577 / 400 : ℝ) (1046109584027 / 1000000000000 : ℝ)
    (42312607571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1154_rightExp :
    Real.exp (231 / 160 : ℝ) ≤ (42365531403 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (231 / 160 : ℝ) (523075224241 / 500000000000 : ℝ)
    (42365531403 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1154_denomUpper :
    Real.exp (129489006896944979 / 10000000000000000 : ℝ) ≤ (2101871302093371 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (129489006896944979 / 10000000000000000 : ℝ)
    (299756510399 / 200000000000 : ℝ) (2101871302093371 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1154_denomLower :
    (165324702413821 / 400000000 : ℝ) ≤ Real.exp (16164946805524129 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16164946805524129 / 1250000000000000 : ℝ) (1497989192033
    / 1000000000000 : ℝ) (165324702413821 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1154_product_lower :
    (16616118680524129 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (577 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1154_leftExp
    (by norm_num : (0 : ℝ) ≤ (42312607571 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1154_product_upper :
    Real.pi * Real.exp (231 / 160 : ℝ) ≤ (133095256896944979 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1154_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1154_endpointLower :
    (2983279 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (577 / 800 : ℝ) (231 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16616118680524129 / 1250000000000000 : ℝ) (Real.pi * Real.exp (577 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1154_product_lower
  have hD : Real.exp (Real.pi * Real.exp (231 / 160 : ℝ) - (577 / 1600 : ℝ)) ≤
      (2101871302093371 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1154_denomUpper
    linarith [hpThetaJensenCell1154_product_upper]
  have hi : (1 / (2101871302093371 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (231 / 160 : ℝ) - (577 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2101871302093371 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2101871302093371 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((577 / 1600 : ℝ) - Real.pi * Real.exp (231 / 160 : ℝ)) := by
    rw [show (577 / 1600 : ℝ) - Real.pi * Real.exp (231 / 160 : ℝ) =
      -(Real.pi * Real.exp (231 / 160 : ℝ) - (577 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (577 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (577 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1154_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2101871302093371 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1154_endpointUpper :
    hpThetaJensenKernelEndpointUpper (577 / 800 : ℝ) (231 / 320 : ℝ) ≤ (30503487 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (231 / 160 : ℝ)) (133095256896944979 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (231 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1154_product_upper
  have hD : (165324702413821 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (577 / 400 : ℝ) - (231 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell1154_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1154_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (577 / 400 : ℝ) - (231 / 640 : ℝ)) ≤
      (1 / (165324702413821 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (165324702413821 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((231 / 640 : ℝ) - Real.pi * Real.exp (577 / 400 : ℝ)) ≤
      (2 / (165324702413821 / 400000000 : ℝ) : ℝ) := by
    rw [show (231 / 640 : ℝ) - Real.pi * Real.exp (577 / 400 : ℝ) =
      -(Real.pi * Real.exp (577 / 400 : ℝ) - (231 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (133095256896944979 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (133095256896944979 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1154_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (577 / 800 : ℝ) (231 / 320 : ℝ)) :
    (2983279 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (30503487 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1154_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1154_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1155_leftExp :
    (42365531401 / 10000000000 : ℝ) ≤ Real.exp (231 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (231 / 160 : ℝ) (1046150448481 / 1000000000000 : ℝ)
    (42365531401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1155_rightExp :
    Real.exp (289 / 200 : ℝ) ≤ (42418521429 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (289 / 200 : ℝ) (261547828633 / 250000000000 : ℝ)
    (42418521429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1155_denomUpper :
    Real.exp (129652354991696397 / 10000000000000000 : ℝ) ≤ (4272973838833901 / 10000000000 : ℝ)
      := by
  apply hpThetaJensen_exp_upper_scaled32 (129652354991696397 / 10000000000000000 : ℝ)
    (1499547820031 / 1000000000000 : ℝ) (4272973838833901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1155_denomLower :
    (4201098284955889 / 10000000000 : ℝ) ≤ Real.exp (16185339315641299 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16185339315641299 / 1250000000000000 : ℝ) (149875308073
    / 100000000000 : ℝ) (4201098284955889 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1155_product_lower :
    (16636901815641299 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (231 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1155_leftExp
    (by norm_num : (0 : ℝ) ≤ (42365531401 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1155_product_upper :
    Real.pi * Real.exp (289 / 200 : ℝ) ≤ (133261729991696397 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1155_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1155_endpointLower :
    (3678447 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (231 / 320 : ℝ) (289 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16636901815641299 / 1250000000000000 : ℝ) (Real.pi * Real.exp (231 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell1155_product_lower
  have hD : Real.exp (Real.pi * Real.exp (289 / 200 : ℝ) - (231 / 640 : ℝ)) ≤
      (4272973838833901 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1155_denomUpper
    linarith [hpThetaJensenCell1155_product_upper]
  have hi : (1 / (4272973838833901 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (289 / 200 : ℝ) - (231 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4272973838833901 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4272973838833901 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((231 / 640 : ℝ) - Real.pi * Real.exp (289 / 200 : ℝ)) := by
    rw [show (231 / 640 : ℝ) - Real.pi * Real.exp (289 / 200 : ℝ) =
      -(Real.pi * Real.exp (289 / 200 : ℝ) - (231 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (231 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (231 / 160 : ℝ)) := by
    have h := hpThetaJensenCell1155_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4272973838833901 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1155_endpointUpper :
    hpThetaJensenKernelEndpointUpper (231 / 320 : ℝ) (289 / 400 : ℝ) ≤ (30089783 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (289 / 200 : ℝ)) (133261729991696397 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (289 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1155_product_upper
  have hD : (4201098284955889 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (231 / 160 : ℝ) - (289 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell1155_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1155_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (231 / 160 : ℝ) - (289 / 800 : ℝ)) ≤
      (1 / (4201098284955889 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4201098284955889 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((289 / 800 : ℝ) - Real.pi * Real.exp (231 / 160 : ℝ)) ≤
      (2 / (4201098284955889 / 10000000000 : ℝ) : ℝ) := by
    rw [show (289 / 800 : ℝ) - Real.pi * Real.exp (231 / 160 : ℝ) =
      -(Real.pi * Real.exp (231 / 160 : ℝ) - (289 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (133261729991696397 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (133261729991696397 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1155_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (231 / 320 : ℝ) (289 / 400 : ℝ)) :
    (3678447 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (30089783 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1155_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1155_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1156_leftExp :
    (42418521427 / 10000000000 : ℝ) ≤ Real.exp (289 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (289 / 200 : ℝ) (1046191314531 / 1000000000000 : ℝ)
    (42418521427 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1156_rightExp :
    Real.exp (1157 / 800 : ℝ) ≤ (21235788867 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1157 / 800 : ℝ) (523116091089 / 500000000000 : ℝ)
    (21235788867 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1156_denomUpper :
    Real.exp (64907955654045131 / 5000000000000000 : ℝ) ≤ (4343435678158299 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (64907955654045131 / 5000000000000000 : ℝ) (1500314455051
    / 1000000000000 : ℝ) (4343435678158299 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1156_denomLower :
    (2135142973910499 / 5000000000 : ℝ) ≤ Real.exp (16205757820861473 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (16205757820861473 / 1250000000000000 : ℝ) (149951833347
    / 100000000000 : ℝ) (2135142973910499 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1156_product_lower :
    (16657710945861473 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (289 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1156_leftExp
    (by norm_num : (0 : ℝ) ≤ (42418521427 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1156_product_upper :
    Real.pi * Real.exp (1157 / 800 : ℝ) ≤ (66714205654045131 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1156_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1156_endpointLower :
    (5805451 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (289 / 400 : ℝ) (1157 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16657710945861473 / 1250000000000000 : ℝ) (Real.pi * Real.exp (289 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell1156_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1157 / 800 : ℝ) - (289 / 800 : ℝ)) ≤
      (4343435678158299 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1156_denomUpper
    linarith [hpThetaJensenCell1156_product_upper]
  have hi : (1 / (4343435678158299 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1157 / 800 : ℝ) - (289 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4343435678158299 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4343435678158299 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((289 / 800 : ℝ) - Real.pi * Real.exp (1157 / 800 : ℝ)) := by
    rw [show (289 / 800 : ℝ) - Real.pi * Real.exp (1157 / 800 : ℝ) =
      -(Real.pi * Real.exp (1157 / 800 : ℝ) - (289 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (289 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (289 / 200 : ℝ)) := by
    have h := hpThetaJensenCell1156_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4343435678158299 / 10000000000 : ℝ))
    hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1156_endpointUpper :
    hpThetaJensenKernelEndpointUpper (289 / 400 : ℝ) (1157 / 1600 : ℝ) ≤ (5936213 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1157 / 800 : ℝ)) (66714205654045131 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1157 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1156_product_upper
  have hD : (2135142973910499 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (289 / 200 : ℝ) - (1157 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1156_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1156_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (289 / 200 : ℝ) - (1157 / 3200 : ℝ)) ≤
      (1 / (2135142973910499 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2135142973910499 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1157 / 3200 : ℝ) - Real.pi * Real.exp (289 / 200 : ℝ)) ≤
      (2 / (2135142973910499 / 5000000000 : ℝ) : ℝ) := by
    rw [show (1157 / 3200 : ℝ) - Real.pi * Real.exp (289 / 200 : ℝ) =
      -(Real.pi * Real.exp (289 / 200 : ℝ) - (1157 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (66714205654045131 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (66714205654045131 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1156_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (289 / 400 : ℝ) (1157 / 1600 : ℝ)) :
    (5805451 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5936213 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1156_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1156_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1157_leftExp :
    (10617894433 / 2500000000 : ℝ) ≤ Real.exp (1157 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1157 / 800 : ℝ) (1046232182177 / 1000000000000 : ℝ)
    (10617894433 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1157_rightExp :
    Real.exp (579 / 400 : ℝ) ≤ (42524700401 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (579 / 400 : ℝ) (1046273051421 / 1000000000000 : ℝ)
    (42524700401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1157_denomUpper :
    Real.exp (129979676106878793 / 10000000000000000 : ℝ) ≤ (176606059546633 / 400000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (129979676106878793 / 10000000000000000 : ℝ) (60043298399
    / 40000000000 : ℝ) (176606059546633 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1157_denomLower :
    (67823491258299 / 156250000 : ℝ) ≤ Real.exp (4056550588444667 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4056550588444667 / 312500000000000 : ℝ) (1500284953167 /
    1000000000000 : ℝ) (67823491258299 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1157_product_lower :
    (4169636525944667 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (1157 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1157_leftExp
    (by norm_num : (0 : ℝ) ≤ (10617894433 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1157_product_upper :
    Real.pi * Real.exp (579 / 400 : ℝ) ≤ (133595301106878793 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1157_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1157_endpointLower :
    (894743 / 312500000 : ℝ) ≤ hpThetaTraceEndpointLower (1157 / 1600 : ℝ) (579 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4169636525944667 / 312500000000000 : ℝ) (Real.pi * Real.exp (1157 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1157_product_lower
  have hD : Real.exp (Real.pi * Real.exp (579 / 400 : ℝ) - (1157 / 3200 : ℝ)) ≤
      (176606059546633 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1157_denomUpper
    linarith [hpThetaJensenCell1157_product_upper]
  have hi : (1 / (176606059546633 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (579 / 400 : ℝ) - (1157 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (176606059546633 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (176606059546633 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1157 / 3200 : ℝ) - Real.pi * Real.exp (579 / 400 : ℝ)) := by
    rw [show (1157 / 3200 : ℝ) - Real.pi * Real.exp (579 / 400 : ℝ) =
      -(Real.pi * Real.exp (579 / 400 : ℝ) - (1157 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1157 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1157 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1157_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (176606059546633 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1157_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1157 / 1600 : ℝ) (579 / 800 : ℝ) ≤ (29277283 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (579 / 400 : ℝ)) (133595301106878793 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (579 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1157_product_upper
  have hD : (67823491258299 / 156250000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1157 / 800 : ℝ) - (579 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell1157_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1157_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1157 / 800 : ℝ) - (579 / 1600 : ℝ)) ≤
      (1 / (67823491258299 / 156250000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (67823491258299 / 156250000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((579 / 1600 : ℝ) - Real.pi * Real.exp (1157 / 800 : ℝ)) ≤
      (2 / (67823491258299 / 156250000 : ℝ) : ℝ) := by
    rw [show (579 / 1600 : ℝ) - Real.pi * Real.exp (1157 / 800 : ℝ) =
      -(Real.pi * Real.exp (1157 / 800 : ℝ) - (579 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (133595301106878793 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (133595301106878793 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1157_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1157 / 1600 : ℝ) (579 / 800 : ℝ)) :
    (894743 / 312500000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (29277283 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1157_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1157_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1158_leftExp :
    (42524700399 / 10000000000 : ℝ) ≤ Real.exp (579 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (579 / 400 : ℝ) (52313652571 / 50000000000 : ℝ)
    (42524700399 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1158_rightExp :
    Real.exp (1159 / 800 : ℝ) ≤ (42577889513 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1159 / 800 : ℝ) (52315696113 / 50000000000 : ℝ)
    (42577889513 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1158_denomUpper :
    Real.exp (130143649648814209 / 10000000000000000 : ℝ) ≤ (561018138376379 / 1250000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (130143649648814209 / 10000000000000000 : ℝ) (46932869929
    / 31250000000 : ℝ) (561018138376379 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1158_denomLower :
    (55154676433647 / 125000000 : ℝ) ≤ Real.exp (16246672946986901 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (16246672946986901 / 1250000000000000 : ℝ) (1501052942739
    / 1000000000000 : ℝ) (55154676433647 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1158_product_lower :
    (16699407321986901 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (579 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1158_leftExp
    (by norm_num : (0 : ℝ) ≤ (42524700399 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1158_product_upper :
    Real.pi * Real.exp (1159 / 800 : ℝ) ≤ (133762399648814209 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1158_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1158_endpointLower :
    (2824109 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (579 / 800 : ℝ) (1159 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (16699407321986901 / 1250000000000000 : ℝ) (Real.pi * Real.exp (579 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell1158_product_lower
  have hD : Real.exp (Real.pi * Real.exp (1159 / 800 : ℝ) - (579 / 1600 : ℝ)) ≤
      (561018138376379 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1158_denomUpper
    linarith [hpThetaJensenCell1158_product_upper]
  have hi : (1 / (561018138376379 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (1159 / 800 : ℝ) - (579 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (561018138376379 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (561018138376379 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((579 / 1600 : ℝ) - Real.pi * Real.exp (1159 / 800 : ℝ)) := by
    rw [show (579 / 1600 : ℝ) - Real.pi * Real.exp (1159 / 800 : ℝ) =
      -(Real.pi * Real.exp (1159 / 800 : ℝ) - (579 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (579 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (579 / 400 : ℝ)) := by
    have h := hpThetaJensenCell1158_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (561018138376379 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1158_endpointUpper :
    hpThetaJensenKernelEndpointUpper (579 / 800 : ℝ) (1159 / 1600 : ℝ) ≤ (5775677 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (1159 / 800 : ℝ)) (133762399648814209 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (1159 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1158_product_upper
  have hD : (55154676433647 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (579 / 400 : ℝ) - (1159 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell1158_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1158_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (579 / 400 : ℝ) - (1159 / 3200 : ℝ)) ≤
      (1 / (55154676433647 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (55154676433647 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((1159 / 3200 : ℝ) - Real.pi * Real.exp (579 / 400 : ℝ)) ≤
      (2 / (55154676433647 / 125000000 : ℝ) : ℝ) := by
    rw [show (1159 / 3200 : ℝ) - Real.pi * Real.exp (579 / 400 : ℝ) =
      -(Real.pi * Real.exp (579 / 400 : ℝ) - (1159 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (133762399648814209 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (133762399648814209 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1158_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (579 / 800 : ℝ) (1159 / 1600 : ℝ)) :
    (2824109 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5775677 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1158_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1158_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1159_leftExp :
    (4257788951 / 1000000000 : ℝ) ≤ Real.exp (1159 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1159 / 800 : ℝ) (1046313922259 / 1000000000000 : ℝ)
    (4257788951 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1159_rightExp :
    Real.exp (29 / 20 : ℝ) ≤ (666111643 / 156250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 20 : ℝ) (130794349337 / 125000000000 : ℝ)
    (666111643 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1159_denomUpper :
    Real.exp (2036059877992299 / 156250000000000 : ℝ) ≤ (114061021222207 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2036059877992299 / 156250000000000 : ℝ) (1502622591229 /
    1000000000000 : ℝ) (114061021222207 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell1159_denomLower :
    (560665223849171 / 1250000000 : ℝ) ≤ Real.exp (1626716963268749 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1626716963268749 / 125000000000000 : ℝ) (1501822305099 /
    1000000000000 : ℝ) (560665223849171 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell1159_product_lower :
    (1672029463268749 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1159 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1159_leftExp
    (by norm_num : (0 : ℝ) ≤ (4257788951 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1159_product_upper :
    Real.pi * Real.exp (29 / 20 : ℝ) ≤ (2092651674867299 / 156250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell1159_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell1159_endpointLower :
    (27855147 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1159 / 1600 : ℝ) (29 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1672029463268749 / 125000000000000 : ℝ) (Real.pi * Real.exp (1159 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell1159_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 20 : ℝ) - (1159 / 3200 : ℝ)) ≤
      (114061021222207 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell1159_denomUpper
    linarith [hpThetaJensenCell1159_product_upper]
  have hi : (1 / (114061021222207 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 20 : ℝ) - (1159 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (114061021222207 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (114061021222207 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1159 / 3200 : ℝ) - Real.pi * Real.exp (29 / 20 : ℝ)) := by
    rw [show (1159 / 3200 : ℝ) - Real.pi * Real.exp (29 / 20 : ℝ) =
      -(Real.pi * Real.exp (29 / 20 : ℝ) - (1159 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1159 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1159 / 800 : ℝ)) := by
    have h := hpThetaJensenCell1159_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (114061021222207 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell1159_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1159 / 1600 : ℝ) (29 / 40 : ℝ) ≤ (14242161 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 20 : ℝ)) (2092651674867299 / 156250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell1159_product_upper
  have hD : (560665223849171 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1159 / 800 : ℝ) - (29 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell1159_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell1159_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1159 / 800 : ℝ) - (29 / 80 : ℝ)) ≤
      (1 / (560665223849171 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (560665223849171 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 80 : ℝ) - Real.pi * Real.exp (1159 / 800 : ℝ)) ≤
      (2 / (560665223849171 / 1250000000 : ℝ) : ℝ) := by
    rw [show (29 / 80 : ℝ) - Real.pi * Real.exp (1159 / 800 : ℝ) =
      -(Real.pi * Real.exp (1159 / 800 : ℝ) - (29 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2092651674867299 / 156250000000000 : ℝ) ^ 2 - 6 *
      (2092651674867299 / 156250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell1159_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1159 / 1600 : ℝ) (29 / 40 : ℝ)) :
    (27855147 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (14242161 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell1159_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell1159_endpointUpper

def hpThetaJensenCellsBatch057Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (36048873 / 10000000000 : ℝ)
  | 1 => (3556961 / 1000000000 : ℝ)
  | 2 => (35095993 / 10000000000 : ℝ)
  | 3 => (6925593 / 2000000000 : ℝ)
  | 4 => (3416547 / 1000000000 : ℝ)
  | 5 => (8427113 / 2500000000 : ℝ)
  | 6 => (4157107 / 1250000000 : ℝ)
  | 7 => (8202657 / 2500000000 : ℝ)
  | 8 => (32369711 / 10000000000 : ℝ)
  | 9 => (15967027 / 5000000000 : ℝ)
  | 10 => (15751801 / 5000000000 : ℝ)
  | 11 => (15539151 / 5000000000 : ℝ)
  | 12 => (30658101 / 10000000000 : ℝ)
  | 13 => (7560737 / 2500000000 : ℝ)
  | 14 => (2983279 / 1000000000 : ℝ)
  | 15 => (3678447 / 1250000000 : ℝ)
  | 16 => (5805451 / 2000000000 : ℝ)
  | 17 => (894743 / 312500000 : ℝ)
  | 18 => (2824109 / 1000000000 : ℝ)
  | 19 => (27855147 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch057Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9212201 / 2500000000 : ℝ)
  | 1 => (36359641 / 10000000000 : ℝ)
  | 2 => (35876231 / 10000000000 : ℝ)
  | 3 => (7079703 / 2000000000 : ℝ)
  | 4 => (34926437 / 10000000000 : ℝ)
  | 5 => (1722997 / 500000000 : ℝ)
  | 6 => (4249871 / 1250000000 : ℝ)
  | 7 => (6708693 / 2000000000 : ℝ)
  | 8 => (129271 / 39062500 : ℝ)
  | 9 => (6529729 / 2000000000 : ℝ)
  | 10 => (32209219 / 10000000000 : ℝ)
  | 11 => (7943761 / 2500000000 : ℝ)
  | 12 => (15673033 / 5000000000 : ℝ)
  | 13 => (30922231 / 10000000000 : ℝ)
  | 14 => (30503487 / 10000000000 : ℝ)
  | 15 => (30089783 / 10000000000 : ℝ)
  | 16 => (5936213 / 2000000000 : ℝ)
  | 17 => (29277283 / 10000000000 : ℝ)
  | 18 => (5775677 / 2000000000 : ℝ)
  | 19 => (14242161 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch057_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch057Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch057Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell1140_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1141_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1142_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1143_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1144_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1145_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1146_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1147_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1148_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1149_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1150_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1151_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1152_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1153_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1154_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1155_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1156_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1157_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1158_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell1159_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper] at h ⊢
    exact h

end HodgeProofHP
