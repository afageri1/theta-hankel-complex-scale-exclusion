import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell100_leftExp :
    (1133148453 / 1000000000 : ℝ) ≤ Real.exp (1 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 8 : ℝ) (501956944669 / 500000000000 : ℝ) (1133148453
    / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell100_rightExp :
    Real.exp (101 / 800 : ℝ) ≤ (11345657743 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (101 / 800 : ℝ) (1003953105491 / 1000000000000 : ℝ)
    (11345657743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell100_denomUpper :
    Real.exp (35330938945804599 / 10000000000000000 : ℝ) ≤ (342297070629 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35330938945804599 / 10000000000000000 : ℝ) (558367463639
    / 500000000000 : ℝ) (342297070629 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell100_denomLower :
    (340669468879 / 10000000000 : ℝ) ≤ Real.exp (441040951844647 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (441040951844647 / 125000000000000 : ℝ) (111656860619 /
    100000000000 : ℝ) (340669468879 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell100_product_lower :
    (444986264344647 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell100_leftExp
    (by norm_num : (0 : ℝ) ≤ (1133148453 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell100_product_upper :
    Real.pi * Real.exp (101 / 800 : ℝ) ≤ (35643438945804599 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell100_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell100_endpointLower :
    (4284572137 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 16 : ℝ) (101 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (444986264344647 / 125000000000000 : ℝ) (Real.pi * Real.exp (1 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell100_product_lower
  have hD : Real.exp (Real.pi * Real.exp (101 / 800 : ℝ) - (1 / 32 : ℝ)) ≤
      (342297070629 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell100_denomUpper
    linarith [hpThetaJensenCell100_product_upper]
  have hi : (1 / (342297070629 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (101 / 800 : ℝ) - (1 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (342297070629 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (342297070629 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 32 : ℝ) - Real.pi * Real.exp (101 / 800 : ℝ)) := by
    rw [show (1 / 32 : ℝ) - Real.pi * Real.exp (101 / 800 : ℝ) =
      -(Real.pi * Real.exp (101 / 800 : ℝ) - (1 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 8 : ℝ)) := by
    have h := hpThetaJensenCell100_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (342297070629 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell100_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 16 : ℝ) (101 / 1600 : ℝ) ≤ (8662248677 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (101 / 800 : ℝ)) (35643438945804599 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (101 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell100_product_upper
  have hD : (340669468879 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 8 : ℝ) - (101 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell100_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell100_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 8 : ℝ) - (101 / 3200 : ℝ)) ≤
      (1 / (340669468879 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (340669468879 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((101 / 3200 : ℝ) - Real.pi * Real.exp (1 / 8 : ℝ)) ≤
      (2 / (340669468879 / 10000000000 : ℝ) : ℝ) := by
    rw [show (101 / 3200 : ℝ) - Real.pi * Real.exp (1 / 8 : ℝ) =
      -(Real.pi * Real.exp (1 / 8 : ℝ) - (101 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35643438945804599 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35643438945804599 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell100_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 16 : ℝ) (101 / 1600 : ℝ)) :
    (4284572137 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8662248677 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell100_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell100_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell101_leftExp :
    (5672828871 / 5000000000 : ℝ) ≤ Real.exp (101 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (101 / 800 : ℝ) (100395310549 / 100000000000 : ℝ)
    (5672828871 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell101_rightExp :
    Real.exp (51 / 400 : ℝ) ≤ (11359848683 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51 / 400 : ℝ) (40159692927 / 40000000000 : ℝ)
    (11359848683 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell101_denomUpper :
    Real.exp (35372396103572019 / 10000000000000000 : ℝ) ≤ (42964885323 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35372396103572019 / 10000000000000000 : ℝ) (11168796137
    / 10000000000 : ℝ) (42964885323 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell101_denomLower :
    (34208281357 / 1000000000 : ℝ) ≤ Real.exp (2207792349812829 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2207792349812829 / 625000000000000 : ℝ) (1116713076657 /
    1000000000000 : ℝ) (34208281357 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell101_product_lower :
    (2227714224812829 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (101 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell101_leftExp
    (by norm_num : (0 : ℝ) ≤ (5672828871 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell101_product_upper :
    Real.pi * Real.exp (51 / 400 : ℝ) ≤ (35688021103572019 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell101_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell101_endpointLower :
    (4281417903 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (101 / 1600 : ℝ) (51 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2227714224812829 / 625000000000000 : ℝ) (Real.pi * Real.exp (101 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell101_product_lower
  have hD : Real.exp (Real.pi * Real.exp (51 / 400 : ℝ) - (101 / 3200 : ℝ)) ≤
      (42964885323 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell101_denomUpper
    linarith [hpThetaJensenCell101_product_upper]
  have hi : (1 / (42964885323 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (51 / 400 : ℝ) - (101 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (42964885323 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (42964885323 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((101 / 3200 : ℝ) - Real.pi * Real.exp (51 / 400 : ℝ)) := by
    rw [show (101 / 3200 : ℝ) - Real.pi * Real.exp (51 / 400 : ℝ) =
      -(Real.pi * Real.exp (51 / 400 : ℝ) - (101 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (101 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (101 / 800 : ℝ)) := by
    have h := hpThetaJensenCell101_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (42964885323 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell101_endpointUpper :
    hpThetaJensenKernelEndpointUpper (101 / 1600 : ℝ) (51 / 800 : ℝ) ≤ (17311805831 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (51 / 400 : ℝ)) (35688021103572019 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (51 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell101_product_upper
  have hD : (34208281357 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (101 / 800 : ℝ) - (51 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell101_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell101_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (101 / 800 : ℝ) - (51 / 1600 : ℝ)) ≤
      (1 / (34208281357 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (34208281357 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((51 / 1600 : ℝ) - Real.pi * Real.exp (101 / 800 : ℝ)) ≤
      (2 / (34208281357 / 1000000000 : ℝ) : ℝ) := by
    rw [show (51 / 1600 : ℝ) - Real.pi * Real.exp (101 / 800 : ℝ) =
      -(Real.pi * Real.exp (101 / 800 : ℝ) - (51 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (35688021103572019 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (35688021103572019 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell101_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (101 / 1600 : ℝ) (51 / 800 : ℝ)) :
    (4281417903 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17311805831 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell101_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell101_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell102_leftExp :
    (5679924341 / 5000000000 : ℝ) ≤ Real.exp (51 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (51 / 400 : ℝ) (501996161587 / 500000000000 : ℝ)
    (5679924341 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell102_rightExp :
    Real.exp (103 / 800 : ℝ) ≤ (2843514343 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (103 / 800 : ℝ) (1004031542391 / 1000000000000 : ℝ)
    (2843514343 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell102_denomUpper :
    Real.exp (8853477255368399 / 2500000000000000 : ℝ) ≤ (69029785317 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8853477255368399 / 2500000000000000 : ℝ) (111702451351 /
    100000000000 : ℝ) (69029785317 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell102_denomLower :
    (17175196747 / 500000000 : ℝ) ≤ Real.exp (2210383421286359 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2210383421286359 / 625000000000000 : ℝ) (558428880099 /
    500000000000 : ℝ) (17175196747 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell102_product_lower :
    (2230500608786359 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (51 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell102_leftExp
    (by norm_num : (0 : ℝ) ≤ (5679924341 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell102_product_upper :
    Real.pi * Real.exp (103 / 800 : ℝ) ≤ (8933164755368399 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell102_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell102_endpointLower :
    (17112934997 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 800 : ℝ) (103 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2230500608786359 / 625000000000000 : ℝ) (Real.pi * Real.exp (51 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell102_product_lower
  have hD : Real.exp (Real.pi * Real.exp (103 / 800 : ℝ) - (51 / 1600 : ℝ)) ≤
      (69029785317 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell102_denomUpper
    linarith [hpThetaJensenCell102_product_upper]
  have hi : (1 / (69029785317 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (103 / 800 : ℝ) - (51 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (69029785317 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (69029785317 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((51 / 1600 : ℝ) - Real.pi * Real.exp (103 / 800 : ℝ)) := by
    rw [show (51 / 1600 : ℝ) - Real.pi * Real.exp (103 / 800 : ℝ) =
      -(Real.pi * Real.exp (103 / 800 : ℝ) - (51 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (51 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (51 / 400 : ℝ)) := by
    have h := hpThetaJensenCell102_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (69029785317 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell102_endpointUpper :
    hpThetaJensenKernelEndpointUpper (51 / 800 : ℝ) (103 / 1600 : ℝ) ≤ (345979869 / 200000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (103 / 800 : ℝ)) (8933164755368399 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (103 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell102_product_upper
  have hD : (17175196747 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (51 / 400 : ℝ) - (103 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell102_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell102_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (51 / 400 : ℝ) - (103 / 3200 : ℝ)) ≤
      (1 / (17175196747 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17175196747 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((103 / 3200 : ℝ) - Real.pi * Real.exp (51 / 400 : ℝ)) ≤
      (2 / (17175196747 / 500000000 : ℝ) : ℝ) := by
    rw [show (103 / 3200 : ℝ) - Real.pi * Real.exp (51 / 400 : ℝ) =
      -(Real.pi * Real.exp (51 / 400 : ℝ) - (103 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8933164755368399 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8933164755368399 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell102_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (51 / 800 : ℝ) (103 / 1600 : ℝ)) :
    (17112934997 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (345979869 / 200000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell102_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell102_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell103_leftExp :
    (11374057371 / 10000000000 : ℝ) ≤ Real.exp (103 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (103 / 800 : ℝ) (100403154239 / 100000000000 : ℝ)
    (11374057371 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell103_rightExp :
    Real.exp (13 / 100 : ℝ) ≤ (5694141917 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (13 / 100 : ℝ) (50203538157 / 50000000000 : ℝ)
    (5694141917 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell103_denomUpper :
    Real.exp (17727738887453781 / 5000000000000000 : ℝ) ≤ (346586653809 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17727738887453781 / 5000000000000000 : ℝ) (22343392541 /
    20000000000 : ℝ) (346586653809 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell103_denomLower :
    (344932883461 / 10000000000 : ℝ) ≤ Real.exp (4425955955534329 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4425955955534329 / 1250000000000000 : ℝ) (279250664281 /
    250000000000 : ℝ) (344932883461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell103_product_lower :
    (4466580955534329 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (103 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell103_leftExp
    (by norm_num : (0 : ℝ) ≤ (11374057371 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell103_product_upper :
    Real.pi * Real.exp (13 / 100 : ℝ) ≤ (17888676387453781 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell103_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell103_endpointLower :
    (2137509869 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (103 / 1600 : ℝ) (13 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4466580955534329 / 1250000000000000 : ℝ) (Real.pi * Real.exp (103 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell103_product_lower
  have hD : Real.exp (Real.pi * Real.exp (13 / 100 : ℝ) - (103 / 3200 : ℝ)) ≤
      (346586653809 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell103_denomUpper
    linarith [hpThetaJensenCell103_product_upper]
  have hi : (1 / (346586653809 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (13 / 100 : ℝ) - (103 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (346586653809 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (346586653809 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((103 / 3200 : ℝ) - Real.pi * Real.exp (13 / 100 : ℝ)) := by
    rw [show (103 / 3200 : ℝ) - Real.pi * Real.exp (13 / 100 : ℝ) =
      -(Real.pi * Real.exp (13 / 100 : ℝ) - (103 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (103 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (103 / 800 : ℝ)) := by
    have h := hpThetaJensenCell103_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (346586653809 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell103_endpointUpper :
    hpThetaJensenKernelEndpointUpper (103 / 1600 : ℝ) (13 / 200 : ℝ) ≤ (17286060487 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (13 / 100 : ℝ)) (17888676387453781 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (13 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell103_product_upper
  have hD : (344932883461 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (103 / 800 : ℝ) - (13 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell103_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell103_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (103 / 800 : ℝ) - (13 / 400 : ℝ)) ≤
      (1 / (344932883461 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (344932883461 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((13 / 400 : ℝ) - Real.pi * Real.exp (103 / 800 : ℝ)) ≤
      (2 / (344932883461 / 10000000000 : ℝ) : ℝ) := by
    rw [show (13 / 400 : ℝ) - Real.pi * Real.exp (103 / 800 : ℝ) =
      -(Real.pi * Real.exp (103 / 800 : ℝ) - (13 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17888676387453781 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (17888676387453781 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell103_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (103 / 1600 : ℝ) (13 / 200 : ℝ)) :
    (2137509869 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17286060487 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell103_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell103_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell104_leftExp :
    (11388283833 / 10000000000 : ℝ) ≤ Real.exp (13 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (13 / 100 : ℝ) (1004070763139 / 1000000000000 : ℝ)
    (11388283833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell104_rightExp :
    Real.exp (21 / 160 : ℝ) ≤ (1140252809 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 160 : ℝ) (50205499271 / 50000000000 : ℝ)
    (1140252809 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell104_denomUpper :
    Real.exp (3549710242984737 / 1000000000000000 : ℝ) ≤ (348032315463 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3549710242984737 / 1000000000000000 : ℝ) (1117314954627
    / 1000000000000 : ℝ) (348032315463 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell104_denomLower :
    (1385478841 / 40000000 : ℝ) ≤ Real.exp (4431152047935267 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4431152047935267 / 1250000000000000 : ℝ) (558573883887 /
    500000000000 : ℝ) (1385478841 / 40000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell104_product_lower :
    (4472167672935267 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (13 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell104_leftExp
    (by norm_num : (0 : ℝ) ≤ (11388283833 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell104_product_upper :
    Real.pi * Real.exp (21 / 160 : ℝ) ≤ (3582210242984737 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell104_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell104_endpointLower :
    (8543551879 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 200 : ℝ) (21 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4472167672935267 / 1250000000000000 : ℝ) (Real.pi * Real.exp (13 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell104_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 160 : ℝ) - (13 / 400 : ℝ)) ≤
      (348032315463 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell104_denomUpper
    linarith [hpThetaJensenCell104_product_upper]
  have hi : (1 / (348032315463 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 160 : ℝ) - (13 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (348032315463 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (348032315463 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((13 / 400 : ℝ) - Real.pi * Real.exp (21 / 160 : ℝ)) := by
    rw [show (13 / 400 : ℝ) - Real.pi * Real.exp (21 / 160 : ℝ) =
      -(Real.pi * Real.exp (21 / 160 : ℝ) - (13 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (13 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (13 / 100 : ℝ)) := by
    have h := hpThetaJensenCell104_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (348032315463 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell104_endpointUpper :
    hpThetaJensenKernelEndpointUpper (13 / 200 : ℝ) (21 / 320 : ℝ) ≤ (17273007197 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 160 : ℝ)) (3582210242984737 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell104_product_upper
  have hD : (1385478841 / 40000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (13 / 100 : ℝ) - (21 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell104_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell104_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (13 / 100 : ℝ) - (21 / 640 : ℝ)) ≤
      (1 / (1385478841 / 40000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1385478841 / 40000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 640 : ℝ) - Real.pi * Real.exp (13 / 100 : ℝ)) ≤
      (2 / (1385478841 / 40000000 : ℝ) : ℝ) := by
    rw [show (21 / 640 : ℝ) - Real.pi * Real.exp (13 / 100 : ℝ) =
      -(Real.pi * Real.exp (13 / 100 : ℝ) - (21 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3582210242984737 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3582210242984737 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell104_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (13 / 200 : ℝ) (21 / 320 : ℝ)) :
    (8543551879 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17273007197 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell104_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell104_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell105_leftExp :
    (1425316011 / 1250000000 : ℝ) ≤ Real.exp (21 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 160 : ℝ) (1004109985419 / 1000000000000 : ℝ)
    (1425316011 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell105_rightExp :
    Real.exp (53 / 400 : ℝ) ≤ (5708395081 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 400 : ℝ) (62759325577 / 62500000000 : ℝ)
    (5708395081 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell105_denomUpper :
    Real.exp (17769391527704033 / 5000000000000000 : ℝ) ≤ (13979438531 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17769391527704033 / 5000000000000000 : ℝ) (1117460496563
    / 1000000000000 : ℝ) (13979438531 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell105_denomLower :
    (434768083 / 12500000 : ℝ) ≤ Real.exp (554544390953689 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (554544390953689 / 156250000000000 : ℝ) (1117293092447 /
    1000000000000 : ℝ) (434768083 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell105_product_lower :
    (559720172203689 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell105_leftExp
    (by norm_num : (0 : ℝ) ≤ (1425316011 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell105_product_upper :
    Real.pi * Real.exp (53 / 400 : ℝ) ≤ (17933454027704033 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell105_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell105_endpointLower :
    (682960387 / 400000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 320 : ℝ) (53 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (559720172203689 / 156250000000000 : ℝ) (Real.pi * Real.exp (21 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell105_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 400 : ℝ) - (21 / 640 : ℝ)) ≤
      (13979438531 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell105_denomUpper
    linarith [hpThetaJensenCell105_product_upper]
  have hi : (1 / (13979438531 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 400 : ℝ) - (21 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (13979438531 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (13979438531 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 640 : ℝ) - Real.pi * Real.exp (53 / 400 : ℝ)) := by
    rw [show (21 / 640 : ℝ) - Real.pi * Real.exp (53 / 400 : ℝ) =
      -(Real.pi * Real.exp (53 / 400 : ℝ) - (21 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 160 : ℝ)) := by
    have h := hpThetaJensenCell105_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (13979438531 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell105_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 320 : ℝ) (53 / 800 : ℝ) ≤ (17259833859 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 400 : ℝ)) (17933454027704033 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell105_product_upper
  have hD : (434768083 / 12500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 160 : ℝ) - (53 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell105_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell105_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 160 : ℝ) - (53 / 1600 : ℝ)) ≤
      (1 / (434768083 / 12500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (434768083 / 12500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 1600 : ℝ) - Real.pi * Real.exp (21 / 160 : ℝ)) ≤
      (2 / (434768083 / 12500000 : ℝ) : ℝ) := by
    rw [show (53 / 1600 : ℝ) - Real.pi * Real.exp (21 / 160 : ℝ) =
      -(Real.pi * Real.exp (21 / 160 : ℝ) - (53 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (17933454027704033 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (17933454027704033 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell105_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 320 : ℝ) (53 / 800 : ℝ)) :
    (682960387 / 400000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17259833859 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell105_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell105_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell106_leftExp :
    (142709877 / 125000000 : ℝ) ≤ Real.exp (53 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 400 : ℝ) (1004149209231 / 1000000000000 : ℝ)
    (142709877 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell106_rightExp :
    Real.exp (107 / 800 : ℝ) ≤ (1428883759 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (107 / 800 : ℝ) (1004188434577 / 1000000000000 : ℝ)
    (1428883759 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell106_denomUpper :
    Real.exp (4447564965088087 / 1250000000000000 : ℝ) ≤ (350947649309 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4447564965088087 / 1250000000000000 : ℝ) (139700781647 /
    125000000000 : ℝ) (350947649309 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell106_denomLower :
    (174633601903 / 5000000000 : ℝ) ≤ Real.exp (55519565050523 / 15625000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (55519565050523 / 15625000000000 : ℝ) (223487726297 /
    200000000000 : ℝ) (174633601903 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell106_product_lower :
    (56042025988023 / 15625000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell106_leftExp
    (by norm_num : (0 : ℝ) ≤ (142709877 / 125000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell106_product_upper :
    Real.pi * Real.exp (107 / 800 : ℝ) ≤ (4488971215088087 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell106_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell106_endpointLower :
    (8530398491 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 800 : ℝ) (107 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (56042025988023 / 15625000000000 : ℝ) (Real.pi * Real.exp (53 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell106_product_lower
  have hD : Real.exp (Real.pi * Real.exp (107 / 800 : ℝ) - (53 / 1600 : ℝ)) ≤
      (350947649309 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell106_denomUpper
    linarith [hpThetaJensenCell106_product_upper]
  have hi : (1 / (350947649309 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (107 / 800 : ℝ) - (53 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (350947649309 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (350947649309 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 1600 : ℝ) - Real.pi * Real.exp (107 / 800 : ℝ)) := by
    rw [show (53 / 1600 : ℝ) - Real.pi * Real.exp (107 / 800 : ℝ) =
      -(Real.pi * Real.exp (107 / 800 : ℝ) - (53 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 400 : ℝ)) := by
    have h := hpThetaJensenCell106_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (350947649309 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell106_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 800 : ℝ) (107 / 1600 : ℝ) ≤ (4311635183 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (107 / 800 : ℝ)) (4488971215088087 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (107 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell106_product_upper
  have hD : (174633601903 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 400 : ℝ) - (107 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell106_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell106_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 400 : ℝ) - (107 / 3200 : ℝ)) ≤
      (1 / (174633601903 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (174633601903 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((107 / 3200 : ℝ) - Real.pi * Real.exp (53 / 400 : ℝ)) ≤
      (2 / (174633601903 / 5000000000 : ℝ) : ℝ) := by
    rw [show (107 / 3200 : ℝ) - Real.pi * Real.exp (53 / 400 : ℝ) =
      -(Real.pi * Real.exp (53 / 400 : ℝ) - (107 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4488971215088087 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4488971215088087 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell106_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 800 : ℝ) (107 / 1600 : ℝ)) :
    (8530398491 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4311635183 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell106_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell106_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell107_leftExp :
    (11431070071 / 10000000000 : ℝ) ≤ Real.exp (107 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (107 / 800 : ℝ) (62761777161 / 62500000000 : ℝ)
    (11431070071 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell107_rightExp :
    Real.exp (27 / 200 : ℝ) ≤ (2861341961 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (27 / 200 : ℝ) (502113830727 / 500000000000 : ℝ)
    (2861341961 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell107_denomUpper :
    Real.exp (8905578125283873 / 2500000000000000 : ℝ) ≤ (88104356569 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8905578125283873 / 2500000000000000 : ℝ) (111775222481 /
    100000000000 : ℝ) (88104356569 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell107_denomLower :
    (175363987261 / 5000000000 : ℝ) ≤ Real.exp (4446782285811629 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4446782285811629 / 1250000000000000 : ℝ) (139698048151 /
    125000000000 : ℝ) (175363987261 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell107_product_lower :
    (4488969785811629 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (107 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell107_leftExp
    (by norm_num : (0 : ℝ) ≤ (11431070071 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell107_product_upper :
    Real.pi * Real.exp (27 / 200 : ℝ) ≤ (8989171875283873 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell107_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell107_endpointLower :
    (852373297 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (107 / 1600 : ℝ) (27 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4488969785811629 / 1250000000000000 : ℝ) (Real.pi * Real.exp (107 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell107_product_lower
  have hD : Real.exp (Real.pi * Real.exp (27 / 200 : ℝ) - (107 / 3200 : ℝ)) ≤
      (88104356569 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell107_denomUpper
    linarith [hpThetaJensenCell107_product_upper]
  have hi : (1 / (88104356569 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (27 / 200 : ℝ) - (107 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (88104356569 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (88104356569 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((107 / 3200 : ℝ) - Real.pi * Real.exp (27 / 200 : ℝ)) := by
    rw [show (107 / 3200 : ℝ) - Real.pi * Real.exp (27 / 200 : ℝ) =
      -(Real.pi * Real.exp (27 / 200 : ℝ) - (107 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (107 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (107 / 800 : ℝ)) := by
    have h := hpThetaJensenCell107_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (88104356569 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell107_endpointUpper :
    hpThetaJensenKernelEndpointUpper (107 / 1600 : ℝ) (27 / 400 : ℝ) ≤ (8616564049 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (27 / 200 : ℝ)) (8989171875283873 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (27 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell107_product_upper
  have hD : (175363987261 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (107 / 800 : ℝ) - (27 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell107_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell107_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (107 / 800 : ℝ) - (27 / 800 : ℝ)) ≤
      (1 / (175363987261 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (175363987261 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((27 / 800 : ℝ) - Real.pi * Real.exp (107 / 800 : ℝ)) ≤
      (2 / (175363987261 / 5000000000 : ℝ) : ℝ) := by
    rw [show (27 / 800 : ℝ) - Real.pi * Real.exp (107 / 800 : ℝ) =
      -(Real.pi * Real.exp (107 / 800 : ℝ) - (27 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (8989171875283873 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (8989171875283873 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell107_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (107 / 1600 : ℝ) (27 / 400 : ℝ)) :
    (852373297 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8616564049 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell107_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell107_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell108_leftExp :
    (11445367843 / 10000000000 : ℝ) ≤ Real.exp (27 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (27 / 200 : ℝ) (1004227661453 / 1000000000000 : ℝ)
    (11445367843 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell108_rightExp :
    Real.exp (109 / 800 : ℝ) ≤ (11459683499 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (109 / 800 : ℝ) (1004266889863 / 1000000000000 : ℝ)
    (11459683499 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell108_denomUpper :
    Real.exp (35664161462673907 / 10000000000000000 : ℝ) ≤ (176947673463 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35664161462673907 / 10000000000000000 : ℝ) (44715936471
    / 40000000000 : ℝ) (176947673463 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell108_denomLower :
    (352196830983 / 10000000000 : ℝ) ≤ Real.exp (4452006381578257 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4452006381578257 / 1250000000000000 : ℝ) (69858147121 /
    62500000000 : ℝ) (352196830983 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell108_product_lower :
    (4494584506578257 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (27 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell108_leftExp
    (by norm_num : (0 : ℝ) ≤ (11445367843 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell108_product_upper :
    Real.pi * Real.exp (109 / 800 : ℝ) ≤ (36001661462673907 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell108_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell108_endpointLower :
    (1703401683 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 400 : ℝ) (109 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4494584506578257 / 1250000000000000 : ℝ) (Real.pi * Real.exp (27 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell108_product_lower
  have hD : Real.exp (Real.pi * Real.exp (109 / 800 : ℝ) - (27 / 800 : ℝ)) ≤
      (176947673463 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell108_denomUpper
    linarith [hpThetaJensenCell108_product_upper]
  have hi : (1 / (176947673463 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (109 / 800 : ℝ) - (27 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (176947673463 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (176947673463 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((27 / 800 : ℝ) - Real.pi * Real.exp (109 / 800 : ℝ)) := by
    rw [show (27 / 800 : ℝ) - Real.pi * Real.exp (109 / 800 : ℝ) =
      -(Real.pi * Real.exp (109 / 800 : ℝ) - (27 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (27 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (27 / 200 : ℝ)) := by
    have h := hpThetaJensenCell108_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (176947673463 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell108_endpointUpper :
    hpThetaJensenKernelEndpointUpper (27 / 400 : ℝ) (109 / 1600 : ℝ) ≤ (17219596229 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (109 / 800 : ℝ)) (36001661462673907 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (109 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell108_product_upper
  have hD : (352196830983 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (27 / 200 : ℝ) - (109 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell108_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell108_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (27 / 200 : ℝ) - (109 / 3200 : ℝ)) ≤
      (1 / (352196830983 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (352196830983 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((109 / 3200 : ℝ) - Real.pi * Real.exp (27 / 200 : ℝ)) ≤
      (2 / (352196830983 / 10000000000 : ℝ) : ℝ) := by
    rw [show (109 / 3200 : ℝ) - Real.pi * Real.exp (27 / 200 : ℝ) =
      -(Real.pi * Real.exp (27 / 200 : ℝ) - (109 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36001661462673907 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36001661462673907 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell108_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (27 / 400 : ℝ) (109 / 1600 : ℝ)) :
    (1703401683 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17219596229 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell108_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell108_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell109_leftExp :
    (5729841749 / 5000000000 : ℝ) ≤ Real.exp (109 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (109 / 800 : ℝ) (502133444931 / 500000000000 : ℝ)
    (5729841749 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell109_rightExp :
    Real.exp (11 / 80 : ℝ) ≤ (573700853 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 80 : ℝ) (251076529951 / 250000000000 : ℝ)
    (573700853 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell109_denomUpper :
    Real.exp (1785303333878829 / 500000000000000 : ℝ) ≤ (355381464613 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (1785303333878829 / 500000000000000 : ℝ) (559022407201 /
    500000000000 : ℝ) (355381464613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell109_denomLower :
    (176836913009 / 5000000000 : ℝ) ≤ Real.exp (2228618749990551 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2228618749990551 / 625000000000000 : ℝ) (111787653799 /
    100000000000 : ℝ) (176836913009 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell109_product_lower :
    (2250103124990551 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (109 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell109_leftExp
    (by norm_num : (0 : ℝ) ≤ (5729841749 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell109_product_upper :
    Real.pi * Real.exp (11 / 80 : ℝ) ≤ (1802334583878829 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell109_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell109_endpointLower :
    (8510224961 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (109 / 1600 : ℝ) (11 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2250103124990551 / 625000000000000 : ℝ) (Real.pi * Real.exp (109 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell109_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 80 : ℝ) - (109 / 3200 : ℝ)) ≤
      (355381464613 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell109_denomUpper
    linarith [hpThetaJensenCell109_product_upper]
  have hi : (1 / (355381464613 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 80 : ℝ) - (109 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (355381464613 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (355381464613 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((109 / 3200 : ℝ) - Real.pi * Real.exp (11 / 80 : ℝ)) := by
    rw [show (109 / 3200 : ℝ) - Real.pi * Real.exp (11 / 80 : ℝ) =
      -(Real.pi * Real.exp (11 / 80 : ℝ) - (109 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (109 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (109 / 800 : ℝ)) := by
    have h := hpThetaJensenCell109_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (355381464613 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell109_endpointUpper :
    hpThetaJensenKernelEndpointUpper (109 / 1600 : ℝ) (11 / 160 : ℝ) ≤ (3441189081 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 80 : ℝ)) (1802334583878829 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell109_product_upper
  have hD : (176836913009 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (109 / 800 : ℝ) - (11 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell109_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell109_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (109 / 800 : ℝ) - (11 / 320 : ℝ)) ≤
      (1 / (176836913009 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (176836913009 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 320 : ℝ) - Real.pi * Real.exp (109 / 800 : ℝ)) ≤
      (2 / (176836913009 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 320 : ℝ) - Real.pi * Real.exp (109 / 800 : ℝ) =
      -(Real.pi * Real.exp (109 / 800 : ℝ) - (11 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (1802334583878829 / 500000000000000 : ℝ) ^ 2 - 6 *
      (1802334583878829 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell109_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (109 / 1600 : ℝ) (11 / 160 : ℝ)) :
    (8510224961 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3441189081 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell109_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell109_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell110_leftExp :
    (11474017059 / 10000000000 : ℝ) ≤ Real.exp (11 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 80 : ℝ) (1004306119803 / 1000000000000 : ℝ)
    (11474017059 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell110_rightExp :
    Real.exp (111 / 800 : ℝ) ≤ (11488368549 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (111 / 800 : ℝ) (502172675639 / 500000000000 : ℝ)
    (11488368549 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell110_denomUpper :
    Real.exp (35748028214958557 / 10000000000000000 : ℝ) ≤ (71375166597 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35748028214958557 / 10000000000000000 : ℝ)
    (1118191433013 / 1000000000000 : ℝ) (71375166597 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell110_denomLower :
    (355159012957 / 10000000000 : ℝ) ≤ Real.exp (4462475650052241 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4462475650052241 / 1250000000000000 : ℝ) (559011468851 /
    500000000000 : ℝ) (355159012957 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell110_product_lower :
    (4505835025052241 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell110_leftExp
    (by norm_num : (0 : ℝ) ≤ (11474017059 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell110_product_upper :
    Real.pi * Real.exp (111 / 800 : ℝ) ≤ (36091778214958557 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell110_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell110_endpointLower :
    (8503382749 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 160 : ℝ) (111 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4505835025052241 / 1250000000000000 : ℝ) (Real.pi * Real.exp (11 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell110_product_lower
  have hD : Real.exp (Real.pi * Real.exp (111 / 800 : ℝ) - (11 / 320 : ℝ)) ≤
      (71375166597 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell110_denomUpper
    linarith [hpThetaJensenCell110_product_upper]
  have hi : (1 / (71375166597 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (111 / 800 : ℝ) - (11 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71375166597 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71375166597 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 320 : ℝ) - Real.pi * Real.exp (111 / 800 : ℝ)) := by
    rw [show (11 / 320 : ℝ) - Real.pi * Real.exp (111 / 800 : ℝ) =
      -(Real.pi * Real.exp (111 / 800 : ℝ) - (11 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 80 : ℝ)) := by
    have h := hpThetaJensenCell110_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71375166597 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell110_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 160 : ℝ) (111 / 1600 : ℝ) ≤ (17192175899 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (111 / 800 : ℝ)) (36091778214958557 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (111 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell110_product_upper
  have hD : (355159012957 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 80 : ℝ) - (111 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell110_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell110_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 80 : ℝ) - (111 / 3200 : ℝ)) ≤
      (1 / (355159012957 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (355159012957 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((111 / 3200 : ℝ) - Real.pi * Real.exp (11 / 80 : ℝ)) ≤
      (2 / (355159012957 / 10000000000 : ℝ) : ℝ) := by
    rw [show (111 / 3200 : ℝ) - Real.pi * Real.exp (11 / 80 : ℝ) =
      -(Real.pi * Real.exp (11 / 80 : ℝ) - (111 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36091778214958557 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36091778214958557 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell110_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 160 : ℝ) (111 / 1600 : ℝ)) :
    (8503382749 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17192175899 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell110_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell110_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell111_leftExp :
    (2872092137 / 2500000000 : ℝ) ≤ Real.exp (111 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (111 / 800 : ℝ) (1004345351277 / 1000000000000 : ℝ)
    (2872092137 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell111_rightExp :
    Real.exp (7 / 50 : ℝ) ≤ (11502737989 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 50 : ℝ) (200876916857 / 200000000000 : ℝ)
    (11502737989 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell111_denomUpper :
    Real.exp (35790046147076477 / 10000000000000000 : ℝ) ≤ (179189253091 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35790046147076477 / 10000000000000000 : ℝ)
    (1118338267939 / 1000000000000 : ℝ) (179189253091 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell111_denomLower :
    (71330489083 / 2000000000 : ℝ) ≤ Real.exp (1116930210107763 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1116930210107763 / 312500000000000 : ℝ) (559084776697 /
    500000000000 : ℝ) (71330489083 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell111_product_lower :
    (1127867710107763 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (111 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell111_leftExp
    (by norm_num : (0 : ℝ) ≤ (2872092137 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell111_product_upper :
    Real.pi * Real.exp (7 / 50 : ℝ) ≤ (36136921147076477 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell111_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell111_endpointLower :
    (3398592767 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (111 / 1600 : ℝ) (7 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1127867710107763 / 312500000000000 : ℝ) (Real.pi * Real.exp (111 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell111_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 50 : ℝ) - (111 / 3200 : ℝ)) ≤
      (179189253091 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell111_denomUpper
    linarith [hpThetaJensenCell111_product_upper]
  have hi : (1 / (179189253091 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 50 : ℝ) - (111 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (179189253091 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (179189253091 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((111 / 3200 : ℝ) - Real.pi * Real.exp (7 / 50 : ℝ)) := by
    rw [show (111 / 3200 : ℝ) - Real.pi * Real.exp (7 / 50 : ℝ) =
      -(Real.pi * Real.exp (7 / 50 : ℝ) - (111 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (111 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (111 / 800 : ℝ)) := by
    have h := hpThetaJensenCell111_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (179189253091 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell111_endpointUpper :
    hpThetaJensenKernelEndpointUpper (111 / 1600 : ℝ) (7 / 100 : ℝ) ≤ (8589143999 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 50 : ℝ)) (36136921147076477 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell111_product_upper
  have hD : (71330489083 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (111 / 800 : ℝ) - (7 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell111_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell111_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (111 / 800 : ℝ) - (7 / 200 : ℝ)) ≤
      (1 / (71330489083 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (71330489083 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 200 : ℝ) - Real.pi * Real.exp (111 / 800 : ℝ)) ≤
      (2 / (71330489083 / 2000000000 : ℝ) : ℝ) := by
    rw [show (7 / 200 : ℝ) - Real.pi * Real.exp (111 / 800 : ℝ) =
      -(Real.pi * Real.exp (111 / 800 : ℝ) - (7 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36136921147076477 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36136921147076477 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell111_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (111 / 1600 : ℝ) (7 / 100 : ℝ)) :
    (3398592767 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8589143999 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell111_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell111_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell112_leftExp :
    (2875684497 / 2500000000 : ℝ) ≤ Real.exp (7 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 50 : ℝ) (251096146071 / 250000000000 : ℝ)
    (2875684497 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell112_rightExp :
    Real.exp (113 / 800 : ℝ) ≤ (5758562701 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (113 / 800 : ℝ) (125552977353 / 125000000000 : ℝ)
    (5758562701 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell112_denomUpper :
    Real.exp (17916060271522693 / 5000000000000000 : ℝ) ≤ (179944769333 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17916060271522693 / 5000000000000000 : ℝ) (69905332469 /
    62500000000 : ℝ) (179944769333 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell112_denomLower :
    (179077088749 / 5000000000 : ℝ) ≤ Real.exp (1118243270037403 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1118243270037403 / 312500000000000 : ℝ) (1118316385397 /
    1000000000000 : ℝ) (179077088749 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell112_product_lower :
    (1129278426287403 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell112_leftExp
    (by norm_num : (0 : ℝ) ≤ (2875684497 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell112_product_upper :
    Real.pi * Real.exp (113 / 800 : ℝ) ≤ (18091060271522693 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell112_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell112_endpointLower :
    (16979045217 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 100 : ℝ) (113 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1129278426287403 / 312500000000000 : ℝ) (Real.pi * Real.exp (7 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell112_product_lower
  have hD : Real.exp (Real.pi * Real.exp (113 / 800 : ℝ) - (7 / 200 : ℝ)) ≤
      (179944769333 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell112_denomUpper
    linarith [hpThetaJensenCell112_product_upper]
  have hi : (1 / (179944769333 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (113 / 800 : ℝ) - (7 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (179944769333 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (179944769333 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 200 : ℝ) - Real.pi * Real.exp (113 / 800 : ℝ)) := by
    rw [show (7 / 200 : ℝ) - Real.pi * Real.exp (113 / 800 : ℝ) =
      -(Real.pi * Real.exp (113 / 800 : ℝ) - (7 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 50 : ℝ)) := by
    have h := hpThetaJensenCell112_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (179944769333 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell112_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 100 : ℝ) (113 / 1600 : ℝ) ≤ (8582140989 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (113 / 800 : ℝ)) (18091060271522693 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (113 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell112_product_upper
  have hD : (179077088749 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 50 : ℝ) - (113 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell112_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell112_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 50 : ℝ) - (113 / 3200 : ℝ)) ≤
      (1 / (179077088749 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (179077088749 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((113 / 3200 : ℝ) - Real.pi * Real.exp (7 / 50 : ℝ)) ≤
      (2 / (179077088749 / 5000000000 : ℝ) : ℝ) := by
    rw [show (113 / 3200 : ℝ) - Real.pi * Real.exp (7 / 50 : ℝ) =
      -(Real.pi * Real.exp (7 / 50 : ℝ) - (113 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18091060271522693 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (18091060271522693 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell112_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 100 : ℝ) (113 / 1600 : ℝ)) :
    (16979045217 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8582140989 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell112_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell112_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell113_leftExp :
    (11517125401 / 10000000000 : ℝ) ≤ Real.exp (113 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (113 / 800 : ℝ) (1004423818823 / 1000000000000 : ℝ)
    (11517125401 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell113_rightExp :
    Real.exp (57 / 400 : ℝ) ≤ (1153153081 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 400 : ℝ) (62778940931 / 62500000000 : ℝ)
    (1153153081 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell113_denomUpper :
    Real.exp (3587425147198033 / 1000000000000000 : ℝ) ≤ (18070449263 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3587425147198033 / 1000000000000000 : ℝ) (279658147007 /
    250000000000 : ℝ) (18070449263 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell113_denomLower :
    (359664263623 / 10000000000 : ℝ) ≤ Real.exp (4478232377847299 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4478232377847299 / 1250000000000000 : ℝ) (559231717017 /
    500000000000 : ℝ) (359664263623 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell113_product_lower :
    (4522763627847299 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (113 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell113_leftExp
    (by norm_num : (0 : ℝ) ≤ (11517125401 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell113_product_upper :
    Real.pi * Real.exp (57 / 400 : ℝ) ≤ (3622737647198033 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell113_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell113_endpointLower :
    (1696500993 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (113 / 1600 : ℝ) (57 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4522763627847299 / 1250000000000000 : ℝ) (Real.pi * Real.exp (113 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell113_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 400 : ℝ) - (113 / 3200 : ℝ)) ≤
      (18070449263 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell113_denomUpper
    linarith [hpThetaJensenCell113_product_upper]
  have hi : (1 / (18070449263 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 400 : ℝ) - (113 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18070449263 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18070449263 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((113 / 3200 : ℝ) - Real.pi * Real.exp (57 / 400 : ℝ)) := by
    rw [show (113 / 3200 : ℝ) - Real.pi * Real.exp (57 / 400 : ℝ) =
      -(Real.pi * Real.exp (57 / 400 : ℝ) - (113 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (113 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (113 / 800 : ℝ)) := by
    have h := hpThetaJensenCell113_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18070449263 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell113_endpointUpper :
    hpThetaJensenKernelEndpointUpper (113 / 1600 : ℝ) (57 / 800 : ℝ) ≤ (27440253 / 16000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 400 : ℝ)) (3622737647198033 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell113_product_upper
  have hD : (359664263623 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (113 / 800 : ℝ) - (57 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell113_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell113_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (113 / 800 : ℝ) - (57 / 1600 : ℝ)) ≤
      (1 / (359664263623 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (359664263623 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 1600 : ℝ) - Real.pi * Real.exp (113 / 800 : ℝ)) ≤
      (2 / (359664263623 / 10000000000 : ℝ) : ℝ) := by
    rw [show (57 / 1600 : ℝ) - Real.pi * Real.exp (113 / 800 : ℝ) =
      -(Real.pi * Real.exp (113 / 800 : ℝ) - (57 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3622737647198033 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3622737647198033 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell113_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (113 / 1600 : ℝ) (57 / 800 : ℝ)) :
    (1696500993 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (27440253 / 16000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell113_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell113_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell114_leftExp :
    (11531530809 / 10000000000 : ℝ) ≤ Real.exp (57 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 400 : ℝ) (200892610979 / 200000000000 : ℝ)
    (11531530809 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell114_rightExp :
    Real.exp (23 / 160 : ℝ) ≤ (2886488559 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 160 : ℝ) (401800917 / 400000000 : ℝ)
    (2886488559 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell114_denomUpper :
    Real.exp (8979109751534487 / 2500000000000000 : ℝ) ≤ (181468450667 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8979109751534487 / 2500000000000000 : ℝ) (223756014769 /
    200000000000 : ℝ) (181468450667 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell114_denomLower :
    (361182758589 / 10000000000 : ℝ) ≤ Real.exp (4483498742163491 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4483498742163491 / 1250000000000000 : ℝ) (559305349813 /
    500000000000 : ℝ) (361182758589 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell114_product_lower :
    (4528420617163491 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell114_leftExp
    (by norm_num : (0 : ℝ) ≤ (11531530809 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell114_product_upper :
    Real.pi * Real.exp (23 / 160 : ℝ) ≤ (9068172251534487 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell114_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell114_endpointLower :
    (8475429127 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 800 : ℝ) (23 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4528420617163491 / 1250000000000000 : ℝ) (Real.pi * Real.exp (57 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell114_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 160 : ℝ) - (57 / 1600 : ℝ)) ≤
      (181468450667 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell114_denomUpper
    linarith [hpThetaJensenCell114_product_upper]
  have hi : (1 / (181468450667 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 160 : ℝ) - (57 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (181468450667 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (181468450667 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 1600 : ℝ) - Real.pi * Real.exp (23 / 160 : ℝ)) := by
    rw [show (57 / 1600 : ℝ) - Real.pi * Real.exp (23 / 160 : ℝ) =
      -(Real.pi * Real.exp (23 / 160 : ℝ) - (57 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 400 : ℝ)) := by
    have h := hpThetaJensenCell114_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (181468450667 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell114_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 800 : ℝ) (23 / 320 : ℝ) ≤ (17135916729 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 160 : ℝ)) (9068172251534487 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell114_product_upper
  have hD : (361182758589 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 400 : ℝ) - (23 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell114_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell114_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 400 : ℝ) - (23 / 640 : ℝ)) ≤
      (1 / (361182758589 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (361182758589 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 640 : ℝ) - Real.pi * Real.exp (57 / 400 : ℝ)) ≤
      (2 / (361182758589 / 10000000000 : ℝ) : ℝ) := by
    rw [show (23 / 640 : ℝ) - Real.pi * Real.exp (57 / 400 : ℝ) =
      -(Real.pi * Real.exp (57 / 400 : ℝ) - (23 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9068172251534487 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9068172251534487 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell114_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 800 : ℝ) (23 / 320 : ℝ)) :
    (8475429127 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17135916729 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell114_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell114_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell115_leftExp :
    (2309190847 / 2000000000 : ℝ) ≤ Real.exp (23 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 160 : ℝ) (1004502292499 / 1000000000000 : ℝ)
    (2309190847 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell115_rightExp :
    Real.exp (29 / 200 : ℝ) ≤ (11560395703 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (29 / 200 : ℝ) (1004541531637 / 1000000000000 : ℝ)
    (11560395703 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell115_denomUpper :
    Real.exp (35958683217774879 / 10000000000000000 : ℝ) ≤ (364473342657 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (35958683217774879 / 10000000000000000 : ℝ) (139865972161
    / 125000000000 : ℝ) (364473342657 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell115_denomLower :
    (362709717733 / 10000000000 : ℝ) ≤ Real.exp (897754436426053 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (897754436426053 / 250000000000000 : ℝ) (1118758182507 /
    1000000000000 : ℝ) (362709717733 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell115_product_lower :
    (906816936426053 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell115_leftExp
    (by norm_num : (0 : ℝ) ≤ (2309190847 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell115_product_upper :
    Real.pi * Real.exp (29 / 200 : ℝ) ≤ (36318058217774879 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell115_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell115_endpointLower :
    (16936590477 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 320 : ℝ) (29 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (906816936426053 / 250000000000000 : ℝ) (Real.pi * Real.exp (23 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell115_product_lower
  have hD : Real.exp (Real.pi * Real.exp (29 / 200 : ℝ) - (23 / 640 : ℝ)) ≤
      (364473342657 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell115_denomUpper
    linarith [hpThetaJensenCell115_product_upper]
  have hi : (1 / (364473342657 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (29 / 200 : ℝ) - (23 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (364473342657 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (364473342657 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 640 : ℝ) - Real.pi * Real.exp (29 / 200 : ℝ)) := by
    rw [show (23 / 640 : ℝ) - Real.pi * Real.exp (29 / 200 : ℝ) =
      -(Real.pi * Real.exp (29 / 200 : ℝ) - (23 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 160 : ℝ)) := by
    have h := hpThetaJensenCell115_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (364473342657 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell115_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 320 : ℝ) (29 / 400 : ℝ) ≤ (8560779039 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (29 / 200 : ℝ)) (36318058217774879 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (29 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell115_product_upper
  have hD : (362709717733 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 160 : ℝ) - (29 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell115_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell115_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 160 : ℝ) - (29 / 800 : ℝ)) ≤
      (1 / (362709717733 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (362709717733 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((29 / 800 : ℝ) - Real.pi * Real.exp (23 / 160 : ℝ)) ≤
      (2 / (362709717733 / 10000000000 : ℝ) : ℝ) := by
    rw [show (29 / 800 : ℝ) - Real.pi * Real.exp (23 / 160 : ℝ) =
      -(Real.pi * Real.exp (23 / 160 : ℝ) - (29 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36318058217774879 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36318058217774879 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell115_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 320 : ℝ) (29 / 400 : ℝ)) :
    (16936590477 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8560779039 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell115_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell115_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell116_leftExp :
    (5780197851 / 5000000000 : ℝ) ≤ Real.exp (29 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (29 / 200 : ℝ) (251135382909 / 250000000000 : ℝ)
    (5780197851 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell116_rightExp :
    Real.exp (117 / 800 : ℝ) ≤ (11574855233 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (117 / 800 : ℝ) (1004580772307 / 1000000000000 : ℝ)
    (11574855233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell116_denomUpper :
    Real.exp (36000984176006169 / 10000000000000000 : ℝ) ≤ (91504591329 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36000984176006169 / 10000000000000000 : ℝ)
    (1119075698681 / 1000000000000 : ℝ) (91504591329 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell116_denomLower :
    (364245196787 / 10000000000 : ℝ) ≤ Real.exp (2247026353389849 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2247026353389849 / 625000000000000 : ℝ) (111890588301 /
    100000000000 : ℝ) (364245196787 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell116_product_lower :
    (2269877915889849 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (29 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell116_leftExp
    (by norm_num : (0 : ℝ) ≤ (5780197851 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell116_product_upper :
    Real.pi * Real.exp (117 / 800 : ℝ) ≤ (36363484176006169 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell116_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell116_endpointLower :
    (1692220689 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 400 : ℝ) (117 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2269877915889849 / 625000000000000 : ℝ) (Real.pi * Real.exp (29 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell116_product_lower
  have hD : Real.exp (Real.pi * Real.exp (117 / 800 : ℝ) - (29 / 800 : ℝ)) ≤
      (91504591329 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell116_denomUpper
    linarith [hpThetaJensenCell116_product_upper]
  have hi : (1 / (91504591329 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (117 / 800 : ℝ) - (29 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (91504591329 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (91504591329 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((29 / 800 : ℝ) - Real.pi * Real.exp (117 / 800 : ℝ)) := by
    rw [show (29 / 800 : ℝ) - Real.pi * Real.exp (117 / 800 : ℝ) =
      -(Real.pi * Real.exp (117 / 800 : ℝ) - (29 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (29 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (29 / 200 : ℝ)) := by
    have h := hpThetaJensenCell116_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (91504591329 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell116_endpointUpper :
    hpThetaJensenKernelEndpointUpper (29 / 400 : ℝ) (117 / 1600 : ℝ) ≤ (17107082457 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (117 / 800 : ℝ)) (36363484176006169 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (117 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell116_product_upper
  have hD : (364245196787 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (29 / 200 : ℝ) - (117 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell116_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell116_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (29 / 200 : ℝ) - (117 / 3200 : ℝ)) ≤
      (1 / (364245196787 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (364245196787 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((117 / 3200 : ℝ) - Real.pi * Real.exp (29 / 200 : ℝ)) ≤
      (2 / (364245196787 / 10000000000 : ℝ) : ℝ) := by
    rw [show (117 / 3200 : ℝ) - Real.pi * Real.exp (29 / 200 : ℝ) =
      -(Real.pi * Real.exp (29 / 200 : ℝ) - (117 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36363484176006169 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36363484176006169 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell116_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (29 / 400 : ℝ) (117 / 1600 : ℝ)) :
    (1692220689 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17107082457 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell116_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell116_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell117_leftExp :
    (180857113 / 156250000 : ℝ) ≤ Real.exp (117 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (117 / 800 : ℝ) (502290386153 / 500000000000 : ℝ)
    (180857113 / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell117_rightExp :
    Real.exp (59 / 400 : ℝ) ≤ (11589332849 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (59 / 400 : ℝ) (100462001451 / 100000000000 : ℝ)
    (11589332849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell117_denomUpper :
    Real.exp (36043341953088457 / 10000000000000000 : ℝ) ≤ (183786012953 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36043341953088457 / 10000000000000000 : ℝ)
    (1119223838357 / 1000000000000 : ℝ) (183786012953 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell117_denomLower :
    (182894625897 / 5000000000 : ℝ) ≤ Real.exp (70302192574237 / 19531250000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (70302192574237 / 19531250000000 : ℝ) (559526900729 /
    500000000000 : ℝ) (182894625897 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell117_product_lower :
    (71022407417987 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (117 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell117_leftExp
    (by norm_num : (0 : ℝ) ≤ (180857113 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell117_product_upper :
    Real.pi * Real.exp (59 / 400 : ℝ) ≤ (36408966953088457 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell117_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell117_endpointLower :
    (16907707783 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (117 / 1600 : ℝ) (59 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (71022407417987 / 19531250000000 : ℝ) (Real.pi * Real.exp (117 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell117_product_lower
  have hD : Real.exp (Real.pi * Real.exp (59 / 400 : ℝ) - (117 / 3200 : ℝ)) ≤
      (183786012953 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell117_denomUpper
    linarith [hpThetaJensenCell117_product_upper]
  have hi : (1 / (183786012953 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (59 / 400 : ℝ) - (117 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (183786012953 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (183786012953 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((117 / 3200 : ℝ) - Real.pi * Real.exp (59 / 400 : ℝ)) := by
    rw [show (117 / 3200 : ℝ) - Real.pi * Real.exp (59 / 400 : ℝ) =
      -(Real.pi * Real.exp (59 / 400 : ℝ) - (117 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (117 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (117 / 800 : ℝ)) := by
    have h := hpThetaJensenCell117_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (183786012953 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell117_endpointUpper :
    hpThetaJensenKernelEndpointUpper (117 / 1600 : ℝ) (59 / 800 : ℝ) ≤ (17092490163 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (59 / 400 : ℝ)) (36408966953088457 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (59 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell117_product_upper
  have hD : (182894625897 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (117 / 800 : ℝ) - (59 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell117_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell117_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (117 / 800 : ℝ) - (59 / 1600 : ℝ)) ≤
      (1 / (182894625897 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (182894625897 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((59 / 1600 : ℝ) - Real.pi * Real.exp (117 / 800 : ℝ)) ≤
      (2 / (182894625897 / 5000000000 : ℝ) : ℝ) := by
    rw [show (59 / 1600 : ℝ) - Real.pi * Real.exp (117 / 800 : ℝ) =
      -(Real.pi * Real.exp (117 / 800 : ℝ) - (59 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36408966953088457 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36408966953088457 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell117_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (117 / 1600 : ℝ) (59 / 800 : ℝ)) :
    (16907707783 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17092490163 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell117_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell117_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell118_leftExp :
    (11589332847 / 10000000000 : ℝ) ≤ Real.exp (59 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (59 / 400 : ℝ) (1004620014509 / 1000000000000 : ℝ)
    (11589332847 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell118_rightExp :
    Real.exp (119 / 800 : ℝ) ≤ (11603828573 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (119 / 800 : ℝ) (502329629123 / 500000000000 : ℝ)
    (11603828573 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell118_denomUpper :
    Real.exp (36085756618136789 / 10000000000000000 : ℝ) ≤ (369134381343 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (36085756618136789 / 10000000000000000 : ℝ) (6996076229 /
    6250000000 : ℝ) (369134381343 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell118_denomLower :
    (367341939207 / 10000000000 : ℝ) ≤ Real.exp (4504635044684053 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4504635044684053 / 1250000000000000 : ℝ) (559600969087 /
    500000000000 : ℝ) (367341939207 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell118_product_lower :
    (4551119419684053 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (59 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell118_leftExp
    (by norm_num : (0 : ℝ) ≤ (11589332847 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell118_product_upper :
    Real.pi * Real.exp (119 / 800 : ℝ) ≤ (36454506618136789 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell118_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell118_endpointLower :
    (16893093447 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 800 : ℝ) (119 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4551119419684053 / 1250000000000000 : ℝ) (Real.pi * Real.exp (59 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell118_product_lower
  have hD : Real.exp (Real.pi * Real.exp (119 / 800 : ℝ) - (59 / 1600 : ℝ)) ≤
      (369134381343 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell118_denomUpper
    linarith [hpThetaJensenCell118_product_upper]
  have hi : (1 / (369134381343 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (119 / 800 : ℝ) - (59 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (369134381343 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (369134381343 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((59 / 1600 : ℝ) - Real.pi * Real.exp (119 / 800 : ℝ)) := by
    rw [show (59 / 1600 : ℝ) - Real.pi * Real.exp (119 / 800 : ℝ) =
      -(Real.pi * Real.exp (119 / 800 : ℝ) - (59 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (59 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (59 / 400 : ℝ)) := by
    have h := hpThetaJensenCell118_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (369134381343 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell118_endpointUpper :
    hpThetaJensenKernelEndpointUpper (59 / 800 : ℝ) (119 / 1600 : ℝ) ≤ (17077781491 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (119 / 800 : ℝ)) (36454506618136789 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (119 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell118_product_upper
  have hD : (367341939207 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (59 / 400 : ℝ) - (119 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell118_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell118_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (59 / 400 : ℝ) - (119 / 3200 : ℝ)) ≤
      (1 / (367341939207 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (367341939207 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((119 / 3200 : ℝ) - Real.pi * Real.exp (59 / 400 : ℝ)) ≤
      (2 / (367341939207 / 10000000000 : ℝ) : ℝ) := by
    rw [show (119 / 3200 : ℝ) - Real.pi * Real.exp (59 / 400 : ℝ) =
      -(Real.pi * Real.exp (59 / 400 : ℝ) - (119 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (36454506618136789 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (36454506618136789 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell118_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (59 / 800 : ℝ) (119 / 1600 : ℝ)) :
    (16893093447 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (17077781491 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell118_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell118_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell119_leftExp :
    (2900957143 / 2500000000 : ℝ) ≤ Real.exp (119 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (119 / 800 : ℝ) (200931851649 / 200000000000 : ℝ)
    (2900957143 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell119_rightExp :
    Real.exp (3 / 20 : ℝ) ≤ (2904585607 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3 / 20 : ℝ) (200939700703 / 200000000000 : ℝ)
    (2904585607 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell119_denomUpper :
    Real.exp (9032057060851951 / 2500000000000000 : ℝ) ≤ (23169093067 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9032057060851951 / 2500000000000000 : ℝ) (139940096733 /
    125000000000 : ℝ) (23169093067 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell119_denomLower :
    (184451658117 / 5000000000 : ℝ) ≤ Real.exp (1127484219098957 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1127484219098957 / 312500000000000 : ℝ) (1119350293513 /
    1000000000000 : ℝ) (184451658117 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell119_product_lower :
    (1139202969098957 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (119 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell119_leftExp
    (by norm_num : (0 : ℝ) ≤ (2900957143 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell119_product_upper :
    Real.pi * Real.exp (3 / 20 : ℝ) ≤ (9125025810851951 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell119_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell119_endpointLower :
    (16878364187 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (119 / 1600 : ℝ) (3 / 40 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1139202969098957 / 312500000000000 : ℝ) (Real.pi * Real.exp (119 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell119_product_lower
  have hD : Real.exp (Real.pi * Real.exp (3 / 20 : ℝ) - (119 / 3200 : ℝ)) ≤
      (23169093067 / 625000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell119_denomUpper
    linarith [hpThetaJensenCell119_product_upper]
  have hi : (1 / (23169093067 / 625000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (3 / 20 : ℝ) - (119 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (23169093067 / 625000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (23169093067 / 625000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((119 / 3200 : ℝ) - Real.pi * Real.exp (3 / 20 : ℝ)) := by
    rw [show (119 / 3200 : ℝ) - Real.pi * Real.exp (3 / 20 : ℝ) =
      -(Real.pi * Real.exp (3 / 20 : ℝ) - (119 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (119 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (119 / 800 : ℝ)) := by
    have h := hpThetaJensenCell119_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (23169093067 / 625000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell119_endpointUpper :
    hpThetaJensenKernelEndpointUpper (119 / 1600 : ℝ) (3 / 40 : ℝ) ≤ (8531478363 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (3 / 20 : ℝ)) (9125025810851951 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (3 / 40 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell119_product_upper
  have hD : (184451658117 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (119 / 800 : ℝ) - (3 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell119_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell119_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (119 / 800 : ℝ) - (3 / 80 : ℝ)) ≤
      (1 / (184451658117 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (184451658117 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((3 / 80 : ℝ) - Real.pi * Real.exp (119 / 800 : ℝ)) ≤
      (2 / (184451658117 / 5000000000 : ℝ) : ℝ) := by
    rw [show (3 / 80 : ℝ) - Real.pi * Real.exp (119 / 800 : ℝ) =
      -(Real.pi * Real.exp (119 / 800 : ℝ) - (3 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9125025810851951 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9125025810851951 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell119_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (119 / 1600 : ℝ) (3 / 40 : ℝ)) :
    (16878364187 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8531478363 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell119_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell119_endpointUpper

def hpThetaJensenCellsBatch005Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4284572137 / 2500000000 : ℝ)
  | 1 => (4281417903 / 2500000000 : ℝ)
  | 2 => (17112934997 / 10000000000 : ℝ)
  | 3 => (2137509869 / 1250000000 : ℝ)
  | 4 => (8543551879 / 5000000000 : ℝ)
  | 5 => (682960387 / 400000000 : ℝ)
  | 6 => (8530398491 / 5000000000 : ℝ)
  | 7 => (852373297 / 500000000 : ℝ)
  | 8 => (1703401683 / 1000000000 : ℝ)
  | 9 => (8510224961 / 5000000000 : ℝ)
  | 10 => (8503382749 / 5000000000 : ℝ)
  | 11 => (3398592767 / 2000000000 : ℝ)
  | 12 => (16979045217 / 10000000000 : ℝ)
  | 13 => (1696500993 / 1000000000 : ℝ)
  | 14 => (8475429127 / 5000000000 : ℝ)
  | 15 => (16936590477 / 10000000000 : ℝ)
  | 16 => (1692220689 / 1000000000 : ℝ)
  | 17 => (16907707783 / 10000000000 : ℝ)
  | 18 => (16893093447 / 10000000000 : ℝ)
  | 19 => (16878364187 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch005Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8662248677 / 5000000000 : ℝ)
  | 1 => (17311805831 / 10000000000 : ℝ)
  | 2 => (345979869 / 200000000 : ℝ)
  | 3 => (17286060487 / 10000000000 : ℝ)
  | 4 => (17273007197 / 10000000000 : ℝ)
  | 5 => (17259833859 / 10000000000 : ℝ)
  | 6 => (4311635183 / 2500000000 : ℝ)
  | 7 => (8616564049 / 5000000000 : ℝ)
  | 8 => (17219596229 / 10000000000 : ℝ)
  | 9 => (3441189081 / 2000000000 : ℝ)
  | 10 => (17192175899 / 10000000000 : ℝ)
  | 11 => (8589143999 / 5000000000 : ℝ)
  | 12 => (8582140989 / 5000000000 : ℝ)
  | 13 => (27440253 / 16000000 : ℝ)
  | 14 => (17135916729 / 10000000000 : ℝ)
  | 15 => (8560779039 / 5000000000 : ℝ)
  | 16 => (17107082457 / 10000000000 : ℝ)
  | 17 => (17092490163 / 10000000000 : ℝ)
  | 18 => (17077781491 / 10000000000 : ℝ)
  | 19 => (8531478363 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch005_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch005Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch005Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell100_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell101_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell102_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell103_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell104_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell105_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell106_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell107_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell108_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell109_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell110_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell111_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell112_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell113_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell114_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell115_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell116_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell117_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell118_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell119_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper] at h ⊢
    exact h

end HodgeProofHP
