import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell960_leftExp :
    (16600584613 / 5000000000 : ℝ) ≤ Real.exp (6 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6 / 5 : ℝ) (1038211997081 / 1000000000000 : ℝ)
    (16600584613 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell960_rightExp :
    Real.exp (961 / 800 : ℝ) ≤ (103883427 / 31250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (961 / 800 : ℝ) (1038252553031 / 1000000000000 : ℝ)
    (103883427 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell960_denomUpper :
    Real.exp (316984447079211 / 31250000000000 : ℝ) ≤ (254253581297901 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (316984447079211 / 31250000000000 : ℝ) (343245304473 /
    250000000000 : ℝ) (254253581297901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell960_denomLower :
    (25087883088681 / 1000000000 : ℝ) ≤ Real.exp (6331337664440487 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6331337664440487 / 625000000000000 : ℝ) (1372408030237 /
    1000000000000 : ℝ) (25087883088681 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell960_product_lower :
    (6519032976940487 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (6 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell960_leftExp
    (by norm_num : (0 : ℝ) ≤ (16600584613 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell960_product_upper :
    Real.pi * Real.exp (961 / 800 : ℝ) ≤ (326359447079211 / 31250000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell960_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell960_endpointLower :
    (146544509 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 5 : ℝ) (961 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6519032976940487 / 625000000000000 : ℝ) (Real.pi * Real.exp (6 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell960_product_lower
  have hD : Real.exp (Real.pi * Real.exp (961 / 800 : ℝ) - (3 / 10 : ℝ)) ≤
      (254253581297901 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell960_denomUpper
    linarith [hpThetaJensenCell960_product_upper]
  have hi : (1 / (254253581297901 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (961 / 800 : ℝ) - (3 / 10 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (254253581297901 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (254253581297901 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((3 / 10 : ℝ) - Real.pi * Real.exp (961 / 800 : ℝ)) := by
    rw [show (3 / 10 : ℝ) - Real.pi * Real.exp (961 / 800 : ℝ) =
      -(Real.pi * Real.exp (961 / 800 : ℝ) - (3 / 10 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (6 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (6 / 5 : ℝ)) := by
    have h := hpThetaJensenCell960_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (254253581297901 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell960_endpointUpper :
    hpThetaJensenKernelEndpointUpper (3 / 5 : ℝ) (961 / 1600 : ℝ) ≤ (298622127 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (961 / 800 : ℝ)) (326359447079211 / 31250000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (961 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell960_product_upper
  have hD : (25087883088681 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (6 / 5 : ℝ) - (961 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell960_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell960_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (6 / 5 : ℝ) - (961 / 3200 : ℝ)) ≤
      (1 / (25087883088681 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (25087883088681 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((961 / 3200 : ℝ) - Real.pi * Real.exp (6 / 5 : ℝ)) ≤
      (2 / (25087883088681 / 1000000000 : ℝ) : ℝ) := by
    rw [show (961 / 3200 : ℝ) - Real.pi * Real.exp (6 / 5 : ℝ) =
      -(Real.pi * Real.exp (6 / 5 : ℝ) - (961 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (326359447079211 / 31250000000000 : ℝ) ^ 2 - 6 *
      (326359447079211 / 31250000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell960_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (3 / 5 : ℝ) (961 / 1600 : ℝ)) :
    (146544509 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (298622127 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell960_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell960_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell961_leftExp :
    (16621348319 / 5000000000 : ℝ) ≤ Real.exp (961 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (961 / 800 : ℝ) (103825255303 / 100000000000 : ℝ)
    (16621348319 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell961_rightExp :
    Real.exp (481 / 400 : ℝ) ≤ (4160534499 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (481 / 400 : ℝ) (1038293110563 / 1000000000000 : ℝ)
    (4160534499 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell961_denomUpper :
    Real.exp (12695315433316907 / 1250000000000000 : ℝ) ≤ (257516078947677 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (12695315433316907 / 1250000000000000 : ℝ) (686764187907
    / 500000000000 : ℝ) (257516078947677 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell961_denomLower :
    (127046938806403 / 5000000000 : ℝ) ≤ Real.exp (6339296238522981 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6339296238522981 / 625000000000000 : ℝ) (1372954259459 /
    1000000000000 : ℝ) (127046938806403 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell961_product_lower :
    (6527186863522981 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (961 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell961_leftExp
    (by norm_num : (0 : ℝ) ≤ (16621348319 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell961_product_upper :
    Real.pi * Real.exp (481 / 400 : ℝ) ≤ (13070706058316907 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell961_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell961_endpointLower :
    (145080529 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (961 / 1600 : ℝ) (481 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6527186863522981 / 625000000000000 : ℝ) (Real.pi * Real.exp (961 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell961_product_lower
  have hD : Real.exp (Real.pi * Real.exp (481 / 400 : ℝ) - (961 / 3200 : ℝ)) ≤
      (257516078947677 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell961_denomUpper
    linarith [hpThetaJensenCell961_product_upper]
  have hi : (1 / (257516078947677 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (481 / 400 : ℝ) - (961 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (257516078947677 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (257516078947677 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((961 / 3200 : ℝ) - Real.pi * Real.exp (481 / 400 : ℝ)) := by
    rw [show (961 / 3200 : ℝ) - Real.pi * Real.exp (481 / 400 : ℝ) =
      -(Real.pi * Real.exp (481 / 400 : ℝ) - (961 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (961 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (961 / 800 : ℝ)) := by
    have h := hpThetaJensenCell961_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (257516078947677 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell961_endpointUpper :
    hpThetaJensenKernelEndpointUpper (961 / 1600 : ℝ) (481 / 800 : ℝ) ≤ (147821813 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (481 / 400 : ℝ)) (13070706058316907 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (481 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell961_product_upper
  have hD : (127046938806403 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (961 / 800 : ℝ) - (481 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell961_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell961_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (961 / 800 : ℝ) - (481 / 1600 : ℝ)) ≤
      (1 / (127046938806403 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (127046938806403 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((481 / 1600 : ℝ) - Real.pi * Real.exp (961 / 800 : ℝ)) ≤
      (2 / (127046938806403 / 5000000000 : ℝ) : ℝ) := by
    rw [show (481 / 1600 : ℝ) - Real.pi * Real.exp (961 / 800 : ℝ) =
      -(Real.pi * Real.exp (961 / 800 : ℝ) - (481 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13070706058316907 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13070706058316907 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell961_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (961 / 1600 : ℝ) (481 / 800 : ℝ)) :
    (145080529 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (147821813 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell961_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell961_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell962_leftExp :
    (3328427599 / 1000000000 : ℝ) ≤ Real.exp (481 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (481 / 400 : ℝ) (519146555281 / 500000000000 : ℝ)
    (3328427599 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell962_rightExp :
    Real.exp (963 / 800 : ℝ) ≤ (33325907351 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (963 / 800 : ℝ) (12979170871 / 12500000000 : ℝ)
    (33325907351 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell962_denomUpper :
    Real.exp (101690187252550143 / 10000000000000000 : ℝ) ≤ (260824701337773 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (101690187252550143 / 10000000000000000 : ℝ)
    (687038226681 / 500000000000 : ℝ) (260824701337773 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell962_denomLower :
    (257354324933131 / 10000000000 : ℝ) ≤ Real.exp (1269453002199701 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1269453002199701 / 125000000000000 : ℝ) (68675070323 /
    50000000000 : ℝ) (257354324933131 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell962_product_lower :
    (1307070189699701 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (481 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell962_leftExp
    (by norm_num : (0 : ℝ) ≤ (3328427599 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell962_product_upper :
    Real.pi * Real.exp (963 / 800 : ℝ) ≤ (104696437252550143 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell962_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell962_endpointLower :
    (287257567 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (481 / 800 : ℝ) (963 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1307070189699701 / 125000000000000 : ℝ) (Real.pi * Real.exp (481 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell962_product_lower
  have hD : Real.exp (Real.pi * Real.exp (963 / 800 : ℝ) - (481 / 1600 : ℝ)) ≤
      (260824701337773 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell962_denomUpper
    linarith [hpThetaJensenCell962_product_upper]
  have hi : (1 / (260824701337773 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (963 / 800 : ℝ) - (481 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (260824701337773 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (260824701337773 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((481 / 1600 : ℝ) - Real.pi * Real.exp (963 / 800 : ℝ)) := by
    rw [show (481 / 1600 : ℝ) - Real.pi * Real.exp (963 / 800 : ℝ) =
      -(Real.pi * Real.exp (963 / 800 : ℝ) - (481 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (481 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (481 / 400 : ℝ)) := by
    have h := hpThetaJensenCell962_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (260824701337773 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell962_endpointUpper :
    hpThetaJensenKernelEndpointUpper (481 / 800 : ℝ) (963 / 1600 : ℝ) ≤ (292689967 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (963 / 800 : ℝ)) (104696437252550143 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (963 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell962_product_upper
  have hD : (257354324933131 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (481 / 400 : ℝ) - (963 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell962_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell962_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (481 / 400 : ℝ) - (963 / 3200 : ℝ)) ≤
      (1 / (257354324933131 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (257354324933131 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((963 / 3200 : ℝ) - Real.pi * Real.exp (481 / 400 : ℝ)) ≤
      (2 / (257354324933131 / 10000000000 : ℝ) : ℝ) := by
    rw [show (963 / 3200 : ℝ) - Real.pi * Real.exp (481 / 400 : ℝ) =
      -(Real.pi * Real.exp (481 / 400 : ℝ) - (963 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (104696437252550143 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (104696437252550143 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell962_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (481 / 800 : ℝ) (963 / 1600 : ℝ)) :
    (287257567 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (292689967 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell962_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell962_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell963_leftExp :
    (33325907349 / 10000000000 : ℝ) ≤ Real.exp (963 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (963 / 800 : ℝ) (1038333669679 / 1000000000000 : ℝ)
    (33325907349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell963_rightExp :
    Real.exp (241 / 200 : ℝ) ≤ (16683795391 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (241 / 200 : ℝ) (1038374230381 / 1000000000000 : ℝ)
    (16683795391 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell963_denomUpper :
    Real.exp (50909007313797863 / 5000000000000000 : ℝ) ≤ (10567206211317 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (50909007313797863 / 5000000000000000 : ℝ) (687312726169
    / 500000000000 : ℝ) (10567206211317 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell963_denomLower :
    (130330433991629 / 5000000000 : ℝ) ≤ Real.exp (12710487990044951 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12710487990044951 / 1250000000000000 : ℝ) (1374049473067
    / 1000000000000 : ℝ) (130330433991629 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell963_product_lower :
    (13087050490044951 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (963 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell963_leftExp
    (by norm_num : (0 : ℝ) ≤ (33325907349 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell963_product_upper :
    Real.pi * Real.exp (241 / 200 : ℝ) ≤ (52413694813797863 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell963_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell963_endpointLower :
    (28437839 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (963 / 1600 : ℝ) (241 / 400 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13087050490044951 / 1250000000000000 : ℝ) (Real.pi * Real.exp (963 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell963_product_lower
  have hD : Real.exp (Real.pi * Real.exp (241 / 200 : ℝ) - (963 / 3200 : ℝ)) ≤
      (10567206211317 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell963_denomUpper
    linarith [hpThetaJensenCell963_product_upper]
  have hi : (1 / (10567206211317 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (241 / 200 : ℝ) - (963 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10567206211317 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (10567206211317 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((963 / 3200 : ℝ) - Real.pi * Real.exp (241 / 200 : ℝ)) := by
    rw [show (963 / 3200 : ℝ) - Real.pi * Real.exp (241 / 200 : ℝ) =
      -(Real.pi * Real.exp (241 / 200 : ℝ) - (963 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (963 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (963 / 800 : ℝ)) := by
    have h := hpThetaJensenCell963_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (10567206211317 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell963_endpointUpper :
    hpThetaJensenKernelEndpointUpper (963 / 1600 : ℝ) (241 / 400 : ℝ) ≤ (57952199 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (241 / 200 : ℝ)) (52413694813797863 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (241 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell963_product_upper
  have hD : (130330433991629 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (963 / 800 : ℝ) - (241 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell963_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell963_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (963 / 800 : ℝ) - (241 / 800 : ℝ)) ≤
      (1 / (130330433991629 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (130330433991629 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((241 / 800 : ℝ) - Real.pi * Real.exp (963 / 800 : ℝ)) ≤
      (2 / (130330433991629 / 5000000000 : ℝ) : ℝ) := by
    rw [show (241 / 800 : ℝ) - Real.pi * Real.exp (963 / 800 : ℝ) =
      -(Real.pi * Real.exp (963 / 800 : ℝ) - (241 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (52413694813797863 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (52413694813797863 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell963_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (963 / 1600 : ℝ) (241 / 400 : ℝ)) :
    (28437839 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (57952199 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell963_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell963_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell964_leftExp :
    (1668379539 / 500000000 : ℝ) ≤ Real.exp (241 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (241 / 200 : ℝ) (51918711519 / 50000000000 : ℝ)
    (1668379539 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell964_rightExp :
    Real.exp (193 / 160 : ℝ) ≤ (668186527 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (193 / 160 : ℝ) (1038414792667 / 1000000000000 : ℝ)
    (668186527 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell964_denomUpper :
    Real.exp (2038920115917511 / 200000000000000 : ℝ) ≤ (267583159220717 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2038920115917511 / 200000000000000 : ℝ) (27503507491 /
    20000000000 : ℝ) (267583159220717 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell964_denomLower :
    (264014213145477 / 10000000000 : ℝ) ≤ Real.exp (636323320335761 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (636323320335761 / 62500000000000 : ℝ) (343649615271 /
    250000000000 : ℝ) (264014213145477 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell964_product_lower :
    (655170976585761 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (241 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell964_leftExp
    (by norm_num : (0 : ℝ) ≤ (1668379539 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell964_product_upper :
    Real.pi * Real.exp (193 / 160 : ℝ) ≤ (2099170115917511 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell964_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell964_endpointLower :
    (2252187 / 80000000 : ℝ) ≤ hpThetaTraceEndpointLower (241 / 400 : ℝ) (193 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (655170976585761 / 62500000000000 : ℝ) (Real.pi * Real.exp (241 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell964_product_lower
  have hD : Real.exp (Real.pi * Real.exp (193 / 160 : ℝ) - (241 / 800 : ℝ)) ≤
      (267583159220717 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell964_denomUpper
    linarith [hpThetaJensenCell964_product_upper]
  have hi : (1 / (267583159220717 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (193 / 160 : ℝ) - (241 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (267583159220717 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (267583159220717 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((241 / 800 : ℝ) - Real.pi * Real.exp (193 / 160 : ℝ)) := by
    rw [show (241 / 800 : ℝ) - Real.pi * Real.exp (193 / 160 : ℝ) =
      -(Real.pi * Real.exp (193 / 160 : ℝ) - (241 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (241 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (241 / 200 : ℝ)) := by
    have h := hpThetaJensenCell964_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (267583159220717 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell964_endpointUpper :
    hpThetaJensenKernelEndpointUpper (241 / 400 : ℝ) (193 / 320 : ℝ) ≤ (286856553 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (193 / 160 : ℝ)) (2099170115917511 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (193 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell964_product_upper
  have hD : (264014213145477 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (241 / 200 : ℝ) - (193 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell964_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell964_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (241 / 200 : ℝ) - (193 / 640 : ℝ)) ≤
      (1 / (264014213145477 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (264014213145477 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((193 / 640 : ℝ) - Real.pi * Real.exp (241 / 200 : ℝ)) ≤
      (2 / (264014213145477 / 10000000000 : ℝ) : ℝ) := by
    rw [show (193 / 640 : ℝ) - Real.pi * Real.exp (241 / 200 : ℝ) =
      -(Real.pi * Real.exp (241 / 200 : ℝ) - (193 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2099170115917511 / 200000000000000 : ℝ) ^ 2 - 6 *
      (2099170115917511 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell964_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (241 / 400 : ℝ) (193 / 320 : ℝ)) :
    (2252187 / 80000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (286856553 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell964_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell964_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell965_leftExp :
    (8352331587 / 2500000000 : ℝ) ≤ Real.exp (193 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (193 / 160 : ℝ) (519207396333 / 500000000000 : ℝ)
    (8352331587 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell965_rightExp :
    Real.exp (483 / 400 : ℝ) ≤ (836277853 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (483 / 400 : ℝ) (1038455356537 / 1000000000000 : ℝ)
    (836277853 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell965_denomUpper :
    Real.exp (2551854024039829 / 250000000000000 : ℝ) ≤ (271034443389853 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2551854024039829 / 250000000000000 : ℝ) (85982888863 /
    62500000000 : ℝ) (271034443389853 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell965_denomLower :
    (267415078405781 / 10000000000 : ℝ) ≤ Real.exp (3185616324383313 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3185616324383313 / 312500000000000 : ℝ) (1375148372319 /
    1000000000000 : ℝ) (267415078405781 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell965_product_lower :
    (3279952261883313 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (193 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell965_leftExp
    (by norm_num : (0 : ℝ) ≤ (8352331587 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell965_product_upper :
    Real.pi * Real.exp (483 / 400 : ℝ) ≤ (2627244649039829 / 250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell965_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell965_endpointLower :
    (278692367 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (193 / 320 : ℝ) (483 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3279952261883313 / 312500000000000 : ℝ) (Real.pi * Real.exp (193 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell965_product_lower
  have hD : Real.exp (Real.pi * Real.exp (483 / 400 : ℝ) - (193 / 640 : ℝ)) ≤
      (271034443389853 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell965_denomUpper
    linarith [hpThetaJensenCell965_product_upper]
  have hi : (1 / (271034443389853 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (483 / 400 : ℝ) - (193 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (271034443389853 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (271034443389853 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((193 / 640 : ℝ) - Real.pi * Real.exp (483 / 400 : ℝ)) := by
    rw [show (193 / 640 : ℝ) - Real.pi * Real.exp (483 / 400 : ℝ) =
      -(Real.pi * Real.exp (483 / 400 : ℝ) - (193 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (193 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (193 / 160 : ℝ)) := by
    have h := hpThetaJensenCell965_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (271034443389853 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell965_endpointUpper :
    hpThetaJensenKernelEndpointUpper (193 / 320 : ℝ) (483 / 800 : ℝ) ≤ (283976487 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (483 / 400 : ℝ)) (2627244649039829 / 250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (483 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell965_product_upper
  have hD : (267415078405781 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (193 / 160 : ℝ) - (483 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell965_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell965_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (193 / 160 : ℝ) - (483 / 1600 : ℝ)) ≤
      (1 / (267415078405781 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (267415078405781 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((483 / 1600 : ℝ) - Real.pi * Real.exp (193 / 160 : ℝ)) ≤
      (2 / (267415078405781 / 10000000000 : ℝ) : ℝ) := by
    rw [show (483 / 1600 : ℝ) - Real.pi * Real.exp (193 / 160 : ℝ) =
      -(Real.pi * Real.exp (193 / 160 : ℝ) - (483 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2627244649039829 / 250000000000000 : ℝ) ^ 2 - 6 *
      (2627244649039829 / 250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell965_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (193 / 320 : ℝ) (483 / 800 : ℝ)) :
    (278692367 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (283976487 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell965_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell965_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell966_leftExp :
    (16725557059 / 5000000000 : ℝ) ≤ Real.exp (483 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (483 / 400 : ℝ) (129806919567 / 125000000000 : ℝ)
    (16725557059 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell966_rightExp :
    Real.exp (967 / 800 : ℝ) ≤ (8373238539 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (967 / 800 : ℝ) (1038495921991 / 1000000000000 : ℝ)
    (8373238539 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell966_denomUpper :
    Real.exp (25550620081452627 / 2500000000000000 : ℝ) ≤ (274534749959241 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (25550620081452627 / 2500000000000000 : ℝ) (172034749489
    / 125000000000 : ℝ) (274534749959241 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell966_denomLower :
    (8464506048049 / 312500000 : ℝ) ≤ Real.exp (6379242344012241 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6379242344012241 / 625000000000000 : ℝ) (1375699208581 /
    1000000000000 : ℝ) (8464506048049 / 312500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell966_product_lower :
    (6568109531512241 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (483 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell966_leftExp
    (by norm_num : (0 : ℝ) ≤ (16725557059 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell966_product_upper :
    Real.pi * Real.exp (967 / 800 : ℝ) ≤ (26305307581452627 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell966_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell966_endpointLower :
    (137942607 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (483 / 800 : ℝ) (967 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6568109531512241 / 625000000000000 : ℝ) (Real.pi * Real.exp (483 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell966_product_lower
  have hD : Real.exp (Real.pi * Real.exp (967 / 800 : ℝ) - (483 / 1600 : ℝ)) ≤
      (274534749959241 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell966_denomUpper
    linarith [hpThetaJensenCell966_product_upper]
  have hi : (1 / (274534749959241 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (967 / 800 : ℝ) - (483 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (274534749959241 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (274534749959241 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((483 / 1600 : ℝ) - Real.pi * Real.exp (967 / 800 : ℝ)) := by
    rw [show (483 / 1600 : ℝ) - Real.pi * Real.exp (967 / 800 : ℝ) =
      -(Real.pi * Real.exp (967 / 800 : ℝ) - (483 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (483 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (483 / 400 : ℝ)) := by
    have h := hpThetaJensenCell966_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (274534749959241 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell966_endpointUpper :
    hpThetaJensenKernelEndpointUpper (483 / 800 : ℝ) (967 / 1600 : ℝ) ≤ (281120641 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (967 / 800 : ℝ)) (26305307581452627 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (967 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell966_product_upper
  have hD : (8464506048049 / 312500000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (483 / 400 : ℝ) - (967 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell966_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell966_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (483 / 400 : ℝ) - (967 / 3200 : ℝ)) ≤
      (1 / (8464506048049 / 312500000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (8464506048049 / 312500000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((967 / 3200 : ℝ) - Real.pi * Real.exp (483 / 400 : ℝ)) ≤
      (2 / (8464506048049 / 312500000 : ℝ) : ℝ) := by
    rw [show (967 / 3200 : ℝ) - Real.pi * Real.exp (483 / 400 : ℝ) =
      -(Real.pi * Real.exp (483 / 400 : ℝ) - (967 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26305307581452627 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (26305307581452627 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell966_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (483 / 800 : ℝ) (967 / 1600 : ℝ)) :
    (137942607 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (281120641 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell966_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell966_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell967_leftExp :
    (16746477077 / 5000000000 : ℝ) ≤ Real.exp (967 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (967 / 800 : ℝ) (103849592199 / 100000000000 : ℝ)
    (16746477077 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell967_rightExp :
    Real.exp (121 / 100 : ℝ) ≤ (33534846527 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (121 / 100 : ℝ) (1038536489031 / 1000000000000 : ℝ)
    (33534846527 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell967_denomUpper :
    Real.exp (102330964105297511 / 10000000000000000 : ℝ) ≤ (3476060422033 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (102330964105297511 / 10000000000000000 : ℝ)
    (688415349367 / 500000000000 : ℝ) (3476060422033 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell967_denomLower :
    (17147643765587 / 625000000 : ℝ) ≤ Real.exp (6387262301660823 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6387262301660823 / 625000000000000 : ℝ) (1376250971671 /
    1000000000000 : ℝ) (17147643765587 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell967_product_lower :
    (6576324801660823 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (967 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell967_leftExp
    (by norm_num : (0 : ℝ) ≤ (16746477077 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell967_product_upper :
    Real.pi * Real.exp (121 / 100 : ℝ) ≤ (105352839105297511 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell967_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell967_endpointLower :
    (273101763 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (967 / 1600 : ℝ) (121 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6576324801660823 / 625000000000000 : ℝ) (Real.pi * Real.exp (967 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell967_product_lower
  have hD : Real.exp (Real.pi * Real.exp (121 / 100 : ℝ) - (967 / 3200 : ℝ)) ≤
      (3476060422033 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell967_denomUpper
    linarith [hpThetaJensenCell967_product_upper]
  have hi : (1 / (3476060422033 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (121 / 100 : ℝ) - (967 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (3476060422033 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (3476060422033 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((967 / 3200 : ℝ) - Real.pi * Real.exp (121 / 100 : ℝ)) := by
    rw [show (967 / 3200 : ℝ) - Real.pi * Real.exp (121 / 100 : ℝ) =
      -(Real.pi * Real.exp (121 / 100 : ℝ) - (967 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (967 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (967 / 800 : ℝ)) := by
    have h := hpThetaJensenCell967_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (3476060422033 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell967_endpointUpper :
    hpThetaJensenKernelEndpointUpper (967 / 1600 : ℝ) (121 / 200 : ℝ) ≤ (278288861 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (121 / 100 : ℝ)) (105352839105297511 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (121 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell967_product_upper
  have hD : (17147643765587 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (967 / 800 : ℝ) - (121 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell967_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell967_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (967 / 800 : ℝ) - (121 / 400 : ℝ)) ≤
      (1 / (17147643765587 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (17147643765587 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((121 / 400 : ℝ) - Real.pi * Real.exp (967 / 800 : ℝ)) ≤
      (2 / (17147643765587 / 625000000 : ℝ) : ℝ) := by
    rw [show (121 / 400 : ℝ) - Real.pi * Real.exp (967 / 800 : ℝ) =
      -(Real.pi * Real.exp (967 / 800 : ℝ) - (121 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (105352839105297511 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (105352839105297511 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell967_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (967 / 1600 : ℝ) (121 / 200 : ℝ)) :
    (273101763 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (278288861 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell967_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell967_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell968_leftExp :
    (1341393861 / 400000000 : ℝ) ≤ Real.exp (121 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (121 / 100 : ℝ) (103853648903 / 100000000000 : ℝ)
    (1341393861 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell968_rightExp :
    Real.exp (969 / 800 : ℝ) ≤ (6715358259 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (969 / 800 : ℝ) (207715411531 / 200000000000 : ℝ)
    (6715358259 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell968_denomUpper :
    Real.exp (20491922498966587 / 2000000000000000 : ℝ) ≤ (140842730726931 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (20491922498966587 / 2000000000000000 : ℝ) (344346083013
    / 250000000000 : ℝ) (140842730726931 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell968_denomLower :
    (138955076447053 / 5000000000 : ℝ) ≤ Real.exp (511623402820839 / 50000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (511623402820839 / 50000000000000 : ℝ) (68840183173 /
    50000000000 : ℝ) (138955076447053 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell968_product_lower :
    (526764027820839 / 50000000000000 : ℝ) ≤ Real.pi * Real.exp (121 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell968_leftExp
    (by norm_num : (0 : ℝ) ≤ (1341393861 / 400000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell968_product_upper :
    Real.pi * Real.exp (969 / 800 : ℝ) ≤ (21096922498966587 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell968_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell968_endpointLower :
    (270341863 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (121 / 200 : ℝ) (969 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (526764027820839 / 50000000000000 : ℝ) (Real.pi * Real.exp (121 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell968_product_lower
  have hD : Real.exp (Real.pi * Real.exp (969 / 800 : ℝ) - (121 / 400 : ℝ)) ≤
      (140842730726931 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell968_denomUpper
    linarith [hpThetaJensenCell968_product_upper]
  have hi : (1 / (140842730726931 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (969 / 800 : ℝ) - (121 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (140842730726931 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (140842730726931 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((121 / 400 : ℝ) - Real.pi * Real.exp (969 / 800 : ℝ)) := by
    rw [show (121 / 400 : ℝ) - Real.pi * Real.exp (969 / 800 : ℝ) =
      -(Real.pi * Real.exp (969 / 800 : ℝ) - (121 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (121 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (121 / 100 : ℝ)) := by
    have h := hpThetaJensenCell968_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (140842730726931 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell968_endpointUpper :
    hpThetaJensenKernelEndpointUpper (121 / 200 : ℝ) (969 / 1600 : ℝ) ≤ (137740497 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (969 / 800 : ℝ)) (21096922498966587 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (969 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell968_product_upper
  have hD : (138955076447053 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (121 / 100 : ℝ) - (969 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell968_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell968_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (121 / 100 : ℝ) - (969 / 3200 : ℝ)) ≤
      (1 / (138955076447053 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (138955076447053 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((969 / 3200 : ℝ) - Real.pi * Real.exp (121 / 100 : ℝ)) ≤
      (2 / (138955076447053 / 5000000000 : ℝ) : ℝ) := by
    rw [show (969 / 3200 : ℝ) - Real.pi * Real.exp (121 / 100 : ℝ) =
      -(Real.pi * Real.exp (121 / 100 : ℝ) - (969 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (21096922498966587 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (21096922498966587 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell968_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (121 / 200 : ℝ) (969 / 1600 : ℝ)) :
    (270341863 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (137740497 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell968_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell968_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell969_leftExp :
    (33576791293 / 10000000000 : ℝ) ≤ Real.exp (969 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (969 / 800 : ℝ) (519288528827 / 500000000000 : ℝ)
    (33576791293 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell969_rightExp :
    Real.exp (97 / 80 : ℝ) ≤ (16809394263 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (97 / 80 : ℝ) (1038617627863 / 1000000000000 : ℝ)
    (16809394263 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell969_denomUpper :
    Real.exp (51294212850880959 / 5000000000000000 : ℝ) ≤ (285337412692429 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (51294212850880959 / 5000000000000000 : ℝ) (688969448851
    / 500000000000 : ℝ) (285337412692429 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell969_denomLower :
    (281508517643397 / 10000000000 : ℝ) ≤ Real.exp (12806666113969807 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12806666113969807 / 1250000000000000 : ℝ) (688678642863
    / 500000000000 : ℝ) (281508517643397 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell969_product_lower :
    (13185572363969807 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (969 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell969_leftExp
    (by norm_num : (0 : ℝ) ≤ (33576791293 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell969_product_upper :
    Real.pi * Real.exp (97 / 80 : ℝ) ≤ (52808275350880959 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell969_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell969_endpointLower :
    (133802681 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (969 / 1600 : ℝ) (97 / 160 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13185572363969807 / 1250000000000000 : ℝ) (Real.pi * Real.exp (969 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell969_product_lower
  have hD : Real.exp (Real.pi * Real.exp (97 / 80 : ℝ) - (969 / 3200 : ℝ)) ≤
      (285337412692429 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell969_denomUpper
    linarith [hpThetaJensenCell969_product_upper]
  have hi : (1 / (285337412692429 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (97 / 80 : ℝ) - (969 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (285337412692429 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (285337412692429 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((969 / 3200 : ℝ) - Real.pi * Real.exp (97 / 80 : ℝ)) := by
    rw [show (969 / 3200 : ℝ) - Real.pi * Real.exp (97 / 80 : ℝ) =
      -(Real.pi * Real.exp (97 / 80 : ℝ) - (969 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (969 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (969 / 800 : ℝ)) := by
    have h := hpThetaJensenCell969_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (285337412692429 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell969_endpointUpper :
    hpThetaJensenKernelEndpointUpper (969 / 1600 : ℝ) (97 / 160 : ℝ) ≤ (136348443 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (97 / 80 : ℝ)) (52808275350880959 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (97 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell969_product_upper
  have hD : (281508517643397 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (969 / 800 : ℝ) - (97 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell969_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell969_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (969 / 800 : ℝ) - (97 / 320 : ℝ)) ≤
      (1 / (281508517643397 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (281508517643397 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((97 / 320 : ℝ) - Real.pi * Real.exp (969 / 800 : ℝ)) ≤
      (2 / (281508517643397 / 10000000000 : ℝ) : ℝ) := by
    rw [show (97 / 320 : ℝ) - Real.pi * Real.exp (969 / 800 : ℝ) =
      -(Real.pi * Real.exp (969 / 800 : ℝ) - (97 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (52808275350880959 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (52808275350880959 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell969_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (969 / 1600 : ℝ) (97 / 160 : ℝ)) :
    (133802681 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (136348443 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell969_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell969_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell970_leftExp :
    (8404697131 / 2500000000 : ℝ) ≤ Real.exp (97 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (97 / 80 : ℝ) (519308813931 / 500000000000 : ℝ)
    (8404697131 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell970_rightExp :
    Real.exp (971 / 800 : ℝ) ≤ (2103802393 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (971 / 800 : ℝ) (1038658199657 / 1000000000000 : ℝ)
    (2103802393 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell970_denomUpper :
    Real.exp (6419837746232049 / 625000000000000 : ℝ) ≤ (72260370054991 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6419837746232049 / 625000000000000 : ℝ) (1378494397553 /
    1000000000000 : ℝ) (72260370054991 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell970_denomLower :
    (57031634734623 / 2000000000 : ℝ) ≤ Real.exp (3205691939896569 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3205691939896569 / 312500000000000 : ℝ) (688955920153 /
    500000000000 : ℝ) (57031634734623 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell970_product_lower :
    (3300516158646569 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (97 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell970_leftExp
    (by norm_num : (0 : ℝ) ≤ (8404697131 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell970_product_upper :
    Real.pi * Real.exp (971 / 800 : ℝ) ≤ (6609290871232049 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell970_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell970_endpointLower :
    (264892109 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 160 : ℝ) (971 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3300516158646569 / 312500000000000 : ℝ) (Real.pi * Real.exp (97 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell970_product_lower
  have hD : Real.exp (Real.pi * Real.exp (971 / 800 : ℝ) - (97 / 320 : ℝ)) ≤
      (72260370054991 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell970_denomUpper
    linarith [hpThetaJensenCell970_product_upper]
  have hi : (1 / (72260370054991 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (971 / 800 : ℝ) - (97 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (72260370054991 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (72260370054991 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((97 / 320 : ℝ) - Real.pi * Real.exp (971 / 800 : ℝ)) := by
    rw [show (97 / 320 : ℝ) - Real.pi * Real.exp (971 / 800 : ℝ) =
      -(Real.pi * Real.exp (971 / 800 : ℝ) - (97 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (97 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (97 / 80 : ℝ)) := by
    have h := hpThetaJensenCell970_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (72260370054991 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell970_endpointUpper :
    hpThetaJensenKernelEndpointUpper (97 / 160 : ℝ) (971 / 1600 : ℝ) ≤ (1054439 / 39062500 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (971 / 800 : ℝ)) (6609290871232049 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (971 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell970_product_upper
  have hD : (57031634734623 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (97 / 80 : ℝ) - (971 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell970_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell970_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (97 / 80 : ℝ) - (971 / 3200 : ℝ)) ≤
      (1 / (57031634734623 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57031634734623 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((971 / 3200 : ℝ) - Real.pi * Real.exp (97 / 80 : ℝ)) ≤
      (2 / (57031634734623 / 2000000000 : ℝ) : ℝ) := by
    rw [show (971 / 3200 : ℝ) - Real.pi * Real.exp (97 / 80 : ℝ) =
      -(Real.pi * Real.exp (97 / 80 : ℝ) - (971 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6609290871232049 / 625000000000000 : ℝ) ^ 2 - 6 *
      (6609290871232049 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell970_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (97 / 160 : ℝ) (971 / 1600 : ℝ)) :
    (264892109 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1054439 / 39062500 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell970_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell970_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell971_leftExp :
    (16830419143 / 5000000000 : ℝ) ≤ Real.exp (971 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (971 / 800 : ℝ) (129832274957 / 125000000000 : ℝ)
    (16830419143 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell971_rightExp :
    Real.exp (243 / 200 : ℝ) ≤ (8425735161 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (243 / 200 : ℝ) (207739754607 / 200000000000 : ℝ)
    (8425735161 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell971_denomUpper :
    Real.exp (25711636851651473 / 2500000000000000 : ℝ) ≤ (29279846941939 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (25711636851651473 / 2500000000000000 : ℝ) (1379050833407
    / 1000000000000 : ℝ) (29279846941939 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell971_denomLower :
    (288859913219919 / 10000000000 : ℝ) ≤ Real.exp (6419445017036957 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6419445017036957 / 625000000000000 : ℝ) (344616832267 /
    250000000000 : ℝ) (288859913219919 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell971_product_lower :
    (6609288767036957 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (971 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell971_leftExp
    (by norm_num : (0 : ℝ) ≤ (16830419143 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell971_product_upper :
    Real.pi * Real.exp (243 / 200 : ℝ) ≤ (26470230601651473 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell971_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell971_endpointLower :
    (131100977 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (971 / 1600 : ℝ) (243 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6609288767036957 / 625000000000000 : ℝ) (Real.pi * Real.exp (971 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell971_product_lower
  have hD : Real.exp (Real.pi * Real.exp (243 / 200 : ℝ) - (971 / 3200 : ℝ)) ≤
      (29279846941939 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell971_denomUpper
    linarith [hpThetaJensenCell971_product_upper]
  have hi : (1 / (29279846941939 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (243 / 200 : ℝ) - (971 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29279846941939 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29279846941939 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((971 / 3200 : ℝ) - Real.pi * Real.exp (243 / 200 : ℝ)) := by
    rw [show (971 / 3200 : ℝ) - Real.pi * Real.exp (243 / 200 : ℝ) =
      -(Real.pi * Real.exp (243 / 200 : ℝ) - (971 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (971 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (971 / 800 : ℝ)) := by
    have h := hpThetaJensenCell971_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29279846941939 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell971_endpointUpper :
    hpThetaJensenKernelEndpointUpper (971 / 1600 : ℝ) (243 / 400 : ℝ) ≤ (133599669 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (243 / 200 : ℝ)) (26470230601651473 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (243 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell971_product_upper
  have hD : (288859913219919 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (971 / 800 : ℝ) - (243 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell971_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell971_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (971 / 800 : ℝ) - (243 / 800 : ℝ)) ≤
      (1 / (288859913219919 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (288859913219919 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((243 / 800 : ℝ) - Real.pi * Real.exp (971 / 800 : ℝ)) ≤
      (2 / (288859913219919 / 10000000000 : ℝ) : ℝ) := by
    rw [show (243 / 800 : ℝ) - Real.pi * Real.exp (971 / 800 : ℝ) =
      -(Real.pi * Real.exp (971 / 800 : ℝ) - (243 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (26470230601651473 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (26470230601651473 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell971_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (971 / 1600 : ℝ) (243 / 400 : ℝ)) :
    (131100977 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (133599669 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell971_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell971_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell972_leftExp :
    (16851470321 / 5000000000 : ℝ) ≤ Real.exp (243 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (243 / 200 : ℝ) (519349386517 / 500000000000 : ℝ)
    (16851470321 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell972_rightExp :
    Real.exp (973 / 800 : ℝ) ≤ (33745095661 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (973 / 800 : ℝ) (519369673999 / 500000000000 : ℝ)
    (33745095661 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell972_denomUpper :
    Real.exp (102975856312927973 / 10000000000000000 : ℝ) ≤ (74152299843851 / 2500000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (102975856312927973 / 10000000000000000 : ℝ)
    (344902051781 / 250000000000 : ℝ) (74152299843851 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell972_denomLower :
    (73153635290067 / 2500000000 : ℝ) ≤ Real.exp (6427516481086379 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6427516481086379 / 625000000000000 : ℝ) (689511876907 /
    500000000000 : ℝ) (73153635290067 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell972_product_lower :
    (6617555543586379 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (243 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell972_leftExp
    (by norm_num : (0 : ℝ) ≤ (16851470321 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell972_product_upper :
    Real.pi * Real.exp (973 / 800 : ℝ) ≤ (106013356312927973 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell972_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell972_endpointLower :
    (64883687 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (243 / 400 : ℝ) (973 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6617555543586379 / 625000000000000 : ℝ) (Real.pi * Real.exp (243 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell972_product_lower
  have hD : Real.exp (Real.pi * Real.exp (973 / 800 : ℝ) - (243 / 800 : ℝ)) ≤
      (74152299843851 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell972_denomUpper
    linarith [hpThetaJensenCell972_product_upper]
  have hi : (1 / (74152299843851 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (973 / 800 : ℝ) - (243 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (74152299843851 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (74152299843851 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((243 / 800 : ℝ) - Real.pi * Real.exp (973 / 800 : ℝ)) := by
    rw [show (243 / 800 : ℝ) - Real.pi * Real.exp (973 / 800 : ℝ) =
      -(Real.pi * Real.exp (973 / 800 : ℝ) - (243 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (243 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (243 / 200 : ℝ)) := by
    have h := hpThetaJensenCell972_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (74152299843851 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell972_endpointUpper :
    hpThetaJensenKernelEndpointUpper (243 / 400 : ℝ) (973 / 1600 : ℝ) ≤ (132242797 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (973 / 800 : ℝ)) (106013356312927973 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (973 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell972_product_upper
  have hD : (73153635290067 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (243 / 200 : ℝ) - (973 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell972_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell972_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (243 / 200 : ℝ) - (973 / 3200 : ℝ)) ≤
      (1 / (73153635290067 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (73153635290067 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((973 / 3200 : ℝ) - Real.pi * Real.exp (243 / 200 : ℝ)) ≤
      (2 / (73153635290067 / 2500000000 : ℝ) : ℝ) := by
    rw [show (973 / 3200 : ℝ) - Real.pi * Real.exp (243 / 200 : ℝ) =
      -(Real.pi * Real.exp (243 / 200 : ℝ) - (973 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (106013356312927973 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (106013356312927973 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell972_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (243 / 400 : ℝ) (973 / 1600 : ℝ)) :
    (64883687 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (132242797 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell972_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell972_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell973_leftExp :
    (33745095659 / 10000000000 : ℝ) ≤ Real.exp (973 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (973 / 800 : ℝ) (1038739347997 / 1000000000000 : ℝ)
    (33745095659 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell973_rightExp :
    Real.exp (487 / 400 : ℝ) ≤ (16893651703 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (487 / 400 : ℝ) (1038779924547 / 1000000000000 : ℝ)
    (16893651703 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell973_denomUpper :
    Real.exp (51552665434582879 / 5000000000000000 : ℝ) ≤ (15023725137107 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51552665434582879 / 5000000000000000 : ℝ) (690083260283
    / 500000000000 : ℝ) (15023725137107 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell973_denomLower :
    (148211438031897 / 5000000000 : ℝ) ≤ Real.exp (12871196570193641 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (12871196570193641 / 1250000000000000 : ℝ) (344895279101
    / 250000000000 : ℝ) (148211438031897 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell973_product_lower :
    (13251665320193641 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (973 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell973_leftExp
    (by norm_num : (0 : ℝ) ≤ (33745095659 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell973_product_upper :
    Real.pi * Real.exp (487 / 400 : ℝ) ≤ (53072977934582879 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell973_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell973_endpointLower :
    (128445171 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (973 / 1600 : ℝ) (487 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (13251665320193641 / 1250000000000000 : ℝ) (Real.pi * Real.exp (973 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell973_product_lower
  have hD : Real.exp (Real.pi * Real.exp (487 / 400 : ℝ) - (973 / 3200 : ℝ)) ≤
      (15023725137107 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell973_denomUpper
    linarith [hpThetaJensenCell973_product_upper]
  have hi : (1 / (15023725137107 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (487 / 400 : ℝ) - (973 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15023725137107 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15023725137107 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((973 / 3200 : ℝ) - Real.pi * Real.exp (487 / 400 : ℝ)) := by
    rw [show (973 / 3200 : ℝ) - Real.pi * Real.exp (487 / 400 : ℝ) =
      -(Real.pi * Real.exp (487 / 400 : ℝ) - (973 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (973 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (973 / 800 : ℝ)) := by
    have h := hpThetaJensenCell973_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15023725137107 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell973_endpointUpper :
    hpThetaJensenKernelEndpointUpper (973 / 1600 : ℝ) (487 / 800 : ℝ) ≤ (130897501 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (487 / 400 : ℝ)) (53072977934582879 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (487 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell973_product_upper
  have hD : (148211438031897 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (973 / 800 : ℝ) - (487 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell973_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell973_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (973 / 800 : ℝ) - (487 / 1600 : ℝ)) ≤
      (1 / (148211438031897 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (148211438031897 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((487 / 1600 : ℝ) - Real.pi * Real.exp (973 / 800 : ℝ)) ≤
      (2 / (148211438031897 / 5000000000 : ℝ) : ℝ) := by
    rw [show (487 / 1600 : ℝ) - Real.pi * Real.exp (973 / 800 : ℝ) =
      -(Real.pi * Real.exp (973 / 800 : ℝ) - (487 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53072977934582879 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (53072977934582879 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell973_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (973 / 1600 : ℝ) (487 / 800 : ℝ)) :
    (128445171 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (130897501 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell973_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell973_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell974_leftExp :
    (8446825851 / 2500000000 : ℝ) ≤ Real.exp (487 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (487 / 400 : ℝ) (519389962273 / 500000000000 : ℝ)
    (8446825851 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell974_rightExp :
    Real.exp (39 / 32 : ℝ) ≤ (16914781971 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (39 / 32 : ℝ) (25970512567 / 25000000000 : ℝ)
    (16914781971 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell974_denomUpper :
    Real.exp (51617485636619803 / 5000000000000000 : ℝ) ≤ (152197612817977 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (51617485636619803 / 5000000000000000 : ℝ) (345181443887
    / 250000000000 : ℝ) (152197612817977 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell974_denomLower :
    (150142875037481 / 5000000000 : ℝ) ≤ Real.exp (3221845221111849 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3221845221111849 / 312500000000000 : ℝ) (690069709351 /
    500000000000 : ℝ) (150142875037481 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell974_product_lower :
    (3317060064861849 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (487 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell974_leftExp
    (by norm_num : (0 : ℝ) ≤ (8446825851 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell974_product_upper :
    Real.pi * Real.exp (39 / 32 : ℝ) ≤ (53139360636619803 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell974_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell974_endpointLower :
    (50853717 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (487 / 800 : ℝ) (39 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3317060064861849 / 312500000000000 : ℝ) (Real.pi * Real.exp (487 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell974_product_lower
  have hD : Real.exp (Real.pi * Real.exp (39 / 32 : ℝ) - (487 / 1600 : ℝ)) ≤
      (152197612817977 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell974_denomUpper
    linarith [hpThetaJensenCell974_product_upper]
  have hi : (1 / (152197612817977 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (39 / 32 : ℝ) - (487 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (152197612817977 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (152197612817977 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((487 / 1600 : ℝ) - Real.pi * Real.exp (39 / 32 : ℝ)) := by
    rw [show (487 / 1600 : ℝ) - Real.pi * Real.exp (39 / 32 : ℝ) =
      -(Real.pi * Real.exp (39 / 32 : ℝ) - (487 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (487 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (487 / 400 : ℝ)) := by
    have h := hpThetaJensenCell974_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (152197612817977 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell974_endpointUpper :
    hpThetaJensenKernelEndpointUpper (487 / 800 : ℝ) (39 / 64 : ℝ) ≤ (259127411 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (39 / 32 : ℝ)) (53139360636619803 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (39 / 64 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell974_product_upper
  have hD : (150142875037481 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (487 / 400 : ℝ) - (39 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell974_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell974_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (487 / 400 : ℝ) - (39 / 128 : ℝ)) ≤
      (1 / (150142875037481 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (150142875037481 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((39 / 128 : ℝ) - Real.pi * Real.exp (487 / 400 : ℝ)) ≤
      (2 / (150142875037481 / 5000000000 : ℝ) : ℝ) := by
    rw [show (39 / 128 : ℝ) - Real.pi * Real.exp (487 / 400 : ℝ) =
      -(Real.pi * Real.exp (487 / 400 : ℝ) - (39 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53139360636619803 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (53139360636619803 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell974_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (487 / 800 : ℝ) (39 / 64 : ℝ)) :
    (50853717 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (259127411 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell974_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell974_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell975_leftExp :
    (1691478197 / 500000000 : ℝ) ≤ Real.exp (39 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (39 / 32 : ℝ) (1038820502679 / 1000000000000 : ℝ)
    (1691478197 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell975_rightExp :
    Real.exp (61 / 50 : ℝ) ≤ (16935938669 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (61 / 50 : ℝ) (1038861082399 / 1000000000000 : ℝ)
    (16935938669 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell975_denomUpper :
    Real.exp (51682388870959717 / 5000000000000000 : ℝ) ≤ (308372228756573 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (51682388870959717 / 5000000000000000 : ℝ) (345321493491
    / 250000000000 : ℝ) (308372228756573 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell975_denomLower :
    (304204008750391 / 10000000000 : ℝ) ≤ Real.exp (645179296483703 / 62500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (645179296483703 / 62500000000000 : ℝ) (1380698662519 /
    1000000000000 : ℝ) (304204008750391 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell975_product_lower :
    (664241796483703 / 62500000000000 : ℝ) ≤ Real.pi * Real.exp (39 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell975_leftExp
    (by norm_num : (0 : ℝ) ≤ (1691478197 / 500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell975_product_upper :
    Real.pi * Real.exp (61 / 50 : ℝ) ≤ (53205826370959717 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell975_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell975_endpointLower :
    (251669331 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 64 : ℝ) (61 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (664241796483703 / 62500000000000 : ℝ) (Real.pi * Real.exp (39 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell975_product_lower
  have hD : Real.exp (Real.pi * Real.exp (61 / 50 : ℝ) - (39 / 128 : ℝ)) ≤
      (308372228756573 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell975_denomUpper
    linarith [hpThetaJensenCell975_product_upper]
  have hi : (1 / (308372228756573 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (61 / 50 : ℝ) - (39 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (308372228756573 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (308372228756573 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((39 / 128 : ℝ) - Real.pi * Real.exp (61 / 50 : ℝ)) := by
    rw [show (39 / 128 : ℝ) - Real.pi * Real.exp (61 / 50 : ℝ) =
      -(Real.pi * Real.exp (61 / 50 : ℝ) - (39 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (39 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (39 / 32 : ℝ)) := by
    have h := hpThetaJensenCell975_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (308372228756573 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell975_endpointUpper :
    hpThetaJensenKernelEndpointUpper (39 / 64 : ℝ) (61 / 100 : ℝ) ≤ (256482671 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (61 / 50 : ℝ)) (53205826370959717 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (61 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell975_product_upper
  have hD : (304204008750391 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (39 / 32 : ℝ) - (61 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell975_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell975_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (39 / 32 : ℝ) - (61 / 200 : ℝ)) ≤
      (1 / (304204008750391 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (304204008750391 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((61 / 200 : ℝ) - Real.pi * Real.exp (39 / 32 : ℝ)) ≤
      (2 / (304204008750391 / 10000000000 : ℝ) : ℝ) := by
    rw [show (61 / 200 : ℝ) - Real.pi * Real.exp (39 / 32 : ℝ) =
      -(Real.pi * Real.exp (39 / 32 : ℝ) - (61 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (53205826370959717 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (53205826370959717 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell975_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (39 / 64 : ℝ) (61 / 100 : ℝ)) :
    (251669331 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (256482671 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell975_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell975_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell976_leftExp :
    (4233984667 / 1250000000 : ℝ) ≤ Real.exp (61 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (61 / 50 : ℝ) (519430541199 / 500000000000 : ℝ)
    (4233984667 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell976_rightExp :
    Real.exp (977 / 800 : ℝ) ≤ (33914243657 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (977 / 800 : ℝ) (519450831851 / 500000000000 : ℝ)
    (33914243657 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell976_denomUpper :
    Real.exp (103494750473125601 / 10000000000000000 : ℝ) ≤ (156203193288153 / 5000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (103494750473125601 / 10000000000000000 : ℝ)
    (345461779409 / 250000000000 : ℝ) (156203193288153 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell976_denomLower :
    (308178512269483 / 10000000000 : ℝ) ≤ Real.exp (1614976466621233 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1614976466621233 / 156250000000000 : ℝ) (172657356219 /
    125000000000 : ℝ) (308178512269483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell976_product_lower :
    (1662681544746233 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (61 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell976_leftExp
    (by norm_num : (0 : ℝ) ≤ (4233984667 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell976_product_upper :
    Real.pi * Real.exp (977 / 800 : ℝ) ≤ (106544750473125601 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell976_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell976_endpointLower :
    (15568277 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 100 : ℝ) (977 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1662681544746233 / 156250000000000 : ℝ) (Real.pi * Real.exp (61 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell976_product_lower
  have hD : Real.exp (Real.pi * Real.exp (977 / 800 : ℝ) - (61 / 200 : ℝ)) ≤
      (156203193288153 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell976_denomUpper
    linarith [hpThetaJensenCell976_product_upper]
  have hi : (1 / (156203193288153 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (977 / 800 : ℝ) - (61 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (156203193288153 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (156203193288153 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((61 / 200 : ℝ) - Real.pi * Real.exp (977 / 800 : ℝ)) := by
    rw [show (61 / 200 : ℝ) - Real.pi * Real.exp (977 / 800 : ℝ) =
      -(Real.pi * Real.exp (977 / 800 : ℝ) - (61 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (61 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (61 / 50 : ℝ)) := by
    have h := hpThetaJensenCell976_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (156203193288153 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell976_endpointUpper :
    hpThetaJensenKernelEndpointUpper (61 / 100 : ℝ) (977 / 1600 : ℝ) ≤ (253860633 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (977 / 800 : ℝ)) (106544750473125601 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (977 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell976_product_upper
  have hD : (308178512269483 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (61 / 50 : ℝ) - (977 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell976_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell976_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (61 / 50 : ℝ) - (977 / 3200 : ℝ)) ≤
      (1 / (308178512269483 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (308178512269483 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((977 / 3200 : ℝ) - Real.pi * Real.exp (61 / 50 : ℝ)) ≤
      (2 / (308178512269483 / 10000000000 : ℝ) : ℝ) := by
    rw [show (977 / 3200 : ℝ) - Real.pi * Real.exp (61 / 50 : ℝ) =
      -(Real.pi * Real.exp (61 / 50 : ℝ) - (977 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (106544750473125601 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (106544750473125601 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell976_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (61 / 100 : ℝ) (977 / 1600 : ℝ)) :
    (15568277 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (253860633 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell976_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell976_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell977_leftExp :
    (6782848731 / 2000000000 : ℝ) ≤ Real.exp (977 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (977 / 800 : ℝ) (1038901663701 / 1000000000000 : ℝ)
    (6782848731 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell977_rightExp :
    Real.exp (489 / 400 : ℝ) ≤ (4244582871 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (489 / 400 : ℝ) (1038942246591 / 1000000000000 : ℝ)
    (4244582871 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell977_denomUpper :
    Real.exp (12953111210453503 / 1250000000000000 : ℝ) ≤ (31649858866467 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12953111210453503 / 1250000000000000 : ℝ) (276481841693
    / 200000000000 : ℝ) (31649858866467 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell977_denomLower :
    (78052533636927 / 2500000000 : ℝ) ≤ Real.exp (2587211663814969 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2587211663814969 / 250000000000000 : ℝ) (690909991111 /
    500000000000 : ℝ) (78052533636927 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell977_product_lower :
    (2663617913814969 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (977 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell977_leftExp
    (by norm_num : (0 : ℝ) ≤ (6782848731 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell977_product_upper :
    Real.pi * Real.exp (489 / 400 : ℝ) ≤ (13334751835453503 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell977_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell977_endpointLower :
    (12326887 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (977 / 1600 : ℝ) (489 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2663617913814969 / 250000000000000 : ℝ) (Real.pi * Real.exp (977 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell977_product_lower
  have hD : Real.exp (Real.pi * Real.exp (489 / 400 : ℝ) - (977 / 3200 : ℝ)) ≤
      (31649858866467 / 1000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell977_denomUpper
    linarith [hpThetaJensenCell977_product_upper]
  have hi : (1 / (31649858866467 / 1000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (489 / 400 : ℝ) - (977 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (31649858866467 / 1000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (31649858866467 / 1000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((977 / 3200 : ℝ) - Real.pi * Real.exp (489 / 400 : ℝ)) := by
    rw [show (977 / 3200 : ℝ) - Real.pi * Real.exp (489 / 400 : ℝ) =
      -(Real.pi * Real.exp (489 / 400 : ℝ) - (977 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (977 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (977 / 800 : ℝ)) := by
    have h := hpThetaJensenCell977_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (31649858866467 / 1000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell977_endpointUpper :
    hpThetaJensenKernelEndpointUpper (977 / 1600 : ℝ) (489 / 800 : ℝ) ≤ (62815287 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (489 / 400 : ℝ)) (13334751835453503 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (489 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell977_product_upper
  have hD : (78052533636927 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (977 / 800 : ℝ) - (489 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell977_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell977_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (977 / 800 : ℝ) - (489 / 1600 : ℝ)) ≤
      (1 / (78052533636927 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (78052533636927 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((489 / 1600 : ℝ) - Real.pi * Real.exp (977 / 800 : ℝ)) ≤
      (2 / (78052533636927 / 2500000000 : ℝ) : ℝ) := by
    rw [show (489 / 1600 : ℝ) - Real.pi * Real.exp (977 / 800 : ℝ) =
      -(Real.pi * Real.exp (977 / 800 : ℝ) - (489 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (13334751835453503 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (13334751835453503 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell977_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (977 / 1600 : ℝ) (489 / 800 : ℝ)) :
    (12326887 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (62815287 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell977_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell977_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell978_leftExp :
    (16978331483 / 5000000000 : ℝ) ≤ Real.exp (489 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (489 / 400 : ℝ) (103894224659 / 100000000000 : ℝ)
    (16978331483 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell978_rightExp :
    Real.exp (979 / 800 : ℝ) ≤ (33999135337 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (979 / 800 : ℝ) (207796566213 / 200000000000 : ℝ)
    (33999135337 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell978_denomUpper :
    Real.exp (103755195580771841 / 10000000000000000 : ℝ) ≤ (320649739156723 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (103755195580771841 / 10000000000000000 : ℝ) (1080447069
    / 781250000 : ℝ) (320649739156723 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell978_denomLower :
    (79074941148807 / 2500000000 : ℝ) ≤ Real.exp (6476162857542617 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6476162857542617 / 625000000000000 : ℝ) (138238206183 /
    100000000000 : ℝ) (79074941148807 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell978_product_lower :
    (6667373795042617 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (489 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell978_leftExp
    (by norm_num : (0 : ℝ) ≤ (16978331483 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell978_product_upper :
    Real.pi * Real.exp (979 / 800 : ℝ) ≤ (106811445580771841 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell978_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell978_endpointLower :
    (24400511 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (489 / 800 : ℝ) (979 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6667373795042617 / 625000000000000 : ℝ) (Real.pi * Real.exp (489 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell978_product_lower
  have hD : Real.exp (Real.pi * Real.exp (979 / 800 : ℝ) - (489 / 1600 : ℝ)) ≤
      (320649739156723 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell978_denomUpper
    linarith [hpThetaJensenCell978_product_upper]
  have hi : (1 / (320649739156723 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (979 / 800 : ℝ) - (489 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (320649739156723 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (320649739156723 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((489 / 1600 : ℝ) - Real.pi * Real.exp (979 / 800 : ℝ)) := by
    rw [show (489 / 1600 : ℝ) - Real.pi * Real.exp (979 / 800 : ℝ) =
      -(Real.pi * Real.exp (979 / 800 : ℝ) - (489 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (489 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (489 / 400 : ℝ)) := by
    have h := hpThetaJensenCell978_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (320649739156723 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell978_endpointUpper :
    hpThetaJensenKernelEndpointUpper (489 / 800 : ℝ) (979 / 1600 : ℝ) ≤ (248684067 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (979 / 800 : ℝ)) (106811445580771841 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (979 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell978_product_upper
  have hD : (79074941148807 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (489 / 400 : ℝ) - (979 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell978_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell978_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (489 / 400 : ℝ) - (979 / 3200 : ℝ)) ≤
      (1 / (79074941148807 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (79074941148807 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((979 / 3200 : ℝ) - Real.pi * Real.exp (489 / 400 : ℝ)) ≤
      (2 / (79074941148807 / 2500000000 : ℝ) : ℝ) := by
    rw [show (979 / 3200 : ℝ) - Real.pi * Real.exp (489 / 400 : ℝ) =
      -(Real.pi * Real.exp (489 / 400 : ℝ) - (979 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (106811445580771841 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (106811445580771841 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell978_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (489 / 800 : ℝ) (979 / 1600 : ℝ)) :
    (24400511 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (248684067 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell978_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell978_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell979_leftExp :
    (6799827067 / 2000000000 : ℝ) ≤ Real.exp (979 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (979 / 800 : ℝ) (129872853883 / 125000000000 : ℝ)
    (6799827067 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell979_rightExp :
    Real.exp (49 / 40 : ℝ) ≤ (34041660829 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49 / 40 : ℝ) (8312187337 / 8000000000 : ℝ)
    (34041660829 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell979_denomUpper :
    Real.exp (103885668368760597 / 10000000000000000 : ℝ) ≤ (1015189865997 / 31250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (103885668368760597 / 10000000000000000 : ℝ)
    (691768119527 / 500000000000 : ℝ) (1015189865997 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell979_denomLower :
    (80112076492793 / 2500000000 : ℝ) ≤ Real.exp (2593722789383833 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2593722789383833 / 250000000000000 : ℝ) (345736272611 /
    250000000000 : ℝ) (80112076492793 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell979_product_lower :
    (2670285289383833 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (979 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell979_leftExp
    (by norm_num : (0 : ℝ) ≤ (6799827067 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell979_product_upper :
    Real.pi * Real.exp (49 / 40 : ℝ) ≤ (106945043368760597 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell979_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell979_endpointLower :
    (120747197 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (979 / 1600 : ℝ) (49 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2670285289383833 / 250000000000000 : ℝ) (Real.pi * Real.exp (979 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell979_product_lower
  have hD : Real.exp (Real.pi * Real.exp (49 / 40 : ℝ) - (979 / 3200 : ℝ)) ≤
      (1015189865997 / 31250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell979_denomUpper
    linarith [hpThetaJensenCell979_product_upper]
  have hi : (1 / (1015189865997 / 31250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (49 / 40 : ℝ) - (979 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1015189865997 / 31250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1015189865997 / 31250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((979 / 3200 : ℝ) - Real.pi * Real.exp (49 / 40 : ℝ)) := by
    rw [show (979 / 3200 : ℝ) - Real.pi * Real.exp (49 / 40 : ℝ) =
      -(Real.pi * Real.exp (49 / 40 : ℝ) - (979 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (979 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (979 / 800 : ℝ)) := by
    have h := hpThetaJensenCell979_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1015189865997 / 31250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell979_endpointUpper :
    hpThetaJensenKernelEndpointUpper (979 / 1600 : ℝ) (49 / 80 : ℝ) ≤ (123064621 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (49 / 40 : ℝ)) (106945043368760597 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (49 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell979_product_upper
  have hD : (80112076492793 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (979 / 800 : ℝ) - (49 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell979_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell979_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (979 / 800 : ℝ) - (49 / 160 : ℝ)) ≤
      (1 / (80112076492793 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (80112076492793 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((49 / 160 : ℝ) - Real.pi * Real.exp (979 / 800 : ℝ)) ≤
      (2 / (80112076492793 / 2500000000 : ℝ) : ℝ) := by
    rw [show (49 / 160 : ℝ) - Real.pi * Real.exp (979 / 800 : ℝ) =
      -(Real.pi * Real.exp (979 / 800 : ℝ) - (49 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (106945043368760597 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (106945043368760597 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell979_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (979 / 1600 : ℝ) (49 / 80 : ℝ)) :
    (120747197 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (123064621 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell979_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell979_endpointUpper

def hpThetaJensenCellsBatch048Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (146544509 / 5000000000 : ℝ)
  | 1 => (145080529 / 5000000000 : ℝ)
  | 2 => (287257567 / 10000000000 : ℝ)
  | 3 => (28437839 / 1000000000 : ℝ)
  | 4 => (2252187 / 80000000 : ℝ)
  | 5 => (278692367 / 10000000000 : ℝ)
  | 6 => (137942607 / 5000000000 : ℝ)
  | 7 => (273101763 / 10000000000 : ℝ)
  | 8 => (270341863 / 10000000000 : ℝ)
  | 9 => (133802681 / 5000000000 : ℝ)
  | 10 => (264892109 / 10000000000 : ℝ)
  | 11 => (131100977 / 5000000000 : ℝ)
  | 12 => (64883687 / 2500000000 : ℝ)
  | 13 => (128445171 / 5000000000 : ℝ)
  | 14 => (50853717 / 2000000000 : ℝ)
  | 15 => (251669331 / 10000000000 : ℝ)
  | 16 => (15568277 / 625000000 : ℝ)
  | 17 => (12326887 / 500000000 : ℝ)
  | 18 => (24400511 / 1000000000 : ℝ)
  | 19 => (120747197 / 5000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch048Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (298622127 / 10000000000 : ℝ)
  | 1 => (147821813 / 5000000000 : ℝ)
  | 2 => (292689967 / 10000000000 : ℝ)
  | 3 => (57952199 / 2000000000 : ℝ)
  | 4 => (286856553 / 10000000000 : ℝ)
  | 5 => (283976487 / 10000000000 : ℝ)
  | 6 => (281120641 / 10000000000 : ℝ)
  | 7 => (278288861 / 10000000000 : ℝ)
  | 8 => (137740497 / 5000000000 : ℝ)
  | 9 => (136348443 / 5000000000 : ℝ)
  | 10 => (1054439 / 39062500 : ℝ)
  | 11 => (133599669 / 5000000000 : ℝ)
  | 12 => (132242797 / 5000000000 : ℝ)
  | 13 => (130897501 / 5000000000 : ℝ)
  | 14 => (259127411 / 10000000000 : ℝ)
  | 15 => (256482671 / 10000000000 : ℝ)
  | 16 => (253860633 / 10000000000 : ℝ)
  | 17 => (62815287 / 2500000000 : ℝ)
  | 18 => (248684067 / 10000000000 : ℝ)
  | 19 => (123064621 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch048_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch048Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch048Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell960_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell961_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell962_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell963_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell964_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell965_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell966_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell967_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell968_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell969_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell970_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell971_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell972_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell973_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell974_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell975_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell976_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell977_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell978_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell979_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper] at h ⊢
    exact h

end HodgeProofHP
