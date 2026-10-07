import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell360_leftExp :
    (7841560927 / 5000000000 : ℝ) ≤ Real.exp (9 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 20 : ℝ) (126770230259 / 125000000000 : ℝ)
    (7841560927 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell360_rightExp :
    Real.exp (361 / 800 : ℝ) ≤ (3140547603 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (361 / 800 : ℝ) (63387591159 / 62500000000 : ℝ)
    (3140547603 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell360_denomUpper :
    Real.exp (9641322365751579 / 2000000000000000 : ℝ) ≤ (1240470814783 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9641322365751579 / 2000000000000000 : ℝ) (1162584637133
    / 1000000000000 : ℝ) (1240470814783 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell360_denomLower :
    (308115664637 / 2500000000 : ℝ) ≤ Real.exp (3008865321971973 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3008865321971973 / 625000000000000 : ℝ) (581174679309 /
    500000000000 : ℝ) (308115664637 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell360_product_lower :
    (3079373134471973 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell360_leftExp
    (by norm_num : (0 : ℝ) ≤ (7841560927 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell360_product_upper :
    Real.pi * Real.exp (361 / 800 : ℝ) ≤ (9866322365751579 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell360_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell360_endpointLower :
    (1088928743 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 40 : ℝ) (361 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3079373134471973 / 625000000000000 : ℝ) (Real.pi * Real.exp (9 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell360_product_lower
  have hD : Real.exp (Real.pi * Real.exp (361 / 800 : ℝ) - (9 / 80 : ℝ)) ≤
      (1240470814783 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell360_denomUpper
    linarith [hpThetaJensenCell360_product_upper]
  have hi : (1 / (1240470814783 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (361 / 800 : ℝ) - (9 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1240470814783 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1240470814783 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 80 : ℝ) - Real.pi * Real.exp (361 / 800 : ℝ)) := by
    rw [show (9 / 80 : ℝ) - Real.pi * Real.exp (361 / 800 : ℝ) =
      -(Real.pi * Real.exp (361 / 800 : ℝ) - (9 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 20 : ℝ)) := by
    have h := hpThetaJensenCell360_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1240470814783 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell360_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 40 : ℝ) (361 / 1600 : ℝ) ≤ (11022444979 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (361 / 800 : ℝ)) (9866322365751579 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (361 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell360_product_upper
  have hD : (308115664637 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 20 : ℝ) - (361 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell360_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell360_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 20 : ℝ) - (361 / 3200 : ℝ)) ≤
      (1 / (308115664637 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (308115664637 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((361 / 3200 : ℝ) - Real.pi * Real.exp (9 / 20 : ℝ)) ≤
      (2 / (308115664637 / 2500000000 : ℝ) : ℝ) := by
    rw [show (361 / 3200 : ℝ) - Real.pi * Real.exp (9 / 20 : ℝ) =
      -(Real.pi * Real.exp (9 / 20 : ℝ) - (361 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9866322365751579 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (9866322365751579 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell360_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 40 : ℝ) (361 / 1600 : ℝ)) :
    (1088928743 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (11022444979 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell360_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell360_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell361_leftExp :
    (7851369007 / 5000000000 : ℝ) ≤ Real.exp (361 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (361 / 800 : ℝ) (1014201458543 / 1000000000000 : ℝ)
    (7851369007 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell361_rightExp :
    Real.exp (181 / 400 : ℝ) ≤ (15722378711 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (181 / 400 : ℝ) (507120538281 / 500000000000 : ℝ)
    (15722378711 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell361_denomUpper :
    Real.exp (48265189901826623 / 10000000000000000 : ℝ) ≤ (623879289059 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48265189901826623 / 10000000000000000 : ℝ)
    (1162797475263 / 1000000000000 : ℝ) (623879289059 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell361_denomLower :
    (309923453917 / 2500000000 : ℝ) ≤ Real.exp (3012521632679893 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3012521632679893 / 625000000000000 : ℝ) (1162561873563 /
    1000000000000 : ℝ) (309923453917 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell361_product_lower :
    (3083224757679893 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (361 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell361_leftExp
    (by norm_num : (0 : ℝ) ≤ (7851369007 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell361_product_upper :
    Real.pi * Real.exp (181 / 400 : ℝ) ≤ (49393314901826623 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell361_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell361_endpointLower :
    (5429359377 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (361 / 1600 : ℝ) (181 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3083224757679893 / 625000000000000 : ℝ) (Real.pi * Real.exp (361 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell361_product_lower
  have hD : Real.exp (Real.pi * Real.exp (181 / 400 : ℝ) - (361 / 3200 : ℝ)) ≤
      (623879289059 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell361_denomUpper
    linarith [hpThetaJensenCell361_product_upper]
  have hi : (1 / (623879289059 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (181 / 400 : ℝ) - (361 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (623879289059 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (623879289059 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((361 / 3200 : ℝ) - Real.pi * Real.exp (181 / 400 : ℝ)) := by
    rw [show (361 / 3200 : ℝ) - Real.pi * Real.exp (181 / 400 : ℝ) =
      -(Real.pi * Real.exp (181 / 400 : ℝ) - (361 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (361 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (361 / 800 : ℝ)) := by
    have h := hpThetaJensenCell361_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (623879289059 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell361_endpointUpper :
    hpThetaJensenKernelEndpointUpper (361 / 1600 : ℝ) (181 / 800 : ℝ) ≤ (10991576463 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (181 / 400 : ℝ)) (49393314901826623 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (181 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell361_product_upper
  have hD : (309923453917 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (361 / 800 : ℝ) - (181 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell361_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell361_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (361 / 800 : ℝ) - (181 / 1600 : ℝ)) ≤
      (1 / (309923453917 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (309923453917 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((181 / 1600 : ℝ) - Real.pi * Real.exp (361 / 800 : ℝ)) ≤
      (2 / (309923453917 / 2500000000 : ℝ) : ℝ) := by
    rw [show (181 / 1600 : ℝ) - Real.pi * Real.exp (361 / 800 : ℝ) =
      -(Real.pi * Real.exp (361 / 800 : ℝ) - (181 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49393314901826623 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (49393314901826623 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell361_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (361 / 1600 : ℝ) (181 / 800 : ℝ)) :
    (5429359377 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10991576463 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell361_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell361_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell362_leftExp :
    (15722378709 / 10000000000 : ℝ) ≤ Real.exp (181 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (181 / 400 : ℝ) (1014241076561 / 1000000000000 : ℝ)
    (15722378709 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell362_rightExp :
    Real.exp (363 / 800 : ℝ) ≤ (3935510993 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (363 / 800 : ℝ) (15848135877 / 15625000000 : ℝ)
    (3935510993 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell362_denomUpper :
    Real.exp (12080961287031849 / 2500000000000000 : ℝ) ≤ (62754942149 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12080961287031849 / 2500000000000000 : ℝ) (290752658209
    / 250000000000 : ℝ) (62754942149 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell362_denomLower :
    (12469770113 / 100000000 : ℝ) ≤ Real.exp (6032365521645591 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6032365521645591 / 1250000000000000 : ℝ) (1162774707443
    / 1000000000000 : ℝ) (12469770113 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell362_product_lower :
    (6174162396645591 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (181 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell362_leftExp
    (by norm_num : (0 : ℝ) ≤ (15722378709 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell362_product_upper :
    Real.pi * Real.exp (363 / 800 : ℝ) ≤ (12363773787031849 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell362_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell362_endpointLower :
    (1353517713 / 1250000000 : ℝ) ≤ hpThetaTraceEndpointLower (181 / 800 : ℝ) (363 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6174162396645591 / 1250000000000000 : ℝ) (Real.pi * Real.exp (181 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell362_product_lower
  have hD : Real.exp (Real.pi * Real.exp (363 / 800 : ℝ) - (181 / 1600 : ℝ)) ≤
      (62754942149 / 500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell362_denomUpper
    linarith [hpThetaJensenCell362_product_upper]
  have hi : (1 / (62754942149 / 500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (363 / 800 : ℝ) - (181 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (62754942149 / 500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (62754942149 / 500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((181 / 1600 : ℝ) - Real.pi * Real.exp (363 / 800 : ℝ)) := by
    rw [show (181 / 1600 : ℝ) - Real.pi * Real.exp (363 / 800 : ℝ) =
      -(Real.pi * Real.exp (363 / 800 : ℝ) - (181 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (181 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (181 / 400 : ℝ)) := by
    have h := hpThetaJensenCell362_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (62754942149 / 500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell362_endpointUpper :
    hpThetaJensenKernelEndpointUpper (181 / 800 : ℝ) (363 / 1600 : ℝ) ≤ (548034959 / 500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (363 / 800 : ℝ)) (12363773787031849 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (363 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell362_product_upper
  have hD : (12469770113 / 100000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (181 / 400 : ℝ) - (363 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell362_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell362_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (181 / 400 : ℝ) - (363 / 3200 : ℝ)) ≤
      (1 / (12469770113 / 100000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12469770113 / 100000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((363 / 3200 : ℝ) - Real.pi * Real.exp (181 / 400 : ℝ)) ≤
      (2 / (12469770113 / 100000000 : ℝ) : ℝ) := by
    rw [show (363 / 3200 : ℝ) - Real.pi * Real.exp (181 / 400 : ℝ) =
      -(Real.pi * Real.exp (181 / 400 : ℝ) - (363 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12363773787031849 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (12363773787031849 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell362_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (181 / 800 : ℝ) (363 / 1600 : ℝ)) :
    (1353517713 / 1250000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (548034959 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell362_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell362_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell363_leftExp :
    (15742043971 / 10000000000 : ℝ) ≤ Real.exp (363 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (363 / 800 : ℝ) (1014280696127 / 1000000000000 : ℝ)
    (15742043971 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell363_rightExp :
    Real.exp (91 / 200 : ℝ) ≤ (15761733831 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91 / 200 : ℝ) (507160158621 / 500000000000 : ℝ)
    (15761733831 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell363_denomUpper :
    Real.exp (48382577671332783 / 10000000000000000 : ℝ) ≤ (252498409 / 2000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48382577671332783 / 10000000000000000 : ℝ) (145403013799
    / 125000000000 : ℝ) (252498409 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell363_denomLower :
    (125431267631 / 1000000000 : ℝ) ≤ Real.exp (6039697425367729 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6039697425367729 / 1250000000000000 : ℝ) (581493930391 /
    500000000000 : ℝ) (125431267631 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell363_product_lower :
    (6181884925367729 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (363 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell363_leftExp
    (by norm_num : (0 : ℝ) ≤ (15742043971 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell363_product_upper :
    Real.pi * Real.exp (91 / 200 : ℝ) ≤ (49516952671332783 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell363_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell363_endpointLower :
    (10797556749 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (363 / 1600 : ℝ) (91 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6181884925367729 / 1250000000000000 : ℝ) (Real.pi * Real.exp (363 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell363_product_lower
  have hD : Real.exp (Real.pi * Real.exp (91 / 200 : ℝ) - (363 / 3200 : ℝ)) ≤
      (252498409 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell363_denomUpper
    linarith [hpThetaJensenCell363_product_upper]
  have hi : (1 / (252498409 / 2000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (91 / 200 : ℝ) - (363 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (252498409 / 2000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (252498409 / 2000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((363 / 3200 : ℝ) - Real.pi * Real.exp (91 / 200 : ℝ)) := by
    rw [show (363 / 3200 : ℝ) - Real.pi * Real.exp (91 / 200 : ℝ) =
      -(Real.pi * Real.exp (91 / 200 : ℝ) - (363 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (363 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (363 / 800 : ℝ)) := by
    have h := hpThetaJensenCell363_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (252498409 / 2000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell363_endpointUpper :
    hpThetaJensenKernelEndpointUpper (363 / 1600 : ℝ) (91 / 400 : ℝ) ≤ (2732453403 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (91 / 200 : ℝ)) (49516952671332783 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (91 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell363_product_upper
  have hD : (125431267631 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (363 / 800 : ℝ) - (91 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell363_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell363_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (363 / 800 : ℝ) - (91 / 800 : ℝ)) ≤
      (1 / (125431267631 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (125431267631 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((91 / 800 : ℝ) - Real.pi * Real.exp (363 / 800 : ℝ)) ≤
      (2 / (125431267631 / 1000000000 : ℝ) : ℝ) := by
    rw [show (91 / 800 : ℝ) - Real.pi * Real.exp (363 / 800 : ℝ) =
      -(Real.pi * Real.exp (363 / 800 : ℝ) - (91 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49516952671332783 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (49516952671332783 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell363_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (363 / 1600 : ℝ) (91 / 400 : ℝ)) :
    (10797556749 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2732453403 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell363_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell363_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell364_leftExp :
    (1576173383 / 1000000000 : ℝ) ≤ Real.exp (91 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (91 / 200 : ℝ) (1014320317241 / 1000000000000 : ℝ)
    (1576173383 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell364_rightExp :
    Real.exp (73 / 160 : ℝ) ≤ (15781448317 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (73 / 160 : ℝ) (1014359939903 / 1000000000000 : ℝ)
    (15781448317 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell364_denomUpper :
    Real.exp (48441387562548981 / 10000000000000000 : ℝ) ≤ (1269938622141 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48441387562548981 / 10000000000000000 : ℝ)
    (1163437908423 / 1000000000000 : ℝ) (1269938622141 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell364_denomLower :
    (1261701244923 / 10000000000 : ℝ) ≤ Real.exp (604703898830717 / 125000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (604703898830717 / 125000000000000 : ℝ) (1163201334087 /
    1000000000000 : ℝ) (1261701244923 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell364_product_lower :
    (618961711330717 / 125000000000000 : ℝ) ≤ Real.pi * Real.exp (91 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell364_leftExp
    (by norm_num : (0 : ℝ) ≤ (1576173383 / 1000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell364_product_upper :
    Real.pi * Real.exp (73 / 160 : ℝ) ≤ (49578887562548981 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell364_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell364_endpointLower :
    (10766964369 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 400 : ℝ) (73 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (618961711330717 / 125000000000000 : ℝ) (Real.pi * Real.exp (91 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell364_product_lower
  have hD : Real.exp (Real.pi * Real.exp (73 / 160 : ℝ) - (91 / 800 : ℝ)) ≤
      (1269938622141 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell364_denomUpper
    linarith [hpThetaJensenCell364_product_upper]
  have hi : (1 / (1269938622141 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (73 / 160 : ℝ) - (91 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1269938622141 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1269938622141 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((91 / 800 : ℝ) - Real.pi * Real.exp (73 / 160 : ℝ)) := by
    rw [show (91 / 800 : ℝ) - Real.pi * Real.exp (73 / 160 : ℝ) =
      -(Real.pi * Real.exp (73 / 160 : ℝ) - (91 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (91 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (91 / 200 : ℝ)) := by
    have h := hpThetaJensenCell364_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1269938622141 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell364_endpointUpper :
    hpThetaJensenKernelEndpointUpper (91 / 400 : ℝ) (73 / 320 : ℝ) ≤ (2724730059 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (73 / 160 : ℝ)) (49578887562548981 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (73 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell364_product_upper
  have hD : (1261701244923 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (91 / 200 : ℝ) - (73 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell364_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell364_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (91 / 200 : ℝ) - (73 / 640 : ℝ)) ≤
      (1 / (1261701244923 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1261701244923 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((73 / 640 : ℝ) - Real.pi * Real.exp (91 / 200 : ℝ)) ≤
      (2 / (1261701244923 / 10000000000 : ℝ) : ℝ) := by
    rw [show (73 / 640 : ℝ) - Real.pi * Real.exp (91 / 200 : ℝ) =
      -(Real.pi * Real.exp (91 / 200 : ℝ) - (73 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49578887562548981 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (49578887562548981 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell364_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (91 / 400 : ℝ) (73 / 320 : ℝ)) :
    (10766964369 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2724730059 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell364_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell364_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell365_leftExp :
    (3945362079 / 2500000000 : ℝ) ≤ Real.exp (73 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (73 / 160 : ℝ) (507179969951 / 500000000000 : ℝ)
    (3945362079 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell365_rightExp :
    Real.exp (183 / 400 : ℝ) ≤ (7900593731 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (183 / 400 : ℝ) (63399972757 / 62500000000 : ℝ)
    (7900593731 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell365_denomUpper :
    Real.exp (24250137461153483 / 5000000000000000 : ℝ) ≤ (319359754409 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (24250137461153483 / 5000000000000000 : ℝ) (1163652027457
    / 1000000000000 : ℝ) (319359754409 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell365_denomLower :
    (1269143155169 / 10000000000 : ℝ) ≤ Real.exp (1513597555561221 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1513597555561221 / 312500000000000 : ℝ) (58170756393 /
    50000000000 : ℝ) (1269143155169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell365_product_lower :
    (1549339743061221 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (73 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell365_leftExp
    (by norm_num : (0 : ℝ) ≤ (3945362079 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell365_product_upper :
    Real.pi * Real.exp (183 / 400 : ℝ) ≤ (24820449961153483 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell365_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell365_endpointLower :
    (10736365033 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 320 : ℝ) (183 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1549339743061221 / 312500000000000 : ℝ) (Real.pi * Real.exp (73 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell365_product_lower
  have hD : Real.exp (Real.pi * Real.exp (183 / 400 : ℝ) - (73 / 640 : ℝ)) ≤
      (319359754409 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell365_denomUpper
    linarith [hpThetaJensenCell365_product_upper]
  have hi : (1 / (319359754409 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (183 / 400 : ℝ) - (73 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (319359754409 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (319359754409 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((73 / 640 : ℝ) - Real.pi * Real.exp (183 / 400 : ℝ)) := by
    rw [show (73 / 640 : ℝ) - Real.pi * Real.exp (183 / 400 : ℝ) =
      -(Real.pi * Real.exp (183 / 400 : ℝ) - (73 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (73 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (73 / 160 : ℝ)) := by
    have h := hpThetaJensenCell365_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (319359754409 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell365_endpointUpper :
    hpThetaJensenKernelEndpointUpper (73 / 320 : ℝ) (183 / 800 : ℝ) ≤ (679251221 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (183 / 400 : ℝ)) (24820449961153483 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (183 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell365_product_upper
  have hD : (1269143155169 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (73 / 160 : ℝ) - (183 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell365_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell365_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (73 / 160 : ℝ) - (183 / 1600 : ℝ)) ≤
      (1 / (1269143155169 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1269143155169 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((183 / 1600 : ℝ) - Real.pi * Real.exp (73 / 160 : ℝ)) ≤
      (2 / (1269143155169 / 10000000000 : ℝ) : ℝ) := by
    rw [show (183 / 1600 : ℝ) - Real.pi * Real.exp (73 / 160 : ℝ) =
      -(Real.pi * Real.exp (73 / 160 : ℝ) - (183 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (24820449961153483 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (24820449961153483 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell365_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (73 / 320 : ℝ) (183 / 800 : ℝ)) :
    (10736365033 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (679251221 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell365_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell365_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell366_leftExp :
    (15801187461 / 10000000000 : ℝ) ≤ Real.exp (183 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (183 / 400 : ℝ) (1014399564111 / 1000000000000 : ℝ)
    (15801187461 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell366_rightExp :
    Real.exp (367 / 800 : ℝ) ≤ (61800591 / 39062500 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (367 / 800 : ℝ) (1014439189869 / 1000000000000 : ℝ)
    (61800591 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell366_denomUpper :
    Real.exp (189684530643963 / 39062500000000 : ℝ) ≤ (51399747121 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (189684530643963 / 39062500000000 : ℝ) (290966617 /
    250000000 : ℝ) (51399747121 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell366_denomLower :
    (1276638850041 / 10000000000 : ℝ) ≤ Real.exp (6061751139747239 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6061751139747239 / 1250000000000000 : ℝ) (116362924263 /
    100000000000 : ℝ) (1276638850041 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell366_product_lower :
    (6205110514747239 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (183 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell366_leftExp
    (by norm_num : (0 : ℝ) ≤ (15801187461 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell366_product_upper :
    Real.pi * Real.exp (367 / 800 : ℝ) ≤ (194152304081463 / 39062500000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell366_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell366_endpointLower :
    (5352879609 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (183 / 800 : ℝ) (367 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6205110514747239 / 1250000000000000 : ℝ) (Real.pi * Real.exp (183 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell366_product_lower
  have hD : Real.exp (Real.pi * Real.exp (367 / 800 : ℝ) - (183 / 1600 : ℝ)) ≤
      (51399747121 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell366_denomUpper
    linarith [hpThetaJensenCell366_product_upper]
  have hi : (1 / (51399747121 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (367 / 800 : ℝ) - (183 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (51399747121 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (51399747121 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((183 / 1600 : ℝ) - Real.pi * Real.exp (367 / 800 : ℝ)) := by
    rw [show (183 / 1600 : ℝ) - Real.pi * Real.exp (367 / 800 : ℝ) =
      -(Real.pi * Real.exp (367 / 800 : ℝ) - (183 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (183 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (183 / 400 : ℝ)) := by
    have h := hpThetaJensenCell366_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (51399747121 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell366_endpointUpper :
    hpThetaJensenKernelEndpointUpper (183 / 800 : ℝ) (367 / 1600 : ℝ) ≤ (2167422397 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (367 / 800 : ℝ)) (194152304081463 / 39062500000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (367 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell366_product_upper
  have hD : (1276638850041 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (183 / 400 : ℝ) - (367 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell366_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell366_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (183 / 400 : ℝ) - (367 / 3200 : ℝ)) ≤
      (1 / (1276638850041 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1276638850041 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((367 / 3200 : ℝ) - Real.pi * Real.exp (183 / 400 : ℝ)) ≤
      (2 / (1276638850041 / 10000000000 : ℝ) : ℝ) := by
    rw [show (367 / 3200 : ℝ) - Real.pi * Real.exp (183 / 400 : ℝ) =
      -(Real.pi * Real.exp (183 / 400 : ℝ) - (367 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (194152304081463 / 39062500000000 : ℝ) ^ 2 - 6 *
      (194152304081463 / 39062500000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell366_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (183 / 800 : ℝ) (367 / 1600 : ℝ)) :
    (5352879609 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2167422397 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell366_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell366_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell367_leftExp :
    (3164190259 / 2000000000 : ℝ) ≤ Real.exp (367 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (367 / 800 : ℝ) (253609797467 / 250000000000 : ℝ)
    (3164190259 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell367_rightExp :
    Real.exp (23 / 50 : ℝ) ≤ (15840739851 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 50 : ℝ) (507239408587 / 500000000000 : ℝ)
    (15840739851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell367_denomUpper :
    Real.exp (48618282430722643 / 10000000000000000 : ℝ) ≤ (32315076369 / 250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48618282430722643 / 10000000000000000 : ℝ)
    (1164081230581 / 1000000000000 : ℝ) (32315076369 / 250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell367_denomLower :
    (642094387881 / 5000000000 : ℝ) ≤ Real.exp (1213824350519041 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1213824350519041 / 250000000000000 : ℝ) (581921839451 /
    500000000000 : ℝ) (642094387881 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell367_product_lower :
    (1242574350519041 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (367 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell367_leftExp
    (by norm_num : (0 : ℝ) ≤ (3164190259 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell367_product_upper :
    Real.pi * Real.exp (23 / 50 : ℝ) ≤ (49765157430722643 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell367_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell367_endpointLower :
    (83399589 / 78125000 : ℝ) ≤ hpThetaTraceEndpointLower (367 / 1600 : ℝ) (23 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1242574350519041 / 250000000000000 : ℝ) (Real.pi * Real.exp (367 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell367_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 50 : ℝ) - (367 / 3200 : ℝ)) ≤
      (32315076369 / 250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell367_denomUpper
    linarith [hpThetaJensenCell367_product_upper]
  have hi : (1 / (32315076369 / 250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 50 : ℝ) - (367 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (32315076369 / 250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (32315076369 / 250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((367 / 3200 : ℝ) - Real.pi * Real.exp (23 / 50 : ℝ)) := by
    rw [show (367 / 3200 : ℝ) - Real.pi * Real.exp (23 / 50 : ℝ) =
      -(Real.pi * Real.exp (23 / 50 : ℝ) - (367 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (367 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (367 / 800 : ℝ)) := by
    have h := hpThetaJensenCell367_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (32315076369 / 250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell367_endpointUpper :
    hpThetaJensenKernelEndpointUpper (367 / 1600 : ℝ) (23 / 100 : ℝ) ≤ (10806198063 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 50 : ℝ)) (49765157430722643 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell367_product_upper
  have hD : (642094387881 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (367 / 800 : ℝ) - (23 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell367_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell367_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (367 / 800 : ℝ) - (23 / 200 : ℝ)) ≤
      (1 / (642094387881 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (642094387881 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 200 : ℝ) - Real.pi * Real.exp (367 / 800 : ℝ)) ≤
      (2 / (642094387881 / 5000000000 : ℝ) : ℝ) := by
    rw [show (23 / 200 : ℝ) - Real.pi * Real.exp (367 / 800 : ℝ) =
      -(Real.pi * Real.exp (367 / 800 : ℝ) - (23 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49765157430722643 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (49765157430722643 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell367_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (367 / 1600 : ℝ) (23 / 100 : ℝ)) :
    (83399589 / 78125000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10806198063 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell367_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell367_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell368_leftExp :
    (15840739849 / 10000000000 : ℝ) ≤ Real.exp (23 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (23 / 50 : ℝ) (1014478817173 / 1000000000000 : ℝ)
    (15840739849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell368_rightExp :
    Real.exp (369 / 800 : ℝ) ≤ (3965138289 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (369 / 800 : ℝ) (1014518446027 / 1000000000000 : ℝ)
    (3965138289 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell368_denomUpper :
    Real.exp (12169350692754377 / 2500000000000000 : ℝ) ≤ (260053520441 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12169350692754377 / 2500000000000000 : ℝ) (582148157847
    / 500000000000 : ℝ) (260053520441 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell368_denomLower :
    (1291793383111 / 10000000000 : ℝ) ≤ Real.exp (6076502072962451 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6076502072962451 / 1250000000000000 : ℝ) (582029218597 /
    500000000000 : ℝ) (1291793383111 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell368_product_lower :
    (6220642697962451 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (23 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell368_leftExp
    (by norm_num : (0 : ℝ) ≤ (15840739849 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell368_product_upper :
    Real.pi * Real.exp (369 / 800 : ℝ) ≤ (12456850692754377 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell368_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell368_endpointLower :
    (5322265017 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 100 : ℝ) (369 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6220642697962451 / 1250000000000000 : ℝ) (Real.pi * Real.exp (23 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell368_product_lower
  have hD : Real.exp (Real.pi * Real.exp (369 / 800 : ℝ) - (23 / 200 : ℝ)) ≤
      (260053520441 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell368_denomUpper
    linarith [hpThetaJensenCell368_product_upper]
  have hi : (1 / (260053520441 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (369 / 800 : ℝ) - (23 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (260053520441 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (260053520441 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((23 / 200 : ℝ) - Real.pi * Real.exp (369 / 800 : ℝ)) := by
    rw [show (23 / 200 : ℝ) - Real.pi * Real.exp (369 / 800 : ℝ) =
      -(Real.pi * Real.exp (369 / 800 : ℝ) - (23 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (23 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (23 / 50 : ℝ)) := by
    have h := hpThetaJensenCell368_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (260053520441 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell368_endpointUpper :
    hpThetaJensenKernelEndpointUpper (23 / 100 : ℝ) (369 / 1600 : ℝ) ≤ (2155055649 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (369 / 800 : ℝ)) (12456850692754377 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (369 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell368_product_upper
  have hD : (1291793383111 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (23 / 50 : ℝ) - (369 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell368_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell368_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (23 / 50 : ℝ) - (369 / 3200 : ℝ)) ≤
      (1 / (1291793383111 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1291793383111 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((369 / 3200 : ℝ) - Real.pi * Real.exp (23 / 50 : ℝ)) ≤
      (2 / (1291793383111 / 10000000000 : ℝ) : ℝ) := by
    rw [show (369 / 3200 : ℝ) - Real.pi * Real.exp (23 / 50 : ℝ) =
      -(Real.pi * Real.exp (23 / 50 : ℝ) - (369 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12456850692754377 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (12456850692754377 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell368_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (23 / 100 : ℝ) (369 / 1600 : ℝ)) :
    (5322265017 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2155055649 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell368_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell368_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell369_leftExp :
    (3172110631 / 2000000000 : ℝ) ≤ Real.exp (369 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (369 / 800 : ℝ) (507259223013 / 500000000000 : ℝ)
    (3172110631 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell369_rightExp :
    Real.exp (37 / 80 : ℝ) ≤ (3970097811 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37 / 80 : ℝ) (1014558076427 / 1000000000000 : ℝ)
    (3970097811 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell369_denomUpper :
    Real.exp (12184150242352923 / 2500000000000000 : ℝ) ≤ (2092780449 / 16000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12184150242352923 / 2500000000000000 : ℝ) (1164511723881
    / 1000000000000 : ℝ) (2092780449 / 16000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell369_denomLower :
    (324863281853 / 2500000000 : ℝ) ≤ Real.exp (1216778422683069 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1216778422683069 / 250000000000000 : ℝ) (232854703607 /
    200000000000 : ℝ) (324863281853 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell369_product_lower :
    (1245684672683069 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (369 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell369_leftExp
    (by norm_num : (0 : ℝ) ≤ (3172110631 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell369_product_upper :
    Real.pi * Real.exp (37 / 80 : ℝ) ≤ (12472431492352923 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell369_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell369_endpointLower :
    (1061390761 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (369 / 1600 : ℝ) (37 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1245684672683069 / 250000000000000 : ℝ) (Real.pi * Real.exp (369 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell369_product_lower
  have hD : Real.exp (Real.pi * Real.exp (37 / 80 : ℝ) - (369 / 3200 : ℝ)) ≤
      (2092780449 / 16000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell369_denomUpper
    linarith [hpThetaJensenCell369_product_upper]
  have hi : (1 / (2092780449 / 16000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (37 / 80 : ℝ) - (369 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2092780449 / 16000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2092780449 / 16000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((369 / 3200 : ℝ) - Real.pi * Real.exp (37 / 80 : ℝ)) := by
    rw [show (369 / 3200 : ℝ) - Real.pi * Real.exp (37 / 80 : ℝ) =
      -(Real.pi * Real.exp (37 / 80 : ℝ) - (369 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (369 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (369 / 800 : ℝ)) := by
    have h := hpThetaJensenCell369_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2092780449 / 16000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell369_endpointUpper :
    hpThetaJensenKernelEndpointUpper (369 / 1600 : ℝ) (37 / 160 : ℝ) ≤ (2148870601 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (37 / 80 : ℝ)) (12472431492352923 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (37 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell369_product_upper
  have hD : (324863281853 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (369 / 800 : ℝ) - (37 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell369_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell369_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (369 / 800 : ℝ) - (37 / 320 : ℝ)) ≤
      (1 / (324863281853 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (324863281853 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((37 / 320 : ℝ) - Real.pi * Real.exp (369 / 800 : ℝ)) ≤
      (2 / (324863281853 / 2500000000 : ℝ) : ℝ) := by
    rw [show (37 / 320 : ℝ) - Real.pi * Real.exp (369 / 800 : ℝ) =
      -(Real.pi * Real.exp (369 / 800 : ℝ) - (37 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12472431492352923 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (12472431492352923 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell369_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (369 / 1600 : ℝ) (37 / 160 : ℝ)) :
    (1061390761 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2148870601 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell369_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell369_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell370_leftExp :
    (7940195621 / 5000000000 : ℝ) ≤ Real.exp (37 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (37 / 80 : ℝ) (507279038213 / 500000000000 : ℝ)
    (7940195621 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell370_rightExp :
    Real.exp (371 / 800 : ℝ) ≤ (3180050829 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (371 / 800 : ℝ) (126824713547 / 125000000000 : ℝ)
    (3180050829 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell370_denomUpper :
    Real.exp (9759175424030597 / 2000000000000000 : ℝ) ≤ (1315764053307 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9759175424030597 / 2000000000000000 : ℝ) (23294549113 /
    20000000000 : ℝ) (1315764053307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell370_denomLower :
    (1307168467 / 10000000 : ℝ) ≤ Real.exp (3045645942671079 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3045645942671079 / 625000000000000 : ℝ) (1164488921921 /
    1000000000000 : ℝ) (1307168467 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell370_product_lower :
    (3118106880171079 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (37 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell370_leftExp
    (by norm_num : (0 : ℝ) ≤ (7940195621 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell370_product_upper :
    Real.pi * Real.exp (371 / 800 : ℝ) ≤ (9990425424030597 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell370_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell370_endpointLower :
    (1058328059 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 160 : ℝ) (371 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3118106880171079 / 625000000000000 : ℝ) (Real.pi * Real.exp (37 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell370_product_lower
  have hD : Real.exp (Real.pi * Real.exp (371 / 800 : ℝ) - (37 / 320 : ℝ)) ≤
      (1315764053307 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell370_denomUpper
    linarith [hpThetaJensenCell370_product_upper]
  have hi : (1 / (1315764053307 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (371 / 800 : ℝ) - (37 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1315764053307 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1315764053307 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((37 / 320 : ℝ) - Real.pi * Real.exp (371 / 800 : ℝ)) := by
    rw [show (37 / 320 : ℝ) - Real.pi * Real.exp (371 / 800 : ℝ) =
      -(Real.pi * Real.exp (371 / 800 : ℝ) - (37 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (37 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (37 / 80 : ℝ)) := by
    have h := hpThetaJensenCell370_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1315764053307 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell370_endpointUpper :
    hpThetaJensenKernelEndpointUpper (37 / 160 : ℝ) (371 / 1600 : ℝ) ≤ (10713422823 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (371 / 800 : ℝ)) (9990425424030597 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (371 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell370_product_upper
  have hD : (1307168467 / 10000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (37 / 80 : ℝ) - (371 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell370_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell370_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (37 / 80 : ℝ) - (371 / 3200 : ℝ)) ≤
      (1 / (1307168467 / 10000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1307168467 / 10000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((371 / 3200 : ℝ) - Real.pi * Real.exp (37 / 80 : ℝ)) ≤
      (2 / (1307168467 / 10000000 : ℝ) : ℝ) := by
    rw [show (371 / 3200 : ℝ) - Real.pi * Real.exp (37 / 80 : ℝ) =
      -(Real.pi * Real.exp (37 / 80 : ℝ) - (371 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9990425424030597 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (9990425424030597 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell370_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (37 / 160 : ℝ) (371 / 1600 : ℝ)) :
    (1058328059 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10713422823 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell370_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell370_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell371_leftExp :
    (15900254143 / 10000000000 : ℝ) ≤ Real.exp (371 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (371 / 800 : ℝ) (8116781667 / 8000000000 : ℝ)
    (15900254143 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell371_rightExp :
    Real.exp (93 / 200 : ℝ) ≤ (15920141889 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (93 / 200 : ℝ) (1014637341873 / 1000000000000 : ℝ)
    (15920141889 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell371_denomUpper :
    Real.exp (48855231317489177 / 10000000000000000 : ℝ) ≤ (661798443923 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (48855231317489177 / 10000000000000000 : ℝ) (116494351151
    / 100000000000 : ℝ) (661798443923 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell371_denomLower :
    (657469933027 / 5000000000 : ℝ) ≤ Real.exp (6098701401701957 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6098701401701957 / 1250000000000000 : ℝ) (1164704649393
    / 1000000000000 : ℝ) (657469933027 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell371_product_lower :
    (6244013901701957 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (371 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell371_leftExp
    (by norm_num : (0 : ℝ) ≤ (15900254143 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell371_product_upper :
    Real.pi * Real.exp (93 / 200 : ℝ) ≤ (50014606317489177 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell371_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell371_endpointLower :
    (10552649451 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (371 / 1600 : ℝ) (93 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6244013901701957 / 1250000000000000 : ℝ) (Real.pi * Real.exp (371 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell371_product_lower
  have hD : Real.exp (Real.pi * Real.exp (93 / 200 : ℝ) - (371 / 3200 : ℝ)) ≤
      (661798443923 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell371_denomUpper
    linarith [hpThetaJensenCell371_product_upper]
  have hi : (1 / (661798443923 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (93 / 200 : ℝ) - (371 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (661798443923 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (661798443923 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((371 / 3200 : ℝ) - Real.pi * Real.exp (93 / 200 : ℝ)) := by
    rw [show (371 / 3200 : ℝ) - Real.pi * Real.exp (93 / 200 : ℝ) =
      -(Real.pi * Real.exp (93 / 200 : ℝ) - (371 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (371 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (371 / 800 : ℝ)) := by
    have h := hpThetaJensenCell371_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (661798443923 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell371_endpointUpper :
    hpThetaJensenKernelEndpointUpper (371 / 1600 : ℝ) (93 / 400 : ℝ) ≤ (5341244083 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (93 / 200 : ℝ)) (50014606317489177 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (93 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell371_product_upper
  have hD : (657469933027 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (371 / 800 : ℝ) - (93 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell371_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell371_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (371 / 800 : ℝ) - (93 / 800 : ℝ)) ≤
      (1 / (657469933027 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (657469933027 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((93 / 800 : ℝ) - Real.pi * Real.exp (371 / 800 : ℝ)) ≤
      (2 / (657469933027 / 5000000000 : ℝ) : ℝ) := by
    rw [show (93 / 800 : ℝ) - Real.pi * Real.exp (371 / 800 : ℝ) =
      -(Real.pi * Real.exp (371 / 800 : ℝ) - (93 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50014606317489177 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50014606317489177 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell371_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (371 / 1600 : ℝ) (93 / 400 : ℝ)) :
    (10552649451 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5341244083 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell371_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell371_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell372_leftExp :
    (248752217 / 156250000 : ℝ) ≤ Real.exp (93 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (93 / 200 : ℝ) (63414833867 / 62500000000 : ℝ) (248752217
    / 156250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell372_rightExp :
    Real.exp (373 / 800 : ℝ) ≤ (1594005451 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (373 / 800 : ℝ) (1014676976919 / 1000000000000 : ℝ)
    (1594005451 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell372_denomUpper :
    Real.exp (4891466366823443 / 1000000000000000 : ℝ) ≤ (665743378861 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4891466366823443 / 1000000000000000 : ℝ) (1165159892013
    / 1000000000000 : ℝ) (665743378861 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell372_denomLower :
    (330691947979 / 2500000000 : ℝ) ≤ Real.exp (47704067767779 / 9765625000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47704067767779 / 9765625000000 : ℝ) (1164920700961 /
    1000000000000 : ℝ) (330691947979 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell372_product_lower :
    (97684746863683 / 19531250000000 : ℝ) ≤ Real.pi * Real.exp (93 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell372_leftExp
    (by norm_num : (0 : ℝ) ≤ (248752217 / 156250000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell372_product_upper :
    Real.pi * Real.exp (373 / 800 : ℝ) ≤ (5007716366823443 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell372_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell372_endpointLower :
    (210440293 / 200000000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 400 : ℝ) (373 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (97684746863683 / 19531250000000 : ℝ) (Real.pi * Real.exp (93 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell372_product_lower
  have hD : Real.exp (Real.pi * Real.exp (373 / 800 : ℝ) - (93 / 800 : ℝ)) ≤
      (665743378861 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell372_denomUpper
    linarith [hpThetaJensenCell372_product_upper]
  have hi : (1 / (665743378861 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (373 / 800 : ℝ) - (93 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (665743378861 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (665743378861 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((93 / 800 : ℝ) - Real.pi * Real.exp (373 / 800 : ℝ)) := by
    rw [show (93 / 800 : ℝ) - Real.pi * Real.exp (373 / 800 : ℝ) =
      -(Real.pi * Real.exp (373 / 800 : ℝ) - (93 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (93 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (93 / 200 : ℝ)) := by
    have h := hpThetaJensenCell372_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (665743378861 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell372_endpointUpper :
    hpThetaJensenKernelEndpointUpper (93 / 400 : ℝ) (373 / 1600 : ℝ) ≤ (2130309903 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (373 / 800 : ℝ)) (5007716366823443 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (373 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell372_product_upper
  have hD : (330691947979 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (93 / 200 : ℝ) - (373 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell372_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell372_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (93 / 200 : ℝ) - (373 / 3200 : ℝ)) ≤
      (1 / (330691947979 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (330691947979 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((373 / 3200 : ℝ) - Real.pi * Real.exp (93 / 200 : ℝ)) ≤
      (2 / (330691947979 / 2500000000 : ℝ) : ℝ) := by
    rw [show (373 / 3200 : ℝ) - Real.pi * Real.exp (93 / 200 : ℝ) =
      -(Real.pi * Real.exp (93 / 200 : ℝ) - (373 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (5007716366823443 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (5007716366823443 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell372_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (93 / 400 : ℝ) (373 / 1600 : ℝ)) :
    (210440293 / 200000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2130309903 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell372_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell372_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell373_leftExp :
    (3985013627 / 2500000000 : ℝ) ≤ Real.exp (373 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (373 / 800 : ℝ) (507338488459 / 500000000000 : ℝ)
    (3985013627 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell373_rightExp :
    Real.exp (187 / 400 : ℝ) ≤ (3989998009 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (187 / 400 : ℝ) (126839576689 / 125000000000 : ℝ)
    (3989998009 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell373_denomUpper :
    Real.exp (12243543565088337 / 2500000000000000 : ℝ) ≤ (1339434138489 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (12243543565088337 / 2500000000000000 : ℝ) (72836037353 /
    62500000000 : ℝ) (1339434138489 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell373_denomLower :
    (1330652716571 / 10000000000 : ℝ) ≤ Real.exp (1528387428809273 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1528387428809273 / 312500000000000 : ℝ) (145642134643 /
    125000000000 : ℝ) (1330652716571 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell373_product_lower :
    (1564910866309273 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (373 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell373_leftExp
    (by norm_num : (0 : ℝ) ≤ (3985013627 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell373_product_upper :
    Real.pi * Real.exp (187 / 400 : ℝ) ≤ (12534949815088337 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell373_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell373_endpointLower :
    (2098275333 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (373 / 1600 : ℝ) (187 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1564910866309273 / 312500000000000 : ℝ) (Real.pi * Real.exp (373 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell373_product_lower
  have hD : Real.exp (Real.pi * Real.exp (187 / 400 : ℝ) - (373 / 3200 : ℝ)) ≤
      (1339434138489 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell373_denomUpper
    linarith [hpThetaJensenCell373_product_upper]
  have hi : (1 / (1339434138489 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (187 / 400 : ℝ) - (373 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1339434138489 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1339434138489 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((373 / 3200 : ℝ) - Real.pi * Real.exp (187 / 400 : ℝ)) := by
    rw [show (373 / 3200 : ℝ) - Real.pi * Real.exp (187 / 400 : ℝ) =
      -(Real.pi * Real.exp (187 / 400 : ℝ) - (373 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (373 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (373 / 800 : ℝ)) := by
    have h := hpThetaJensenCell373_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1339434138489 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell373_endpointUpper :
    hpThetaJensenKernelEndpointUpper (373 / 1600 : ℝ) (187 / 800 : ℝ) ≤ (5310303669 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (187 / 400 : ℝ)) (12534949815088337 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (187 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell373_product_upper
  have hD : (1330652716571 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (373 / 800 : ℝ) - (187 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell373_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell373_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (373 / 800 : ℝ) - (187 / 1600 : ℝ)) ≤
      (1 / (1330652716571 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1330652716571 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((187 / 1600 : ℝ) - Real.pi * Real.exp (373 / 800 : ℝ)) ≤
      (2 / (1330652716571 / 10000000000 : ℝ) : ℝ) := by
    rw [show (187 / 1600 : ℝ) - Real.pi * Real.exp (373 / 800 : ℝ) =
      -(Real.pi * Real.exp (373 / 800 : ℝ) - (187 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12534949815088337 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (12534949815088337 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell373_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (373 / 1600 : ℝ) (187 / 800 : ℝ)) :
    (2098275333 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5310303669 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell373_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell373_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell374_leftExp :
    (3191998407 / 2000000000 : ℝ) ≤ Real.exp (187 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (187 / 400 : ℝ) (1014716613511 / 1000000000000 : ℝ)
    (3191998407 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell374_rightExp :
    Real.exp (15 / 32 : ℝ) ≤ (31959909 / 20000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (15 / 32 : ℝ) (507378125827 / 500000000000 : ℝ)
    (31959909 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell374_denomUpper :
    Real.exp (98067526395037 / 20000000000000 : ℝ) ≤ (269487902409 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (98067526395037 / 20000000000000 : ℝ) (1165593628957 /
    1000000000000 : ℝ) (269487902409 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell374_denomLower :
    (1338595116843 / 10000000000 : ℝ) ≤ Real.exp (1224197707430493 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1224197707430493 / 250000000000000 : ℝ) (582676889237 /
    500000000000 : ℝ) (1338595116843 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell374_product_lower :
    (1253494582430493 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (187 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell374_leftExp
    (by norm_num : (0 : ℝ) ≤ (3191998407 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell374_product_upper :
    Real.pi * Real.exp (15 / 32 : ℝ) ≤ (100405026395037 / 20000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell374_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell374_endpointLower :
    (10460735959 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (187 / 800 : ℝ) (15 / 64 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1253494582430493 / 250000000000000 : ℝ) (Real.pi * Real.exp (187 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell374_product_lower
  have hD : Real.exp (Real.pi * Real.exp (15 / 32 : ℝ) - (187 / 1600 : ℝ)) ≤
      (269487902409 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell374_denomUpper
    linarith [hpThetaJensenCell374_product_upper]
  have hi : (1 / (269487902409 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (15 / 32 : ℝ) - (187 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (269487902409 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (269487902409 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((187 / 1600 : ℝ) - Real.pi * Real.exp (15 / 32 : ℝ)) := by
    rw [show (187 / 1600 : ℝ) - Real.pi * Real.exp (15 / 32 : ℝ) =
      -(Real.pi * Real.exp (15 / 32 : ℝ) - (187 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (187 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (187 / 400 : ℝ)) := by
    have h := hpThetaJensenCell374_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (269487902409 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell374_endpointUpper :
    hpThetaJensenKernelEndpointUpper (187 / 800 : ℝ) (15 / 64 : ℝ) ≤ (10589662107 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (15 / 32 : ℝ)) (100405026395037 / 20000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (15 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell374_product_upper
  have hD : (1338595116843 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (187 / 400 : ℝ) - (15 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell374_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell374_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (187 / 400 : ℝ) - (15 / 128 : ℝ)) ≤
      (1 / (1338595116843 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1338595116843 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((15 / 128 : ℝ) - Real.pi * Real.exp (187 / 400 : ℝ)) ≤
      (2 / (1338595116843 / 10000000000 : ℝ) : ℝ) := by
    rw [show (15 / 128 : ℝ) - Real.pi * Real.exp (187 / 400 : ℝ) =
      -(Real.pi * Real.exp (187 / 400 : ℝ) - (15 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (100405026395037 / 20000000000000 : ℝ) ^ 2 - 6 *
      (100405026395037 / 20000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell374_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (187 / 800 : ℝ) (15 / 64 : ℝ)) :
    (10460735959 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10589662107 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell374_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell374_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell375_leftExp :
    (15979954499 / 10000000000 : ℝ) ≤ Real.exp (15 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (15 / 32 : ℝ) (1014756251653 / 1000000000000 : ℝ)
    (15979954499 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell375_rightExp :
    Real.exp (47 / 100 : ℝ) ≤ (15999941933 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47 / 100 : ℝ) (63424743209 / 62500000000 : ℝ)
    (15999941933 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell375_denomUpper :
    Real.exp (49093430577119269 / 10000000000000000 : ℝ) ≤ (169437920507 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49093430577119269 / 10000000000000000 : ℝ)
    (1165810986463 / 1000000000000 : ℝ) (169437920507 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell375_denomLower :
    (1346595473159 / 10000000000 : ℝ) ≤ Real.exp (6128437151802801 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6128437151802801 / 1250000000000000 : ℝ) (1165570805461
    / 1000000000000 : ℝ) (1346595473159 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell375_product_lower :
    (6275312151802801 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (15 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell375_leftExp
    (by norm_num : (0 : ℝ) ≤ (15979954499 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell375_product_upper :
    Real.pi * Real.exp (47 / 100 : ℝ) ≤ (50265305577119269 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell375_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell375_endpointLower :
    (5215046499 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (15 / 64 : ℝ) (47 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6275312151802801 / 1250000000000000 : ℝ) (Real.pi * Real.exp (15 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell375_product_lower
  have hD : Real.exp (Real.pi * Real.exp (47 / 100 : ℝ) - (15 / 128 : ℝ)) ≤
      (169437920507 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell375_denomUpper
    linarith [hpThetaJensenCell375_product_upper]
  have hi : (1 / (169437920507 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (47 / 100 : ℝ) - (15 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (169437920507 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (169437920507 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((15 / 128 : ℝ) - Real.pi * Real.exp (47 / 100 : ℝ)) := by
    rw [show (15 / 128 : ℝ) - Real.pi * Real.exp (47 / 100 : ℝ) =
      -(Real.pi * Real.exp (47 / 100 : ℝ) - (15 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (15 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (15 / 32 : ℝ)) := by
    have h := hpThetaJensenCell375_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (169437920507 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell375_endpointUpper :
    hpThetaJensenKernelEndpointUpper (15 / 64 : ℝ) (47 / 200 : ℝ) ≤ (10558714297 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (47 / 100 : ℝ)) (50265305577119269 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (47 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell375_product_upper
  have hD : (1346595473159 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (15 / 32 : ℝ) - (47 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell375_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell375_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (15 / 32 : ℝ) - (47 / 400 : ℝ)) ≤
      (1 / (1346595473159 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1346595473159 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((47 / 400 : ℝ) - Real.pi * Real.exp (15 / 32 : ℝ)) ≤
      (2 / (1346595473159 / 10000000000 : ℝ) : ℝ) := by
    rw [show (47 / 400 : ℝ) - Real.pi * Real.exp (15 / 32 : ℝ) =
      -(Real.pi * Real.exp (15 / 32 : ℝ) - (47 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50265305577119269 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50265305577119269 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell375_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (15 / 64 : ℝ) (47 / 200 : ℝ)) :
    (5215046499 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10558714297 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell375_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell375_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell376_leftExp :
    (15999941931 / 10000000000 : ℝ) ≤ Real.exp (47 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (47 / 100 : ℝ) (1014795891343 / 1000000000000 : ℝ)
    (15999941931 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell376_rightExp :
    Real.exp (377 / 800 : ℝ) ≤ (3203990873 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (377 / 800 : ℝ) (1014835532583 / 1000000000000 : ℝ)
    (3203990873 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell376_denomUpper :
    Real.exp (9830635298680689 / 2000000000000000 : ℝ) ≤ (681813092099 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9830635298680689 / 2000000000000000 : ℝ) (291507167669 /
    250000000000 : ℝ) (681813092099 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell376_denomLower :
    (270930854167 / 2000000000 : ℝ) ≤ Real.exp (6135895571361769 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (6135895571361769 / 1250000000000000 : ℝ) (1165788158627
    / 1000000000000 : ℝ) (270930854167 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell376_product_lower :
    (6283161196361769 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (47 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell376_leftExp
    (by norm_num : (0 : ℝ) ≤ (15999941931 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell376_product_upper :
    Real.pi * Real.exp (377 / 800 : ℝ) ≤ (10065635298680689 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell376_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell376_endpointLower :
    (10399448251 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 200 : ℝ) (377 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6283161196361769 / 1250000000000000 : ℝ) (Real.pi * Real.exp (47 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell376_product_lower
  have hD : Real.exp (Real.pi * Real.exp (377 / 800 : ℝ) - (47 / 400 : ℝ)) ≤
      (681813092099 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell376_denomUpper
    linarith [hpThetaJensenCell376_product_upper]
  have hi : (1 / (681813092099 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (377 / 800 : ℝ) - (47 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (681813092099 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (681813092099 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((47 / 400 : ℝ) - Real.pi * Real.exp (377 / 800 : ℝ)) := by
    rw [show (47 / 400 : ℝ) - Real.pi * Real.exp (377 / 800 : ℝ) =
      -(Real.pi * Real.exp (377 / 800 : ℝ) - (47 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (47 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (47 / 100 : ℝ)) := by
    have h := hpThetaJensenCell376_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (681813092099 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell376_endpointUpper :
    hpThetaJensenKernelEndpointUpper (47 / 200 : ℝ) (377 / 1600 : ℝ) ≤ (10527764377 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (377 / 800 : ℝ)) (10065635298680689 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (377 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell376_product_upper
  have hD : (270930854167 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (47 / 100 : ℝ) - (377 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell376_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell376_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (47 / 100 : ℝ) - (377 / 3200 : ℝ)) ≤
      (1 / (270930854167 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (270930854167 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((377 / 3200 : ℝ) - Real.pi * Real.exp (47 / 100 : ℝ)) ≤
      (2 / (270930854167 / 2000000000 : ℝ) : ℝ) := by
    rw [show (377 / 3200 : ℝ) - Real.pi * Real.exp (47 / 100 : ℝ) =
      -(Real.pi * Real.exp (47 / 100 : ℝ) - (377 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10065635298680689 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (10065635298680689 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell376_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (47 / 200 : ℝ) (377 / 1600 : ℝ)) :
    (10399448251 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10527764377 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell376_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell376_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell377_leftExp :
    (4004988591 / 2500000000 : ℝ) ≤ Real.exp (377 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (377 / 800 : ℝ) (507417766291 / 500000000000 : ℝ)
    (4004988591 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell377_rightExp :
    Real.exp (189 / 400 : ℝ) ≤ (16039991829 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (189 / 400 : ℝ) (101487517537 / 100000000000 : ℝ)
    (16039991829 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell377_denomUpper :
    Real.exp (49213001050043597 / 10000000000000000 : ℝ) ≤ (1371808468079 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (49213001050043597 / 10000000000000000 : ℝ)
    (1166246682143 / 1000000000000 : ℝ) (1371808468079 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell377_denomLower :
    (340693000127 / 2500000000 : ℝ) ≤ Real.exp (1535840952197109 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1535840952197109 / 312500000000000 : ℝ) (291501459629 /
    250000000000 : ℝ) (340693000127 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell377_product_lower :
    (1572755014697109 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (377 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell377_leftExp
    (by norm_num : (0 : ℝ) ≤ (4004988591 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell377_product_upper :
    Real.pi * Real.exp (189 / 400 : ℝ) ≤ (50391126050043597 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell377_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell377_endpointLower :
    (10368802179 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (377 / 1600 : ℝ) (189 / 800 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1572755014697109 / 312500000000000 : ℝ) (Real.pi * Real.exp (377 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell377_product_lower
  have hD : Real.exp (Real.pi * Real.exp (189 / 400 : ℝ) - (377 / 3200 : ℝ)) ≤
      (1371808468079 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell377_denomUpper
    linarith [hpThetaJensenCell377_product_upper]
  have hi : (1 / (1371808468079 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (189 / 400 : ℝ) - (377 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1371808468079 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1371808468079 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((377 / 3200 : ℝ) - Real.pi * Real.exp (189 / 400 : ℝ)) := by
    rw [show (377 / 3200 : ℝ) - Real.pi * Real.exp (189 / 400 : ℝ) =
      -(Real.pi * Real.exp (189 / 400 : ℝ) - (377 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (377 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (377 / 800 : ℝ)) := by
    have h := hpThetaJensenCell377_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1371808468079 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell377_endpointUpper :
    hpThetaJensenKernelEndpointUpper (377 / 1600 : ℝ) (189 / 800 : ℝ) ≤ (10496812813 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (189 / 400 : ℝ)) (50391126050043597 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (189 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell377_product_upper
  have hD : (340693000127 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (377 / 800 : ℝ) - (189 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell377_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell377_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (377 / 800 : ℝ) - (189 / 1600 : ℝ)) ≤
      (1 / (340693000127 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (340693000127 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((189 / 1600 : ℝ) - Real.pi * Real.exp (377 / 800 : ℝ)) ≤
      (2 / (340693000127 / 2500000000 : ℝ) : ℝ) := by
    rw [show (189 / 1600 : ℝ) - Real.pi * Real.exp (377 / 800 : ℝ) =
      -(Real.pi * Real.exp (377 / 800 : ℝ) - (189 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (50391126050043597 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (50391126050043597 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell377_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (377 / 1600 : ℝ) (189 / 800 : ℝ)) :
    (10368802179 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (10496812813 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell377_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell377_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell378_leftExp :
    (4009997957 / 2500000000 : ℝ) ≤ Real.exp (189 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (189 / 400 : ℝ) (1014875175369 / 1000000000000 : ℝ)
    (4009997957 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell378_rightExp :
    Real.exp (379 / 800 : ℝ) ≤ (3212010871 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (379 / 800 : ℝ) (507457409853 / 500000000000 : ℝ)
    (3212010871 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell378_denomUpper :
    Real.exp (9854580868257503 / 2000000000000000 : ℝ) ≤ (1380050714517 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9854580868257503 / 2000000000000000 : ℝ) (583232510687 /
    500000000000 : ℝ) (1380050714517 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell378_denomLower :
    (137094915617 / 1000000000 : ℝ) ≤ Real.exp (1537710468965943 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1537710468965943 / 312500000000000 : ℝ) (29155596141 /
    25000000000 : ℝ) (137094915617 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell378_product_lower :
    (1574722187715943 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (189 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell378_leftExp
    (by norm_num : (0 : ℝ) ≤ (4009997957 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell378_product_upper :
    Real.pi * Real.exp (379 / 800 : ℝ) ≤ (10090830868257503 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell378_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell378_endpointLower :
    (10338155251 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (189 / 800 : ℝ) (379 / 1600 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1574722187715943 / 312500000000000 : ℝ) (Real.pi * Real.exp (189 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell378_product_lower
  have hD : Real.exp (Real.pi * Real.exp (379 / 800 : ℝ) - (189 / 1600 : ℝ)) ≤
      (1380050714517 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell378_denomUpper
    linarith [hpThetaJensenCell378_product_upper]
  have hi : (1 / (1380050714517 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (379 / 800 : ℝ) - (189 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1380050714517 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1380050714517 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((189 / 1600 : ℝ) - Real.pi * Real.exp (379 / 800 : ℝ)) := by
    rw [show (189 / 1600 : ℝ) - Real.pi * Real.exp (379 / 800 : ℝ) =
      -(Real.pi * Real.exp (379 / 800 : ℝ) - (189 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (189 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (189 / 400 : ℝ)) := by
    have h := hpThetaJensenCell378_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1380050714517 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell378_endpointUpper :
    hpThetaJensenKernelEndpointUpper (189 / 800 : ℝ) (379 / 1600 : ℝ) ≤ (2616465019 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (379 / 800 : ℝ)) (10090830868257503 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (379 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell378_product_upper
  have hD : (137094915617 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (189 / 400 : ℝ) - (379 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell378_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell378_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (189 / 400 : ℝ) - (379 / 3200 : ℝ)) ≤
      (1 / (137094915617 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (137094915617 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((379 / 3200 : ℝ) - Real.pi * Real.exp (189 / 400 : ℝ)) ≤
      (2 / (137094915617 / 1000000000 : ℝ) : ℝ) := by
    rw [show (379 / 3200 : ℝ) - Real.pi * Real.exp (189 / 400 : ℝ) =
      -(Real.pi * Real.exp (189 / 400 : ℝ) - (379 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (10090830868257503 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (10090830868257503 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell378_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (189 / 800 : ℝ) (379 / 1600 : ℝ)) :
    (10338155251 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (2616465019 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell378_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell378_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell379_leftExp :
    (8030027177 / 5000000000 : ℝ) ≤ Real.exp (379 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (379 / 800 : ℝ) (202982963941 / 200000000000 : ℝ)
    (8030027177 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell379_rightExp :
    Real.exp (19 / 40 : ℝ) ≤ (2010017747 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19 / 40 : ℝ) (1014954465591 / 1000000000000 : ℝ)
    (2010017747 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell379_denomUpper :
    Real.exp (6166610808850971 / 1250000000000000 : ℝ) ≤ (347088357111 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (6166610808850971 / 1250000000000000 : ℝ) (583341844459 /
    500000000000 : ℝ) (347088357111 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell379_denomLower :
    (1379186236849 / 10000000000 : ℝ) ≤ Real.exp (3079164892380723 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (3079164892380723 / 625000000000000 : ℝ) (1166442180523 /
    1000000000000 : ℝ) (1379186236849 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell379_product_lower :
    (3153383642380723 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (379 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell379_leftExp
    (by norm_num : (0 : ℝ) ≤ (8030027177 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell379_product_upper :
    Real.pi * Real.exp (19 / 40 : ℝ) ≤ (6314657683850971 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell379_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell379_endpointLower :
    (10307507921 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (379 / 1600 : ℝ) (19 / 80 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3153383642380723 / 625000000000000 : ℝ) (Real.pi * Real.exp (379 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell379_product_lower
  have hD : Real.exp (Real.pi * Real.exp (19 / 40 : ℝ) - (379 / 3200 : ℝ)) ≤
      (347088357111 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell379_denomUpper
    linarith [hpThetaJensenCell379_product_upper]
  have hi : (1 / (347088357111 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (19 / 40 : ℝ) - (379 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (347088357111 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (347088357111 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((379 / 3200 : ℝ) - Real.pi * Real.exp (19 / 40 : ℝ)) := by
    rw [show (379 / 3200 : ℝ) - Real.pi * Real.exp (19 / 40 : ℝ) =
      -(Real.pi * Real.exp (19 / 40 : ℝ) - (379 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (379 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (379 / 800 : ℝ)) := by
    have h := hpThetaJensenCell379_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (347088357111 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell379_endpointUpper :
    hpThetaJensenKernelEndpointUpper (379 / 1600 : ℝ) (19 / 80 : ℝ) ≤ (5217453319 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (19 / 40 : ℝ)) (6314657683850971 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (19 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell379_product_upper
  have hD : (1379186236849 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (379 / 800 : ℝ) - (19 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell379_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell379_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (379 / 800 : ℝ) - (19 / 160 : ℝ)) ≤
      (1 / (1379186236849 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1379186236849 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((19 / 160 : ℝ) - Real.pi * Real.exp (379 / 800 : ℝ)) ≤
      (2 / (1379186236849 / 10000000000 : ℝ) : ℝ) := by
    rw [show (19 / 160 : ℝ) - Real.pi * Real.exp (379 / 800 : ℝ) =
      -(Real.pi * Real.exp (379 / 800 : ℝ) - (19 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (6314657683850971 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (6314657683850971 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell379_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (379 / 1600 : ℝ) (19 / 80 : ℝ)) :
    (10307507921 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (5217453319 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell379_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell379_endpointUpper

def hpThetaJensenCellsBatch018Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1088928743 / 1000000000 : ℝ)
  | 1 => (5429359377 / 5000000000 : ℝ)
  | 2 => (1353517713 / 1250000000 : ℝ)
  | 3 => (10797556749 / 10000000000 : ℝ)
  | 4 => (10766964369 / 10000000000 : ℝ)
  | 5 => (10736365033 / 10000000000 : ℝ)
  | 6 => (5352879609 / 5000000000 : ℝ)
  | 7 => (83399589 / 78125000 : ℝ)
  | 8 => (5322265017 / 5000000000 : ℝ)
  | 9 => (1061390761 / 1000000000 : ℝ)
  | 10 => (1058328059 / 1000000000 : ℝ)
  | 11 => (10552649451 / 10000000000 : ℝ)
  | 12 => (210440293 / 200000000 : ℝ)
  | 13 => (2098275333 / 2000000000 : ℝ)
  | 14 => (10460735959 / 10000000000 : ℝ)
  | 15 => (5215046499 / 5000000000 : ℝ)
  | 16 => (10399448251 / 10000000000 : ℝ)
  | 17 => (10368802179 / 10000000000 : ℝ)
  | 18 => (10338155251 / 10000000000 : ℝ)
  | 19 => (10307507921 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch018Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11022444979 / 10000000000 : ℝ)
  | 1 => (10991576463 / 10000000000 : ℝ)
  | 2 => (548034959 / 500000000 : ℝ)
  | 3 => (2732453403 / 2500000000 : ℝ)
  | 4 => (2724730059 / 2500000000 : ℝ)
  | 5 => (679251221 / 625000000 : ℝ)
  | 6 => (2167422397 / 2000000000 : ℝ)
  | 7 => (10806198063 / 10000000000 : ℝ)
  | 8 => (2155055649 / 2000000000 : ℝ)
  | 9 => (2148870601 / 2000000000 : ℝ)
  | 10 => (10713422823 / 10000000000 : ℝ)
  | 11 => (5341244083 / 5000000000 : ℝ)
  | 12 => (2130309903 / 2000000000 : ℝ)
  | 13 => (5310303669 / 5000000000 : ℝ)
  | 14 => (10589662107 / 10000000000 : ℝ)
  | 15 => (10558714297 / 10000000000 : ℝ)
  | 16 => (10527764377 / 10000000000 : ℝ)
  | 17 => (10496812813 / 10000000000 : ℝ)
  | 18 => (2616465019 / 2500000000 : ℝ)
  | 19 => (5217453319 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch018_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch018Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch018Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell360_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell361_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell362_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell363_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell364_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell365_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell366_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell367_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell368_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell369_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell370_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell371_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell372_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell373_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell374_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell375_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell376_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell377_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell378_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell379_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper] at h ⊢
    exact h

end HodgeProofHP
