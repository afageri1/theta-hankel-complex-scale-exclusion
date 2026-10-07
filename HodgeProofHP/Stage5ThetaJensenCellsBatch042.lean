import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell840_leftExp :
    (28576511179 / 10000000000 : ℝ) ≤ Real.exp (21 / 20 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 20 : ℝ) (1033356766681 / 1000000000000 : ℝ)
    (28576511179 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell840_rightExp :
    Real.exp (841 / 800 : ℝ) ≤ (7153063539 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (841 / 800 : ℝ) (103339713297 / 100000000000 : ℝ)
    (7153063539 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell840_denomUpper :
    Real.exp (21815764342677627 / 2500000000000000 : ℝ) ≤ (30814592816739 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21815764342677627 / 2500000000000000 : ℝ) (65675113233 /
    50000000000 : ℝ) (30814592816739 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell840_denomLower :
    (60921807934597 / 10000000000 : ℝ) ≤ Real.exp (10893451738482121 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10893451738482121 / 1250000000000000 : ℝ) (82064280623 /
    62500000000 : ℝ) (60921807934597 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell840_product_lower :
    (11221967363482121 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 20 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell840_leftExp
    (by norm_num : (0 : ℝ) ≤ (28576511179 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell840_product_upper :
    Real.pi * Real.exp (841 / 800 : ℝ) ≤ (22472014342677627 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell840_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell840_endpointLower :
    (217852861 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 40 : ℝ) (841 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11221967363482121 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 20 : ℝ))
    (by norm_num) hpThetaJensenCell840_product_lower
  have hD : Real.exp (Real.pi * Real.exp (841 / 800 : ℝ) - (21 / 80 : ℝ)) ≤
      (30814592816739 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell840_denomUpper
    linarith [hpThetaJensenCell840_product_upper]
  have hi : (1 / (30814592816739 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (841 / 800 : ℝ) - (21 / 80 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (30814592816739 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (30814592816739 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 80 : ℝ) - Real.pi * Real.exp (841 / 800 : ℝ)) := by
    rw [show (21 / 80 : ℝ) - Real.pi * Real.exp (841 / 800 : ℝ) =
      -(Real.pi * Real.exp (841 / 800 : ℝ) - (21 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 20 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 20 : ℝ)) := by
    have h := hpThetaJensenCell840_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (30814592816739 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell840_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 40 : ℝ) (841 / 1600 : ℝ) ≤ (4431431 / 50000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (841 / 800 : ℝ)) (22472014342677627 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (841 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell840_product_upper
  have hD : (60921807934597 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 20 : ℝ) - (841 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell840_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell840_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 20 : ℝ) - (841 / 3200 : ℝ)) ≤
      (1 / (60921807934597 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (60921807934597 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((841 / 3200 : ℝ) - Real.pi * Real.exp (21 / 20 : ℝ)) ≤
      (2 / (60921807934597 / 10000000000 : ℝ) : ℝ) := by
    rw [show (841 / 3200 : ℝ) - Real.pi * Real.exp (21 / 20 : ℝ) =
      -(Real.pi * Real.exp (21 / 20 : ℝ) - (841 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22472014342677627 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (22472014342677627 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell840_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 40 : ℝ) (841 / 1600 : ℝ)) :
    (217852861 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4431431 / 50000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell840_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell840_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell841_leftExp :
    (14306127077 / 5000000000 : ℝ) ≤ Real.exp (841 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (841 / 800 : ℝ) (1033397132969 / 1000000000000 : ℝ)
    (14306127077 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell841_rightExp :
    Real.exp (421 / 400 : ℝ) ≤ (5729608367 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (421 / 400 : ℝ) (1033437500833 / 1000000000000 : ℝ)
    (5729608367 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell841_denomUpper :
    Real.exp (17474472538508631 / 2000000000000000 : ℝ) ≤ (62306520502293 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17474472538508631 / 2000000000000000 : ℝ) (656975503129
    / 500000000000 : ℝ) (62306520502293 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell841_denomLower :
    (12318100632617 / 2000000000 : ℝ) ≤ Real.exp (5453548672010823 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5453548672010823 / 625000000000000 : ℝ) (1313476493101 /
    1000000000000 : ℝ) (12318100632617 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell841_product_lower :
    (5618001797010823 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (841 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell841_leftExp
    (by norm_num : (0 : ℝ) ≤ (14306127077 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell841_product_upper :
    Real.pi * Real.exp (421 / 400 : ℝ) ≤ (18000097538508631 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell841_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell841_endpointLower :
    (864312399 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (841 / 1600 : ℝ) (421 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5618001797010823 / 625000000000000 : ℝ) (Real.pi * Real.exp (841 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell841_product_lower
  have hD : Real.exp (Real.pi * Real.exp (421 / 400 : ℝ) - (841 / 3200 : ℝ)) ≤
      (62306520502293 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell841_denomUpper
    linarith [hpThetaJensenCell841_product_upper]
  have hi : (1 / (62306520502293 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (421 / 400 : ℝ) - (841 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (62306520502293 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (62306520502293 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((841 / 3200 : ℝ) - Real.pi * Real.exp (421 / 400 : ℝ)) := by
    rw [show (841 / 3200 : ℝ) - Real.pi * Real.exp (421 / 400 : ℝ) =
      -(Real.pi * Real.exp (421 / 400 : ℝ) - (841 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (841 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (841 / 800 : ℝ)) := by
    have h := hpThetaJensenCell841_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (62306520502293 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell841_endpointUpper :
    hpThetaJensenKernelEndpointUpper (841 / 1600 : ℝ) (421 / 800 : ℝ) ≤ (439538997 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (421 / 400 : ℝ)) (18000097538508631 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (421 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell841_product_upper
  have hD : (12318100632617 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (841 / 800 : ℝ) - (421 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell841_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell841_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (841 / 800 : ℝ) - (421 / 1600 : ℝ)) ≤
      (1 / (12318100632617 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (12318100632617 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((421 / 1600 : ℝ) - Real.pi * Real.exp (841 / 800 : ℝ)) ≤
      (2 / (12318100632617 / 2000000000 : ℝ) : ℝ) := by
    rw [show (421 / 1600 : ℝ) - Real.pi * Real.exp (841 / 800 : ℝ) =
      -(Real.pi * Real.exp (841 / 800 : ℝ) - (421 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (18000097538508631 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (18000097538508631 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell841_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (841 / 1600 : ℝ) (421 / 800 : ℝ)) :
    (864312399 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (439538997 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell841_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell841_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell842_leftExp :
    (28648041833 / 10000000000 : ℝ) ≤ Real.exp (421 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (421 / 400 : ℝ) (32294921901 / 31250000000 : ℝ)
    (28648041833 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell842_rightExp :
    Real.exp (843 / 800 : ℝ) ≤ (14341937139 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (843 / 800 : ℝ) (516738935137 / 500000000000 : ℝ)
    (14341937139 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell842_denomUpper :
    Real.exp (43740904322322427 / 5000000000000000 : ℝ) ≤ (787402318339 / 125000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43740904322322427 / 5000000000000000 : ℝ) (657200239401
    / 500000000000 : ℝ) (787402318339 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell842_denomLower :
    (6226741266901 / 1000000000 : ℝ) ≤ Real.exp (10920760504777267 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10920760504777267 / 1250000000000000 : ℝ) (1313925225747
    / 1000000000000 : ℝ) (6226741266901 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell842_product_lower :
    (11250057379777267 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (421 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell842_leftExp
    (by norm_num : (0 : ℝ) ≤ (28648041833 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell842_product_upper :
    Real.pi * Real.exp (843 / 800 : ℝ) ≤ (45056529322322427 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell842_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell842_endpointLower :
    (857258809 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (421 / 800 : ℝ) (843 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11250057379777267 / 1250000000000000 : ℝ) (Real.pi * Real.exp (421 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell842_product_lower
  have hD : Real.exp (Real.pi * Real.exp (843 / 800 : ℝ) - (421 / 1600 : ℝ)) ≤
      (787402318339 / 125000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell842_denomUpper
    linarith [hpThetaJensenCell842_product_upper]
  have hi : (1 / (787402318339 / 125000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (843 / 800 : ℝ) - (421 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (787402318339 / 125000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (787402318339 / 125000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((421 / 1600 : ℝ) - Real.pi * Real.exp (843 / 800 : ℝ)) := by
    rw [show (421 / 1600 : ℝ) - Real.pi * Real.exp (843 / 800 : ℝ) =
      -(Real.pi * Real.exp (843 / 800 : ℝ) - (421 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (421 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (421 / 400 : ℝ)) := by
    have h := hpThetaJensenCell842_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (787402318339 / 125000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell842_endpointUpper :
    hpThetaJensenKernelEndpointUpper (421 / 800 : ℝ) (843 / 1600 : ℝ) ≤ (871915841 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (843 / 800 : ℝ)) (45056529322322427 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (843 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell842_product_upper
  have hD : (6226741266901 / 1000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (421 / 400 : ℝ) - (843 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell842_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell842_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (421 / 400 : ℝ) - (843 / 3200 : ℝ)) ≤
      (1 / (6226741266901 / 1000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6226741266901 / 1000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((843 / 3200 : ℝ) - Real.pi * Real.exp (421 / 400 : ℝ)) ≤
      (2 / (6226741266901 / 1000000000 : ℝ) : ℝ) := by
    rw [show (843 / 3200 : ℝ) - Real.pi * Real.exp (421 / 400 : ℝ) =
      -(Real.pi * Real.exp (421 / 400 : ℝ) - (843 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45056529322322427 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (45056529322322427 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell842_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (421 / 800 : ℝ) (843 / 1600 : ℝ)) :
    (857258809 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (871915841 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell842_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell842_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell843_leftExp :
    (7170968569 / 2500000000 : ℝ) ≤ Real.exp (843 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (843 / 800 : ℝ) (1033477870273 / 1000000000000 : ℝ)
    (7170968569 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell843_rightExp :
    Real.exp (211 / 200 : ℝ) ≤ (1435987577 / 500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (211 / 200 : ℝ) (258379560323 / 250000000000 : ℝ)
    (1435987577 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell843_denomUpper :
    Real.exp (4379569769990161 / 500000000000000 : ℝ) ≤ (7960786586023 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4379569769990161 / 500000000000000 : ℝ) (657425341823 /
    500000000000 : ℝ) (7960786586023 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell843_denomLower :
    (31476323519097 / 5000000000 : ℝ) ≤ Real.exp (2733610311077731 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2733610311077731 / 312500000000000 : ℝ) (52574987573 /
    40000000000 : ℝ) (31476323519097 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell843_product_lower :
    (2816032186077731 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (843 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell843_leftExp
    (by norm_num : (0 : ℝ) ≤ (7170968569 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell843_product_upper :
    Real.pi * Real.exp (211 / 200 : ℝ) ≤ (4511288519990161 / 500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell843_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell843_endpointLower :
    (212562623 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (843 / 1600 : ℝ) (211 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2816032186077731 / 312500000000000 : ℝ) (Real.pi * Real.exp (843 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell843_product_lower
  have hD : Real.exp (Real.pi * Real.exp (211 / 200 : ℝ) - (843 / 3200 : ℝ)) ≤
      (7960786586023 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell843_denomUpper
    linarith [hpThetaJensenCell843_product_upper]
  have hi : (1 / (7960786586023 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (211 / 200 : ℝ) - (843 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (7960786586023 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (7960786586023 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((843 / 3200 : ℝ) - Real.pi * Real.exp (211 / 200 : ℝ)) := by
    rw [show (843 / 3200 : ℝ) - Real.pi * Real.exp (211 / 200 : ℝ) =
      -(Real.pi * Real.exp (211 / 200 : ℝ) - (843 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (843 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (843 / 800 : ℝ)) := by
    have h := hpThetaJensenCell843_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (7960786586023 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell843_endpointUpper :
    hpThetaJensenKernelEndpointUpper (843 / 1600 : ℝ) (211 / 400 : ℝ) ≤ (172959911 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (211 / 200 : ℝ)) (4511288519990161 / 500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (211 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell843_product_upper
  have hD : (31476323519097 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (843 / 800 : ℝ) - (211 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell843_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell843_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (843 / 800 : ℝ) - (211 / 800 : ℝ)) ≤
      (1 / (31476323519097 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (31476323519097 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((211 / 800 : ℝ) - Real.pi * Real.exp (843 / 800 : ℝ)) ≤
      (2 / (31476323519097 / 5000000000 : ℝ) : ℝ) := by
    rw [show (211 / 800 : ℝ) - Real.pi * Real.exp (843 / 800 : ℝ) =
      -(Real.pi * Real.exp (843 / 800 : ℝ) - (211 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4511288519990161 / 500000000000000 : ℝ) ^ 2 - 6 *
      (4511288519990161 / 500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell843_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (843 / 1600 : ℝ) (211 / 400 : ℝ)) :
    (212562623 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (172959911 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell843_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell843_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell844_leftExp :
    (14359875769 / 5000000000 : ℝ) ≤ Real.exp (211 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (211 / 200 : ℝ) (1033518241291 / 1000000000000 : ℝ)
    (14359875769 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell844_rightExp :
    Real.exp (169 / 160 : ℝ) ≤ (7188918419 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (169 / 160 : ℝ) (1033558613887 / 1000000000000 : ℝ)
    (7188918419 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell844_denomUpper :
    Real.exp (21925280782701467 / 2500000000000000 : ℝ) ≤ (64388955959729 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21925280782701467 / 2500000000000000 : ℝ) (1315301622149
    / 1000000000000 : ℝ) (64388955959729 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell844_denomLower :
    (63646318358887 / 10000000000 : ℝ) ≤ Real.exp (5474069792110531 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5474069792110531 / 625000000000000 : ℝ) (328706221297 /
    250000000000 : ℝ) (63646318358887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell844_product_lower :
    (5639108854610531 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (211 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell844_leftExp
    (by norm_num : (0 : ℝ) ≤ (14359875769 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell844_product_upper :
    Real.pi * Real.exp (169 / 160 : ℝ) ≤ (22584655782701467 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell844_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell844_endpointLower :
    (421643633 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (211 / 400 : ℝ) (169 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5639108854610531 / 625000000000000 : ℝ) (Real.pi * Real.exp (211 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell844_product_lower
  have hD : Real.exp (Real.pi * Real.exp (169 / 160 : ℝ) - (211 / 800 : ℝ)) ≤
      (64388955959729 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell844_denomUpper
    linarith [hpThetaJensenCell844_product_upper]
  have hi : (1 / (64388955959729 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (169 / 160 : ℝ) - (211 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (64388955959729 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (64388955959729 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((211 / 800 : ℝ) - Real.pi * Real.exp (169 / 160 : ℝ)) := by
    rw [show (211 / 800 : ℝ) - Real.pi * Real.exp (169 / 160 : ℝ) =
      -(Real.pi * Real.exp (169 / 160 : ℝ) - (211 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (211 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (211 / 200 : ℝ)) := by
    have h := hpThetaJensenCell844_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (64388955959729 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell844_endpointUpper :
    hpThetaJensenKernelEndpointUpper (211 / 400 : ℝ) (169 / 320 : ℝ) ≤ (107216119 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (169 / 160 : ℝ)) (22584655782701467 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (169 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell844_product_upper
  have hD : (63646318358887 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (211 / 200 : ℝ) - (169 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell844_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell844_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (211 / 200 : ℝ) - (169 / 640 : ℝ)) ≤
      (1 / (63646318358887 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (63646318358887 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((169 / 640 : ℝ) - Real.pi * Real.exp (211 / 200 : ℝ)) ≤
      (2 / (63646318358887 / 10000000000 : ℝ) : ℝ) := by
    rw [show (169 / 640 : ℝ) - Real.pi * Real.exp (211 / 200 : ℝ) =
      -(Real.pi * Real.exp (211 / 200 : ℝ) - (169 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22584655782701467 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (22584655782701467 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell844_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (211 / 400 : ℝ) (169 / 320 : ℝ)) :
    (421643633 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (107216119 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell844_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell844_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell845_leftExp :
    (14377836837 / 5000000000 : ℝ) ≤ Real.exp (169 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (169 / 160 : ℝ) (516779306943 / 500000000000 : ℝ)
    (14377836837 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell845_rightExp :
    Real.exp (423 / 400 : ℝ) ≤ (28791640743 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (423 / 400 : ℝ) (1033598988059 / 1000000000000 : ℝ)
    (28791640743 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell845_denomUpper :
    Real.exp (87810992016723599 / 10000000000000000 : ℝ) ≤ (65100290768783 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (87810992016723599 / 10000000000000000 : ℝ) (82234580981
    / 62500000000 : ℝ) (65100290768783 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell845_denomLower :
    (32174270177699 / 5000000000 : ℝ) ≤ Real.exp (5480927773053063 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5480927773053063 / 625000000000000 : ℝ) (164409476837 /
    125000000000 : ℝ) (32174270177699 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell845_product_lower :
    (5646162148053063 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (169 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell845_leftExp
    (by norm_num : (0 : ℝ) ≤ (14377836837 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell845_product_upper :
    Real.pi * Real.exp (423 / 400 : ℝ) ≤ (90451617016723599 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell845_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell845_endpointLower :
    (209092237 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (169 / 320 : ℝ) (423 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5646162148053063 / 625000000000000 : ℝ) (Real.pi * Real.exp (169 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell845_product_lower
  have hD : Real.exp (Real.pi * Real.exp (423 / 400 : ℝ) - (169 / 640 : ℝ)) ≤
      (65100290768783 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell845_denomUpper
    linarith [hpThetaJensenCell845_product_upper]
  have hi : (1 / (65100290768783 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (423 / 400 : ℝ) - (169 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65100290768783 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65100290768783 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((169 / 640 : ℝ) - Real.pi * Real.exp (423 / 400 : ℝ)) := by
    rw [show (169 / 640 : ℝ) - Real.pi * Real.exp (423 / 400 : ℝ) =
      -(Real.pi * Real.exp (423 / 400 : ℝ) - (169 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (169 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (169 / 160 : ℝ)) := by
    have h := hpThetaJensenCell845_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65100290768783 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell845_endpointUpper :
    hpThetaJensenKernelEndpointUpper (169 / 320 : ℝ) (423 / 800 : ℝ) ≤ (106337981 / 1250000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (423 / 400 : ℝ)) (90451617016723599 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (423 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell845_product_upper
  have hD : (32174270177699 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (169 / 160 : ℝ) - (423 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell845_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell845_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (169 / 160 : ℝ) - (423 / 1600 : ℝ)) ≤
      (1 / (32174270177699 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (32174270177699 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((423 / 1600 : ℝ) - Real.pi * Real.exp (169 / 160 : ℝ)) ≤
      (2 / (32174270177699 / 5000000000 : ℝ) : ℝ) := by
    rw [show (423 / 1600 : ℝ) - Real.pi * Real.exp (169 / 160 : ℝ) =
      -(Real.pi * Real.exp (169 / 160 : ℝ) - (423 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (90451617016723599 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (90451617016723599 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell845_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (169 / 320 : ℝ) (423 / 800 : ℝ)) :
    (209092237 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (106337981 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell845_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell845_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell846_leftExp :
    (28791640741 / 10000000000 : ℝ) ≤ Real.exp (423 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (423 / 400 : ℝ) (516799494029 / 500000000000 : ℝ)
    (28791640741 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell846_rightExp :
    Real.exp (847 / 800 : ℝ) ≤ (28827652797 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (847 / 800 : ℝ) (32301230119 / 31250000000 : ℝ)
    (28827652797 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell846_denomUpper :
    Real.exp (87921002233485621 / 10000000000000000 : ℝ) ≤ (8227551782959 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87921002233485621 / 10000000000000000 : ℝ)
    (1316205705661 / 1000000000000 : ℝ) (8227551782959 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell846_denomLower :
    (65059428439077 / 10000000000 : ℝ) ≤ Real.exp (10975589152349959 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (10975589152349959 / 1250000000000000 : ℝ) (20558241863 /
    15625000000 : ℝ) (65059428439077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell846_product_lower :
    (11306448527349959 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (423 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell846_leftExp
    (by norm_num : (0 : ℝ) ≤ (28791640741 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell846_product_upper :
    Real.pi * Real.exp (847 / 800 : ℝ) ≤ (90564752233485621 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell846_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell846_endpointLower :
    (165899071 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (423 / 800 : ℝ) (847 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11306448527349959 / 1250000000000000 : ℝ) (Real.pi * Real.exp (423 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell846_product_lower
  have hD : Real.exp (Real.pi * Real.exp (847 / 800 : ℝ) - (423 / 1600 : ℝ)) ≤
      (8227551782959 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell846_denomUpper
    linarith [hpThetaJensenCell846_product_upper]
  have hi : (1 / (8227551782959 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (847 / 800 : ℝ) - (423 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (8227551782959 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (8227551782959 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((423 / 1600 : ℝ) - Real.pi * Real.exp (847 / 800 : ℝ)) := by
    rw [show (423 / 1600 : ℝ) - Real.pi * Real.exp (847 / 800 : ℝ) =
      -(Real.pi * Real.exp (847 / 800 : ℝ) - (423 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (423 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (423 / 400 : ℝ)) := by
    have h := hpThetaJensenCell846_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (8227551782959 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell846_endpointUpper :
    hpThetaJensenKernelEndpointUpper (423 / 800 : ℝ) (847 / 1600 : ℝ) ≤ (421862029 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (847 / 800 : ℝ)) (90564752233485621 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (847 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell846_product_upper
  have hD : (65059428439077 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (423 / 400 : ℝ) - (847 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell846_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell846_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (423 / 400 : ℝ) - (847 / 3200 : ℝ)) ≤
      (1 / (65059428439077 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (65059428439077 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((847 / 3200 : ℝ) - Real.pi * Real.exp (423 / 400 : ℝ)) ≤
      (2 / (65059428439077 / 10000000000 : ℝ) : ℝ) := by
    rw [show (847 / 3200 : ℝ) - Real.pi * Real.exp (423 / 400 : ℝ) =
      -(Real.pi * Real.exp (423 / 400 : ℝ) - (847 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (90564752233485621 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (90564752233485621 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell846_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (423 / 800 : ℝ) (847 / 1600 : ℝ)) :
    (165899071 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (421862029 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell846_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell846_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell847_leftExp :
    (5765530559 / 2000000000 : ℝ) ≤ Real.exp (847 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (847 / 800 : ℝ) (1033639363807 / 1000000000000 : ℝ)
    (5765530559 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell847_rightExp :
    Real.exp (53 / 50 : ℝ) ≤ (28863709893 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (53 / 50 : ℝ) (516839870567 / 500000000000 : ℝ)
    (28863709893 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell847_denomUpper :
    Real.exp (88031153953879549 / 10000000000000000 : ℝ) ≤ (16637361319767 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (88031153953879549 / 10000000000000000 : ℝ)
    (1316658853407 / 1000000000000 : ℝ) (16637361319767 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell847_denomLower :
    (4111193730487 / 625000000 : ℝ) ≤ Real.exp (2197868084988741 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2197868084988741 / 250000000000000 : ℝ) (329044970043 /
    250000000000 : ℝ) (4111193730487 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell847_product_lower :
    (2264118084988741 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (847 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell847_leftExp
    (by norm_num : (0 : ℝ) ≤ (5765530559 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell847_product_upper :
    Real.pi * Real.exp (53 / 50 : ℝ) ≤ (90678028953879549 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell847_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell847_endpointLower :
    (12854161 / 156250000 : ℝ) ≤ hpThetaTraceEndpointLower (847 / 1600 : ℝ) (53 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2264118084988741 / 250000000000000 : ℝ) (Real.pi * Real.exp (847 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell847_product_lower
  have hD : Real.exp (Real.pi * Real.exp (53 / 50 : ℝ) - (847 / 3200 : ℝ)) ≤
      (16637361319767 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell847_denomUpper
    linarith [hpThetaJensenCell847_product_upper]
  have hi : (1 / (16637361319767 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (53 / 50 : ℝ) - (847 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (16637361319767 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (16637361319767 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((847 / 3200 : ℝ) - Real.pi * Real.exp (53 / 50 : ℝ)) := by
    rw [show (847 / 3200 : ℝ) - Real.pi * Real.exp (53 / 50 : ℝ) =
      -(Real.pi * Real.exp (53 / 50 : ℝ) - (847 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (847 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (847 / 800 : ℝ)) := by
    have h := hpThetaJensenCell847_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (16637361319767 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell847_endpointUpper :
    hpThetaJensenKernelEndpointUpper (847 / 1600 : ℝ) (53 / 100 : ℝ) ≤ (418394699 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (53 / 50 : ℝ)) (90678028953879549 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (53 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell847_product_upper
  have hD : (4111193730487 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (847 / 800 : ℝ) - (53 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell847_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell847_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (847 / 800 : ℝ) - (53 / 200 : ℝ)) ≤
      (1 / (4111193730487 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4111193730487 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((53 / 200 : ℝ) - Real.pi * Real.exp (847 / 800 : ℝ)) ≤
      (2 / (4111193730487 / 625000000 : ℝ) : ℝ) := by
    rw [show (53 / 200 : ℝ) - Real.pi * Real.exp (847 / 800 : ℝ) =
      -(Real.pi * Real.exp (847 / 800 : ℝ) - (53 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (90678028953879549 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (90678028953879549 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell847_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (847 / 1600 : ℝ) (53 / 100 : ℝ)) :
    (12854161 / 156250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (418394699 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell847_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell847_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell848_leftExp :
    (7215927473 / 2500000000 : ℝ) ≤ Real.exp (53 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (53 / 50 : ℝ) (1033679741133 / 1000000000000 : ℝ)
    (7215927473 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell848_rightExp :
    Real.exp (849 / 800 : ℝ) ≤ (2889981209 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (849 / 800 : ℝ) (516860060019 / 500000000000 : ℝ)
    (2889981209 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell848_denomUpper :
    Real.exp (8814144736325937 / 1000000000000000 : ℝ) ≤ (33643752236291 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8814144736325937 / 1000000000000000 : ℝ) (658556370177 /
    500000000000 : ℝ) (33643752236291 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell848_denomLower :
    (66507672882613 / 10000000000 : ℝ) ≤ Real.exp (2750777346469627 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2750777346469627 / 312500000000000 : ℝ) (329158254723 /
    250000000000 : ℝ) (66507672882613 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell848_product_lower :
    (2833687502719627 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (53 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell848_leftExp
    (by norm_num : (0 : ℝ) ≤ (7215927473 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell848_product_upper :
    Real.pi * Real.exp (849 / 800 : ℝ) ≤ (9079144736325937 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell848_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell848_endpointLower :
    (815881611 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 100 : ℝ) (849 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2833687502719627 / 312500000000000 : ℝ) (Real.pi * Real.exp (53 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell848_product_lower
  have hD : Real.exp (Real.pi * Real.exp (849 / 800 : ℝ) - (53 / 200 : ℝ)) ≤
      (33643752236291 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell848_denomUpper
    linarith [hpThetaJensenCell848_product_upper]
  have hi : (1 / (33643752236291 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (849 / 800 : ℝ) - (53 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (33643752236291 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (33643752236291 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((53 / 200 : ℝ) - Real.pi * Real.exp (849 / 800 : ℝ)) := by
    rw [show (53 / 200 : ℝ) - Real.pi * Real.exp (849 / 800 : ℝ) =
      -(Real.pi * Real.exp (849 / 800 : ℝ) - (53 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (53 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (53 / 50 : ℝ)) := by
    have h := hpThetaJensenCell848_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (33643752236291 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell848_endpointUpper :
    hpThetaJensenKernelEndpointUpper (53 / 100 : ℝ) (849 / 1600 : ℝ) ≤ (829899683 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (849 / 800 : ℝ)) (9079144736325937 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (849 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell848_product_upper
  have hD : (66507672882613 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (53 / 50 : ℝ) - (849 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell848_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell848_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (53 / 50 : ℝ) - (849 / 3200 : ℝ)) ≤
      (1 / (66507672882613 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (66507672882613 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((849 / 3200 : ℝ) - Real.pi * Real.exp (53 / 50 : ℝ)) ≤
      (2 / (66507672882613 / 10000000000 : ℝ) : ℝ) := by
    rw [show (849 / 3200 : ℝ) - Real.pi * Real.exp (53 / 50 : ℝ) =
      -(Real.pi * Real.exp (53 / 50 : ℝ) - (849 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9079144736325937 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9079144736325937 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell848_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (53 / 100 : ℝ) (849 / 1600 : ℝ)) :
    (815881611 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (829899683 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell848_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell848_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell849_leftExp :
    (28899812089 / 10000000000 : ℝ) ≤ Real.exp (849 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (849 / 800 : ℝ) (1033720120037 / 1000000000000 : ℝ)
    (28899812089 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell849_rightExp :
    Real.exp (17 / 16 : ℝ) ≤ (28935959443 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 16 : ℝ) (1033760500519 / 1000000000000 : ℝ)
    (28935959443 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell849_denomUpper :
    Real.exp (88251882634412699 / 10000000000000000 : ℝ) ≤ (68034714173163 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (88251882634412699 / 10000000000000000 : ℝ) (329391841967
    / 250000000000 : ℝ) (68034714173163 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell849_denomLower :
    (2689810742413 / 400000000 : ℝ) ≤ Real.exp (11016896057538211 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11016896057538211 / 1250000000000000 : ℝ) (82317931049 /
    62500000000 : ℝ) (2689810742413 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell849_product_lower :
    (11348927307538211 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (849 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell849_leftExp
    (by norm_num : (0 : ℝ) ≤ (28899812089 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell849_product_upper :
    Real.pi * Real.exp (17 / 16 : ℝ) ≤ (90905007634412699 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell849_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell849_endpointLower :
    (404570547 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (849 / 1600 : ℝ) (17 / 32 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11348927307538211 / 1250000000000000 : ℝ) (Real.pi * Real.exp (849 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell849_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 16 : ℝ) - (849 / 3200 : ℝ)) ≤
      (68034714173163 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell849_denomUpper
    linarith [hpThetaJensenCell849_product_upper]
  have hi : (1 / (68034714173163 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 16 : ℝ) - (849 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (68034714173163 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (68034714173163 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((849 / 3200 : ℝ) - Real.pi * Real.exp (17 / 16 : ℝ)) := by
    rw [show (849 / 3200 : ℝ) - Real.pi * Real.exp (17 / 16 : ℝ) =
      -(Real.pi * Real.exp (17 / 16 : ℝ) - (849 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (849 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (849 / 800 : ℝ)) := by
    have h := hpThetaJensenCell849_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (68034714173163 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell849_endpointUpper :
    hpThetaJensenKernelEndpointUpper (849 / 1600 : ℝ) (17 / 32 : ℝ) ≤ (102881841 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 16 : ℝ)) (90905007634412699 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 32 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell849_product_upper
  have hD : (2689810742413 / 400000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (849 / 800 : ℝ) - (17 / 64 : ℝ)) := by
    apply le_trans hpThetaJensenCell849_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell849_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (849 / 800 : ℝ) - (17 / 64 : ℝ)) ≤
      (1 / (2689810742413 / 400000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (2689810742413 / 400000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 64 : ℝ) - Real.pi * Real.exp (849 / 800 : ℝ)) ≤
      (2 / (2689810742413 / 400000000 : ℝ) : ℝ) := by
    rw [show (17 / 64 : ℝ) - Real.pi * Real.exp (849 / 800 : ℝ) =
      -(Real.pi * Real.exp (849 / 800 : ℝ) - (17 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (90905007634412699 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (90905007634412699 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell849_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (849 / 1600 : ℝ) (17 / 32 : ℝ)) :
    (404570547 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (102881841 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell849_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell849_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell850_leftExp :
    (28935959441 / 10000000000 : ℝ) ≤ Real.exp (17 / 16 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 16 : ℝ) (516880250259 / 500000000000 : ℝ)
    (28935959441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell850_rightExp :
    Real.exp (851 / 800 : ℝ) ≤ (3621519001 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (851 / 800 : ℝ) (1033800882577 / 1000000000000 : ℝ)
    (3621519001 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell850_denomUpper :
    Real.exp (11045307492908593 / 1250000000000000 : ℝ) ≤ (17197799631393 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11045307492908593 / 1250000000000000 : ℝ) (659011368667
    / 500000000000 : ℝ) (17197799631393 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell850_denomLower :
    (67992008975593 / 10000000000 : ℝ) ≤ Real.exp (11030700461521259 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11030700461521259 / 1250000000000000 : ℝ) (82346344701 /
    62500000000 : ℝ) (67992008975593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell850_product_lower :
    (11363122336521259 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 16 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell850_leftExp
    (by norm_num : (0 : ℝ) ≤ (28935959441 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell850_product_upper :
    Real.pi * Real.exp (851 / 800 : ℝ) ≤ (11377338742908593 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell850_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell850_endpointLower :
    (80244457 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 32 : ℝ) (851 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11363122336521259 / 1250000000000000 : ℝ) (Real.pi * Real.exp (17 / 16 : ℝ))
    (by norm_num) hpThetaJensenCell850_product_lower
  have hD : Real.exp (Real.pi * Real.exp (851 / 800 : ℝ) - (17 / 64 : ℝ)) ≤
      (17197799631393 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell850_denomUpper
    linarith [hpThetaJensenCell850_product_upper]
  have hi : (1 / (17197799631393 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (851 / 800 : ℝ) - (17 / 64 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17197799631393 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17197799631393 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 64 : ℝ) - Real.pi * Real.exp (851 / 800 : ℝ)) := by
    rw [show (17 / 64 : ℝ) - Real.pi * Real.exp (851 / 800 : ℝ) =
      -(Real.pi * Real.exp (851 / 800 : ℝ) - (17 / 64 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 16 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 16 : ℝ)) := by
    have h := hpThetaJensenCell850_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17197799631393 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell850_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 32 : ℝ) (851 / 1600 : ℝ) ≤ (816254349 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (851 / 800 : ℝ)) (11377338742908593 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (851 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell850_product_upper
  have hD : (67992008975593 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 16 : ℝ) - (851 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell850_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell850_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 16 : ℝ) - (851 / 3200 : ℝ)) ≤
      (1 / (67992008975593 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (67992008975593 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((851 / 3200 : ℝ) - Real.pi * Real.exp (17 / 16 : ℝ)) ≤
      (2 / (67992008975593 / 10000000000 : ℝ) : ℝ) := by
    rw [show (851 / 3200 : ℝ) - Real.pi * Real.exp (17 / 16 : ℝ) =
      -(Real.pi * Real.exp (17 / 16 : ℝ) - (851 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (11377338742908593 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (11377338742908593 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell850_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 32 : ℝ) (851 / 1600 : ℝ)) :
    (80244457 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (816254349 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell850_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell850_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell851_leftExp :
    (14486076003 / 5000000000 : ℝ) ≤ Real.exp (851 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (851 / 800 : ℝ) (64612555161 / 62500000000 : ℝ)
    (14486076003 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell851_rightExp :
    Real.exp (213 / 200 : ℝ) ≤ (14504194921 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (213 / 200 : ℝ) (1033841266213 / 1000000000000 : ℝ)
    (14504194921 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell851_denomUpper :
    Real.exp (44236589734449153 / 5000000000000000 : ℝ) ≤ (17389270877413 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44236589734449153 / 5000000000000000 : ℝ) (26369577003 /
    20000000000 : ℝ) (17389270877413 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell851_denomLower :
    (68748018236267 / 10000000000 : ℝ) ≤ Real.exp (5522261310302097 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5522261310302097 / 625000000000000 : ℝ) (658998437799 /
    500000000000 : ℝ) (68748018236267 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell851_product_lower :
    (5688667560302097 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (851 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell851_leftExp
    (by norm_num : (0 : ℝ) ≤ (14486076003 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell851_product_upper :
    Real.pi * Real.exp (213 / 200 : ℝ) ≤ (45566277234449153 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell851_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell851_endpointLower :
    (159158371 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (851 / 1600 : ℝ) (213 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5688667560302097 / 625000000000000 : ℝ) (Real.pi * Real.exp (851 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell851_product_lower
  have hD : Real.exp (Real.pi * Real.exp (213 / 200 : ℝ) - (851 / 3200 : ℝ)) ≤
      (17389270877413 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell851_denomUpper
    linarith [hpThetaJensenCell851_product_upper]
  have hi : (1 / (17389270877413 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (213 / 200 : ℝ) - (851 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (17389270877413 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (17389270877413 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((851 / 3200 : ℝ) - Real.pi * Real.exp (213 / 200 : ℝ)) := by
    rw [show (851 / 3200 : ℝ) - Real.pi * Real.exp (213 / 200 : ℝ) =
      -(Real.pi * Real.exp (213 / 200 : ℝ) - (851 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (851 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (851 / 800 : ℝ)) := by
    have h := hpThetaJensenCell851_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (17389270877413 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell851_endpointUpper :
    hpThetaJensenKernelEndpointUpper (851 / 1600 : ℝ) (213 / 400 : ℝ) ≤ (809498359 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (213 / 200 : ℝ)) (45566277234449153 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (213 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell851_product_upper
  have hD : (68748018236267 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (851 / 800 : ℝ) - (213 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell851_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell851_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (851 / 800 : ℝ) - (213 / 800 : ℝ)) ≤
      (1 / (68748018236267 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (68748018236267 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((213 / 800 : ℝ) - Real.pi * Real.exp (851 / 800 : ℝ)) ≤
      (2 / (68748018236267 / 10000000000 : ℝ) : ℝ) := by
    rw [show (213 / 800 : ℝ) - Real.pi * Real.exp (851 / 800 : ℝ) =
      -(Real.pi * Real.exp (851 / 800 : ℝ) - (213 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (45566277234449153 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (45566277234449153 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell851_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (851 / 1600 : ℝ) (213 / 400 : ℝ)) :
    (159158371 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (809498359 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell851_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell851_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell852_leftExp :
    (362604873 / 125000000 : ℝ) ≤ Real.exp (213 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (213 / 200 : ℝ) (258460316553 / 250000000000 : ℝ)
    (362604873 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell852_rightExp :
    Real.exp (853 / 800 : ℝ) ≤ (29044673001 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (853 / 800 : ℝ) (516940825713 / 500000000000 : ℝ)
    (29044673001 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell852_denomUpper :
    Real.exp (88584041387230593 / 10000000000000000 : ℝ) ≤ (35166248465227 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (88584041387230593 / 10000000000000000 : ℝ) (164866963463
    / 125000000000 : ℝ) (35166248465227 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell852_denomLower :
    (347567111109 / 50000000 : ℝ) ≤ Real.exp (138229531959727 / 15625000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (138229531959727 / 15625000000000 : ℝ) (263690595863 /
    200000000000 : ℝ) (347567111109 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell852_product_lower :
    (142394571022227 / 15625000000000 : ℝ) ≤ Real.pi * Real.exp (213 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell852_leftExp
    (by norm_num : (0 : ℝ) ≤ (362604873 / 125000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell852_product_upper :
    Real.pi * Real.exp (853 / 800 : ℝ) ≤ (91246541387230593 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell852_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell852_endpointLower :
    (394591383 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (213 / 400 : ℝ) (853 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (142394571022227 / 15625000000000 : ℝ) (Real.pi * Real.exp (213 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell852_product_lower
  have hD : Real.exp (Real.pi * Real.exp (853 / 800 : ℝ) - (213 / 800 : ℝ)) ≤
      (35166248465227 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell852_denomUpper
    linarith [hpThetaJensenCell852_product_upper]
  have hi : (1 / (35166248465227 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (853 / 800 : ℝ) - (213 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (35166248465227 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (35166248465227 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((213 / 800 : ℝ) - Real.pi * Real.exp (853 / 800 : ℝ)) := by
    rw [show (213 / 800 : ℝ) - Real.pi * Real.exp (853 / 800 : ℝ) =
      -(Real.pi * Real.exp (853 / 800 : ℝ) - (213 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (213 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (213 / 200 : ℝ)) := by
    have h := hpThetaJensenCell852_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (35166248465227 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell852_endpointUpper :
    hpThetaJensenKernelEndpointUpper (213 / 400 : ℝ) (853 / 1600 : ℝ) ≤ (32111463 / 400000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (853 / 800 : ℝ)) (91246541387230593 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (853 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell852_product_upper
  have hD : (347567111109 / 50000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (213 / 200 : ℝ) - (853 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell852_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell852_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (213 / 200 : ℝ) - (853 / 3200 : ℝ)) ≤
      (1 / (347567111109 / 50000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (347567111109 / 50000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((853 / 3200 : ℝ) - Real.pi * Real.exp (213 / 200 : ℝ)) ≤
      (2 / (347567111109 / 50000000 : ℝ) : ℝ) := by
    rw [show (853 / 3200 : ℝ) - Real.pi * Real.exp (213 / 200 : ℝ) =
      -(Real.pi * Real.exp (213 / 200 : ℝ) - (853 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (91246541387230593 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (91246541387230593 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell852_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (213 / 400 : ℝ) (853 / 1600 : ℝ)) :
    (394591383 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (32111463 / 400000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell852_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell852_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell853_leftExp :
    (29044672999 / 10000000000 : ℝ) ≤ Real.exp (853 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (853 / 800 : ℝ) (41355266057 / 40000000000 : ℝ)
    (29044672999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell853_rightExp :
    Real.exp (427 / 400 : ℝ) ≤ (29081001543 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (427 / 400 : ℝ) (1033922038217 / 1000000000000 : ℝ)
    (29081001543 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell853_denomUpper :
    Real.exp (88695045880477999 / 10000000000000000 : ℝ) ≤ (14223513701961 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (88695045880477999 / 10000000000000000 : ℝ)
    (1319393311411 / 1000000000000 : ℝ) (14223513701961 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell853_denomLower :
    (70288348656947 / 10000000000 : ℝ) ≤ Real.exp (11072220292034301 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11072220292034301 / 1250000000000000 : ℝ) (263781965551
    / 200000000000 : ℝ) (70288348656947 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell853_product_lower :
    (11405814042034301 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (853 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell853_leftExp
    (by norm_num : (0 : ℝ) ≤ (29044672999 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell853_product_upper :
    Real.pi * Real.exp (427 / 400 : ℝ) ≤ (91360670880477999 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell853_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell853_endpointLower :
    (782617119 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (853 / 1600 : ℝ) (427 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11405814042034301 / 1250000000000000 : ℝ) (Real.pi * Real.exp (853 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell853_product_lower
  have hD : Real.exp (Real.pi * Real.exp (427 / 400 : ℝ) - (853 / 3200 : ℝ)) ≤
      (14223513701961 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell853_denomUpper
    linarith [hpThetaJensenCell853_product_upper]
  have hi : (1 / (14223513701961 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (427 / 400 : ℝ) - (853 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (14223513701961 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (14223513701961 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((853 / 3200 : ℝ) - Real.pi * Real.exp (427 / 400 : ℝ)) := by
    rw [show (853 / 3200 : ℝ) - Real.pi * Real.exp (427 / 400 : ℝ) =
      -(Real.pi * Real.exp (427 / 400 : ℝ) - (853 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (853 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (853 / 800 : ℝ)) := by
    have h := hpThetaJensenCell853_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (14223513701961 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell853_endpointUpper :
    hpThetaJensenKernelEndpointUpper (853 / 1600 : ℝ) (427 / 800 : ℝ) ≤ (796118811 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (427 / 400 : ℝ)) (91360670880477999 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (427 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell853_product_upper
  have hD : (70288348656947 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (853 / 800 : ℝ) - (427 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell853_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell853_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (853 / 800 : ℝ) - (427 / 1600 : ℝ)) ≤
      (1 / (70288348656947 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (70288348656947 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((427 / 1600 : ℝ) - Real.pi * Real.exp (853 / 800 : ℝ)) ≤
      (2 / (70288348656947 / 10000000000 : ℝ) : ℝ) := by
    rw [show (427 / 1600 : ℝ) - Real.pi * Real.exp (853 / 800 : ℝ) =
      -(Real.pi * Real.exp (853 / 800 : ℝ) - (427 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (91360670880477999 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (91360670880477999 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell853_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (853 / 1600 : ℝ) (427 / 800 : ℝ)) :
    (782617119 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (796118811 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell853_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell853_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell854_leftExp :
    (29081001541 / 10000000000 : ℝ) ≤ Real.exp (427 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (427 / 400 : ℝ) (129240254777 / 125000000000 : ℝ)
    (29081001541 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell854_rightExp :
    Real.exp (171 / 160 : ℝ) ≤ (7279343881 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (171 / 160 : ℝ) (206792485317 / 200000000000 : ℝ)
    (7279343881 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell854_denomUpper :
    Real.exp (22201548281142433 / 2500000000000000 : ℝ) ≤ (71912429834263 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (22201548281142433 / 2500000000000000 : ℝ) (263970332533
    / 200000000000 : ℝ) (71912429834263 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell854_denomLower :
    (888411589797 / 125000000 : ℝ) ≤ Real.exp (11086095849149159 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11086095849149159 / 1250000000000000 : ℝ) (659683711167
    / 500000000000 : ℝ) (888411589797 / 125000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell854_product_lower :
    (11420080224149159 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (427 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell854_leftExp
    (by norm_num : (0 : ℝ) ≤ (29081001541 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell854_product_upper :
    Real.pi * Real.exp (171 / 160 : ℝ) ≤ (22868735781142433 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell854_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell854_endpointLower :
    (776094731 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (427 / 800 : ℝ) (171 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11420080224149159 / 1250000000000000 : ℝ) (Real.pi * Real.exp (427 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell854_product_lower
  have hD : Real.exp (Real.pi * Real.exp (171 / 160 : ℝ) - (427 / 1600 : ℝ)) ≤
      (71912429834263 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell854_denomUpper
    linarith [hpThetaJensenCell854_product_upper]
  have hi : (1 / (71912429834263 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (171 / 160 : ℝ) - (427 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71912429834263 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71912429834263 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((427 / 1600 : ℝ) - Real.pi * Real.exp (171 / 160 : ℝ)) := by
    rw [show (427 / 1600 : ℝ) - Real.pi * Real.exp (171 / 160 : ℝ) =
      -(Real.pi * Real.exp (171 / 160 : ℝ) - (427 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (427 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (427 / 400 : ℝ)) := by
    have h := hpThetaJensenCell854_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71912429834263 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell854_endpointUpper :
    hpThetaJensenKernelEndpointUpper (427 / 800 : ℝ) (171 / 320 : ℝ) ≤ (394747441 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (171 / 160 : ℝ)) (22868735781142433 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (171 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell854_product_upper
  have hD : (888411589797 / 125000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (427 / 400 : ℝ) - (171 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell854_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell854_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (427 / 400 : ℝ) - (171 / 640 : ℝ)) ≤
      (1 / (888411589797 / 125000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (888411589797 / 125000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((171 / 640 : ℝ) - Real.pi * Real.exp (427 / 400 : ℝ)) ≤
      (2 / (888411589797 / 125000000 : ℝ) : ℝ) := by
    rw [show (171 / 640 : ℝ) - Real.pi * Real.exp (427 / 400 : ℝ) =
      -(Real.pi * Real.exp (427 / 400 : ℝ) - (171 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (22868735781142433 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (22868735781142433 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell854_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (427 / 800 : ℝ) (171 / 320 : ℝ)) :
    (776094731 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (394747441 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell854_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell854_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell855_leftExp :
    (14558687761 / 5000000000 : ℝ) ≤ Real.exp (171 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (171 / 160 : ℝ) (129245303323 / 125000000000 : ℝ)
    (14558687761 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell855_rightExp :
    Real.exp (107 / 100 : ℝ) ≤ (29153795001 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (107 / 100 : ℝ) (1034002816531 / 1000000000000 : ℝ)
    (29153795001 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell855_denomUpper :
    Real.exp (88917483298576593 / 10000000000000000 : ℝ) ≤ (2908688577709 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (88917483298576593 / 10000000000000000 : ℝ)
    (1320310762873 / 1000000000000 : ℝ) (2908688577709 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell855_denomLower :
    (35933644651349 / 5000000000 : ℝ) ≤ Real.exp (5549994625056939 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5549994625056939 / 625000000000000 : ℝ) (329956441111 /
    250000000000 : ℝ) (35933644651349 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell855_product_lower :
    (5717182125056939 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (171 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell855_leftExp
    (by norm_num : (0 : ℝ) ≤ (14558687761 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell855_product_upper :
    Real.pi * Real.exp (107 / 100 : ℝ) ≤ (91589358298576593 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell855_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell855_endpointLower :
    (384807709 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (171 / 320 : ℝ) (107 / 200 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5717182125056939 / 625000000000000 : ℝ) (Real.pi * Real.exp (171 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell855_product_lower
  have hD : Real.exp (Real.pi * Real.exp (107 / 100 : ℝ) - (171 / 640 : ℝ)) ≤
      (2908688577709 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell855_denomUpper
    linarith [hpThetaJensenCell855_product_upper]
  have hi : (1 / (2908688577709 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (107 / 100 : ℝ) - (171 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2908688577709 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2908688577709 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((171 / 640 : ℝ) - Real.pi * Real.exp (107 / 100 : ℝ)) := by
    rw [show (171 / 640 : ℝ) - Real.pi * Real.exp (107 / 100 : ℝ) =
      -(Real.pi * Real.exp (107 / 100 : ℝ) - (171 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (171 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (171 / 160 : ℝ)) := by
    have h := hpThetaJensenCell855_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2908688577709 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell855_endpointUpper :
    hpThetaJensenKernelEndpointUpper (171 / 320 : ℝ) (107 / 200 : ℝ) ≤ (391457301 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (107 / 100 : ℝ)) (91589358298576593 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (107 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell855_product_upper
  have hD : (35933644651349 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (171 / 160 : ℝ) - (107 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell855_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell855_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (171 / 160 : ℝ) - (107 / 400 : ℝ)) ≤
      (1 / (35933644651349 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (35933644651349 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((107 / 400 : ℝ) - Real.pi * Real.exp (171 / 160 : ℝ)) ≤
      (2 / (35933644651349 / 5000000000 : ℝ) : ℝ) := by
    rw [show (107 / 400 : ℝ) - Real.pi * Real.exp (171 / 160 : ℝ) =
      -(Real.pi * Real.exp (171 / 160 : ℝ) - (107 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (91589358298576593 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (91589358298576593 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell855_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (171 / 320 : ℝ) (107 / 200 : ℝ)) :
    (384807709 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (391457301 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell855_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell855_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell856_leftExp :
    (29153794999 / 10000000000 : ℝ) ≤ Real.exp (107 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (107 / 100 : ℝ) (103400281653 / 100000000000 : ℝ)
    (29153794999 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell856_rightExp :
    Real.exp (857 / 800 : ℝ) ≤ (2919026003 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (857 / 800 : ℝ) (206808641611 / 200000000000 : ℝ)
    (2919026003 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell856_denomUpper :
    Real.exp (8902891657842779 / 1000000000000000 : ℝ) ≤ (18383014453753 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8902891657842779 / 1000000000000000 : ℝ) (1320770613431
    / 1000000000000 : ℝ) (18383014453753 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell856_denomLower :
    (72671568470467 / 10000000000 : ℝ) ≤ Real.exp (11113900517312301 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11113900517312301 / 1250000000000000 : ℝ) (1320284855493
    / 1000000000000 : ℝ) (72671568470467 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell856_product_lower :
    (11448666142312301 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (107 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell856_leftExp
    (by norm_num : (0 : ℝ) ≤ (29153794999 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell856_product_upper :
    Real.pi * Real.exp (857 / 800 : ℝ) ≤ (9170391657842779 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell856_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell856_endpointLower :
    (763178997 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (107 / 200 : ℝ) (857 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (11448666142312301 / 1250000000000000 : ℝ) (Real.pi * Real.exp (107 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell856_product_lower
  have hD : Real.exp (Real.pi * Real.exp (857 / 800 : ℝ) - (107 / 400 : ℝ)) ≤
      (18383014453753 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell856_denomUpper
    linarith [hpThetaJensenCell856_product_upper]
  have hi : (1 / (18383014453753 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (857 / 800 : ℝ) - (107 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18383014453753 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18383014453753 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((107 / 400 : ℝ) - Real.pi * Real.exp (857 / 800 : ℝ)) := by
    rw [show (107 / 400 : ℝ) - Real.pi * Real.exp (857 / 800 : ℝ) =
      -(Real.pi * Real.exp (857 / 800 : ℝ) - (107 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (107 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (107 / 100 : ℝ)) := by
    have h := hpThetaJensenCell856_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18383014453753 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell856_endpointUpper :
    hpThetaJensenKernelEndpointUpper (107 / 200 : ℝ) (857 / 1600 : ℝ) ≤ (776377787 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (857 / 800 : ℝ)) (9170391657842779 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (857 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell856_product_upper
  have hD : (72671568470467 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (107 / 100 : ℝ) - (857 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell856_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell856_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (107 / 100 : ℝ) - (857 / 3200 : ℝ)) ≤
      (1 / (72671568470467 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (72671568470467 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((857 / 3200 : ℝ) - Real.pi * Real.exp (107 / 100 : ℝ)) ≤
      (2 / (72671568470467 / 10000000000 : ℝ) : ℝ) := by
    rw [show (857 / 3200 : ℝ) - Real.pi * Real.exp (107 / 100 : ℝ) =
      -(Real.pi * Real.exp (107 / 100 : ℝ) - (857 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9170391657842779 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9170391657842779 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell856_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (107 / 200 : ℝ) (857 / 1600 : ℝ)) :
    (763178997 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (776377787 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell856_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell856_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell857_leftExp :
    (7297565007 / 2500000000 : ℝ) ≤ Real.exp (857 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (857 / 800 : ℝ) (517021604027 / 500000000000 : ℝ)
    (7297565007 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell857_rightExp :
    Real.exp (429 / 400 : ℝ) ≤ (2922677067 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (429 / 400 : ℝ) (1034083601157 / 1000000000000 : ℝ)
    (2922677067 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell857_denomUpper :
    Real.exp (8914049314947731 / 1000000000000000 : ℝ) ≤ (74357097496887 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (8914049314947731 / 1000000000000000 : ℝ) (1321231215777
    / 1000000000000 : ℝ) (74357097496887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell857_denomLower :
    (4592868755111 / 625000000 : ℝ) ≤ Real.exp (2781957418183893 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2781957418183893 / 312500000000000 : ℝ) (1320744696877 /
    1000000000000 : ℝ) (4592868755111 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell857_product_lower :
    (2865746480683893 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (857 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell857_leftExp
    (by norm_num : (0 : ℝ) ≤ (7297565007 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell857_product_upper :
    Real.pi * Real.exp (429 / 400 : ℝ) ≤ (9181861814947731 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell857_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell857_endpointLower :
    (189196321 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (857 / 1600 : ℝ) (429 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2865746480683893 / 312500000000000 : ℝ) (Real.pi * Real.exp (857 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell857_product_lower
  have hD : Real.exp (Real.pi * Real.exp (429 / 400 : ℝ) - (857 / 3200 : ℝ)) ≤
      (74357097496887 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell857_denomUpper
    linarith [hpThetaJensenCell857_product_upper]
  have hi : (1 / (74357097496887 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (429 / 400 : ℝ) - (857 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (74357097496887 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (74357097496887 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((857 / 3200 : ℝ) - Real.pi * Real.exp (429 / 400 : ℝ)) := by
    rw [show (857 / 3200 : ℝ) - Real.pi * Real.exp (429 / 400 : ℝ) =
      -(Real.pi * Real.exp (429 / 400 : ℝ) - (857 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (857 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (857 / 800 : ℝ)) := by
    have h := hpThetaJensenCell857_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (74357097496887 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell857_endpointUpper :
    hpThetaJensenKernelEndpointUpper (857 / 1600 : ℝ) (429 / 800 : ℝ) ≤ (769884251 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (429 / 400 : ℝ)) (9181861814947731 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (429 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell857_product_upper
  have hD : (4592868755111 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (857 / 800 : ℝ) - (429 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell857_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell857_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (857 / 800 : ℝ) - (429 / 1600 : ℝ)) ≤
      (1 / (4592868755111 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (4592868755111 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((429 / 1600 : ℝ) - Real.pi * Real.exp (857 / 800 : ℝ)) ≤
      (2 / (4592868755111 / 625000000 : ℝ) : ℝ) := by
    rw [show (429 / 1600 : ℝ) - Real.pi * Real.exp (857 / 800 : ℝ) =
      -(Real.pi * Real.exp (857 / 800 : ℝ) - (429 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9181861814947731 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9181861814947731 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell857_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (857 / 1600 : ℝ) (429 / 800 : ℝ)) :
    (189196321 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (769884251 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell857_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell857_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell858_leftExp :
    (7306692667 / 2500000000 : ℝ) ≤ Real.exp (429 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (429 / 400 : ℝ) (258520900289 / 250000000000 : ℝ)
    (7306692667 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell858_rightExp :
    Real.exp (859 / 800 : ℝ) ≤ (114309871 / 39062500 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (859 / 800 : ℝ) (258530998959 / 250000000000 : ℝ)
    (114309871 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell858_denomUpper :
    Real.exp (348641457752003 / 39062500000000 : ℝ) ≤ (18798118242857 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (348641457752003 / 39062500000000 : ℝ) (1321692571301 /
    1000000000000 : ℝ) (18798118242857 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell858_denomLower :
    (37155210798887 / 5000000000 : ℝ) ≤ Real.exp (2785444184888233 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2785444184888233 / 312500000000000 : ℝ) (264241058007 /
    200000000000 : ℝ) (37155210798887 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell858_product_lower :
    (2869330903638233 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (429 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell858_leftExp
    (by norm_num : (0 : ℝ) ≤ (7306692667 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell858_product_upper :
    Real.pi * Real.exp (859 / 800 : ℝ) ≤ (359115090564503 / 39062500000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell858_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell858_endpointLower :
    (46902131 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (429 / 800 : ℝ) (859 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2869330903638233 / 312500000000000 : ℝ) (Real.pi * Real.exp (429 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell858_product_lower
  have hD : Real.exp (Real.pi * Real.exp (859 / 800 : ℝ) - (429 / 1600 : ℝ)) ≤
      (18798118242857 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell858_denomUpper
    linarith [hpThetaJensenCell858_product_upper]
  have hi : (1 / (18798118242857 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (859 / 800 : ℝ) - (429 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18798118242857 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18798118242857 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((429 / 1600 : ℝ) - Real.pi * Real.exp (859 / 800 : ℝ)) := by
    rw [show (429 / 1600 : ℝ) - Real.pi * Real.exp (859 / 800 : ℝ) =
      -(Real.pi * Real.exp (859 / 800 : ℝ) - (429 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (429 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (429 / 400 : ℝ)) := by
    have h := hpThetaJensenCell858_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18798118242857 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell858_endpointUpper :
    hpThetaJensenKernelEndpointUpper (429 / 800 : ℝ) (859 / 1600 : ℝ) ≤ (47714613 / 625000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (859 / 800 : ℝ)) (359115090564503 / 39062500000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (859 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell858_product_upper
  have hD : (37155210798887 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (429 / 400 : ℝ) - (859 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell858_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell858_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (429 / 400 : ℝ) - (859 / 3200 : ℝ)) ≤
      (1 / (37155210798887 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (37155210798887 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((859 / 3200 : ℝ) - Real.pi * Real.exp (429 / 400 : ℝ)) ≤
      (2 / (37155210798887 / 5000000000 : ℝ) : ℝ) := by
    rw [show (859 / 3200 : ℝ) - Real.pi * Real.exp (429 / 400 : ℝ) =
      -(Real.pi * Real.exp (429 / 400 : ℝ) - (859 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (359115090564503 / 39062500000000 : ℝ) ^ 2 - 6 *
      (359115090564503 / 39062500000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell858_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (429 / 800 : ℝ) (859 / 1600 : ℝ)) :
    (46902131 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (47714613 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell858_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell858_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell859_leftExp :
    (14631663487 / 5000000000 : ℝ) ≤ Real.exp (859 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (859 / 800 : ℝ) (206824799167 / 200000000000 : ℝ)
    (14631663487 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell859_rightExp :
    Real.exp (43 / 40 : ℝ) ≤ (14649964503 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 40 : ℝ) (517082196047 / 500000000000 : ℝ)
    (14649964503 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell859_denomUpper :
    Real.exp (44682038432873279 / 5000000000000000 : ℝ) ≤ (15207665168853 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (44682038432873279 / 5000000000000000 : ℝ) (1322154681431
    / 1000000000000 : ℝ) (15207665168853 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell859_denomLower :
    (18786318102129 / 2500000000 : ℝ) ≤ Real.exp (5577870869681413 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5577870869681413 / 625000000000000 : ℝ) (660833318177 /
    500000000000 : ℝ) (18786318102129 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell859_product_lower :
    (5745839619681413 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (859 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell859_leftExp
    (by norm_num : (0 : ℝ) ≤ (14631663487 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell859_product_upper :
    Real.pi * Real.exp (43 / 40 : ℝ) ≤ (46024225932873279 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell859_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell859_endpointLower :
    (11626957 / 156250000 : ℝ) ≤ hpThetaTraceEndpointLower (859 / 1600 : ℝ) (43 / 80 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (5745839619681413 / 625000000000000 : ℝ) (Real.pi * Real.exp (859 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell859_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 40 : ℝ) - (859 / 3200 : ℝ)) ≤
      (15207665168853 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell859_denomUpper
    linarith [hpThetaJensenCell859_product_upper]
  have hi : (1 / (15207665168853 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 40 : ℝ) - (859 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15207665168853 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15207665168853 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((859 / 3200 : ℝ) - Real.pi * Real.exp (43 / 40 : ℝ)) := by
    rw [show (859 / 3200 : ℝ) - Real.pi * Real.exp (43 / 40 : ℝ) =
      -(Real.pi * Real.exp (43 / 40 : ℝ) - (859 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (859 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (859 / 800 : ℝ)) := by
    have h := hpThetaJensenCell859_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15207665168853 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell859_endpointUpper :
    hpThetaJensenKernelEndpointUpper (859 / 1600 : ℝ) (43 / 80 : ℝ) ≤ (378513137 / 5000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 40 : ℝ)) (46024225932873279 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 80 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell859_product_upper
  have hD : (18786318102129 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (859 / 800 : ℝ) - (43 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell859_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell859_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (859 / 800 : ℝ) - (43 / 160 : ℝ)) ≤
      (1 / (18786318102129 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (18786318102129 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 160 : ℝ) - Real.pi * Real.exp (859 / 800 : ℝ)) ≤
      (2 / (18786318102129 / 2500000000 : ℝ) : ℝ) := by
    rw [show (43 / 160 : ℝ) - Real.pi * Real.exp (859 / 800 : ℝ) =
      -(Real.pi * Real.exp (859 / 800 : ℝ) - (43 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (46024225932873279 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (46024225932873279 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell859_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (859 / 1600 : ℝ) (43 / 80 : ℝ)) :
    (11626957 / 156250000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (378513137 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell859_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell859_endpointUpper

def hpThetaJensenCellsBatch042Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (217852861 / 2500000000 : ℝ)
  | 1 => (864312399 / 10000000000 : ℝ)
  | 2 => (857258809 / 10000000000 : ℝ)
  | 3 => (212562623 / 2500000000 : ℝ)
  | 4 => (421643633 / 5000000000 : ℝ)
  | 5 => (209092237 / 2500000000 : ℝ)
  | 6 => (165899071 / 2000000000 : ℝ)
  | 7 => (12854161 / 156250000 : ℝ)
  | 8 => (815881611 / 10000000000 : ℝ)
  | 9 => (404570547 / 5000000000 : ℝ)
  | 10 => (80244457 / 1000000000 : ℝ)
  | 11 => (159158371 / 2000000000 : ℝ)
  | 12 => (394591383 / 5000000000 : ℝ)
  | 13 => (782617119 / 10000000000 : ℝ)
  | 14 => (776094731 / 10000000000 : ℝ)
  | 15 => (384807709 / 5000000000 : ℝ)
  | 16 => (763178997 / 10000000000 : ℝ)
  | 17 => (189196321 / 2500000000 : ℝ)
  | 18 => (46902131 / 625000000 : ℝ)
  | 19 => (11626957 / 156250000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch042Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4431431 / 50000000 : ℝ)
  | 1 => (439538997 / 5000000000 : ℝ)
  | 2 => (871915841 / 10000000000 : ℝ)
  | 3 => (172959911 / 2000000000 : ℝ)
  | 4 => (107216119 / 1250000000 : ℝ)
  | 5 => (106337981 / 1250000000 : ℝ)
  | 6 => (421862029 / 5000000000 : ℝ)
  | 7 => (418394699 / 5000000000 : ℝ)
  | 8 => (829899683 / 10000000000 : ℝ)
  | 9 => (102881841 / 1250000000 : ℝ)
  | 10 => (816254349 / 10000000000 : ℝ)
  | 11 => (809498359 / 10000000000 : ℝ)
  | 12 => (32111463 / 400000000 : ℝ)
  | 13 => (796118811 / 10000000000 : ℝ)
  | 14 => (394747441 / 5000000000 : ℝ)
  | 15 => (391457301 / 5000000000 : ℝ)
  | 16 => (776377787 / 10000000000 : ℝ)
  | 17 => (769884251 / 10000000000 : ℝ)
  | 18 => (47714613 / 625000000 : ℝ)
  | 19 => (378513137 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch042_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch042Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch042Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell840_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell841_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell842_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell843_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell844_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell845_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell846_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell847_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell848_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell849_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell850_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell851_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell852_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell853_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell854_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell855_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell856_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell857_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell858_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell859_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper] at h ⊢
    exact h

end HodgeProofHP
