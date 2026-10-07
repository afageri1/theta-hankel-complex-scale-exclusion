import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell900_leftExp :
    (3850271061 / 1250000000 : ℝ) ≤ Real.exp (9 / 8 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (9 / 8 : ℝ) (1035781537021 / 1000000000000 : ℝ)
    (3850271061 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell900_rightExp :
    Real.exp (901 / 800 : ℝ) ≤ (1233627811 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (901 / 800 : ℝ) (1035821998029 / 1000000000000 : ℝ)
    (1233627811 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell900_denomUpper :
    Real.exp (3763056495642923 / 400000000000000 : ℝ) ≤ (60905523750499 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3763056495642923 / 400000000000000 : ℝ) (8386055379 /
    6250000000 : ℝ) (60905523750499 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell900_denomLower :
    (6015380770441 / 500000000 : ℝ) ≤ Real.exp (1468003454758639 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1468003454758639 / 156250000000000 : ℝ) (1341248224171 /
    1000000000000 : ℝ) (6015380770441 / 500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell900_product_lower :
    (1511997595383639 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (9 / 8 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell900_leftExp
    (by norm_num : (0 : ℝ) ≤ (3850271061 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell900_product_upper :
    Real.pi * Real.exp (901 / 800 : ℝ) ≤ (3875556495642923 / 400000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell900_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell900_endpointLower :
    (519657191 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 16 : ℝ) (901 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1511997595383639 / 156250000000000 : ℝ) (Real.pi * Real.exp (9 / 8 : ℝ))
    (by norm_num) hpThetaJensenCell900_product_lower
  have hD : Real.exp (Real.pi * Real.exp (901 / 800 : ℝ) - (9 / 32 : ℝ)) ≤
      (60905523750499 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell900_denomUpper
    linarith [hpThetaJensenCell900_product_upper]
  have hi : (1 / (60905523750499 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (901 / 800 : ℝ) - (9 / 32 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (60905523750499 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (60905523750499 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((9 / 32 : ℝ) - Real.pi * Real.exp (901 / 800 : ℝ)) := by
    rw [show (9 / 32 : ℝ) - Real.pi * Real.exp (901 / 800 : ℝ) =
      -(Real.pi * Real.exp (901 / 800 : ℝ) - (9 / 32 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (9 / 8 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (9 / 8 : ℝ)) := by
    have h := hpThetaJensenCell900_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (60905523750499 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell900_endpointUpper :
    hpThetaJensenKernelEndpointUpper (9 / 16 : ℝ) (901 / 1600 : ℝ) ≤ (528978811 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (901 / 800 : ℝ)) (3875556495642923 / 400000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (901 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell900_product_upper
  have hD : (6015380770441 / 500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (9 / 8 : ℝ) - (901 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell900_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell900_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (9 / 8 : ℝ) - (901 / 3200 : ℝ)) ≤
      (1 / (6015380770441 / 500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (6015380770441 / 500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((901 / 3200 : ℝ) - Real.pi * Real.exp (9 / 8 : ℝ)) ≤
      (2 / (6015380770441 / 500000000 : ℝ) : ℝ) := by
    rw [show (901 / 3200 : ℝ) - Real.pi * Real.exp (9 / 8 : ℝ) =
      -(Real.pi * Real.exp (9 / 8 : ℝ) - (901 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3875556495642923 / 400000000000000 : ℝ) ^ 2 - 6 *
      (3875556495642923 / 400000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell900_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (9 / 16 : ℝ) (901 / 1600 : ℝ)) :
    (519657191 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (528978811 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell900_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell900_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell901_leftExp :
    (30840695273 / 10000000000 : ℝ) ≤ Real.exp (901 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (901 / 800 : ℝ) (258955499507 / 250000000000 : ℝ)
    (30840695273 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell901_rightExp :
    Real.exp (451 / 400 : ℝ) ≤ (30879270249 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (451 / 400 : ℝ) (129482807577 / 125000000000 : ℝ)
    (30879270249 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell901_denomUpper :
    Real.exp (94194474259366657 / 10000000000000000 : ℝ) ≤ (30814423593229 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (94194474259366657 / 10000000000000000 : ℝ) (671131994327
    / 500000000000 : ℝ) (30814423593229 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell901_denomLower :
    (121734563864283 / 10000000000 : ℝ) ≤ Real.exp (11758766443011827 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11758766443011827 / 1250000000000000 : ℝ) (335435631283
    / 250000000000 : ℝ) (121734563864283 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell901_product_lower :
    (12111110193011827 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (901 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell901_leftExp
    (by norm_num : (0 : ℝ) ≤ (30840695273 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell901_product_upper :
    Real.pi * Real.exp (451 / 400 : ℝ) ≤ (97010099259366657 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell901_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell901_endpointLower :
    (25748079 / 500000000 : ℝ) ≤ hpThetaTraceEndpointLower (901 / 1600 : ℝ) (451 / 800 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12111110193011827 / 1250000000000000 : ℝ) (Real.pi * Real.exp (901 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell901_product_lower
  have hD : Real.exp (Real.pi * Real.exp (451 / 400 : ℝ) - (901 / 3200 : ℝ)) ≤
      (30814423593229 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell901_denomUpper
    linarith [hpThetaJensenCell901_product_upper]
  have hi : (1 / (30814423593229 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (451 / 400 : ℝ) - (901 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (30814423593229 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (30814423593229 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((901 / 3200 : ℝ) - Real.pi * Real.exp (451 / 400 : ℝ)) := by
    rw [show (901 / 3200 : ℝ) - Real.pi * Real.exp (451 / 400 : ℝ) =
      -(Real.pi * Real.exp (451 / 400 : ℝ) - (901 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (901 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (901 / 800 : ℝ)) := by
    have h := hpThetaJensenCell901_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (30814423593229 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell901_endpointUpper :
    hpThetaJensenKernelEndpointUpper (901 / 1600 : ℝ) (451 / 800 : ℝ) ≤ (524206731 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (451 / 400 : ℝ)) (97010099259366657 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (451 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell901_product_upper
  have hD : (121734563864283 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (901 / 800 : ℝ) - (451 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell901_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell901_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (901 / 800 : ℝ) - (451 / 1600 : ℝ)) ≤
      (1 / (121734563864283 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (121734563864283 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((451 / 1600 : ℝ) - Real.pi * Real.exp (901 / 800 : ℝ)) ≤
      (2 / (121734563864283 / 10000000000 : ℝ) : ℝ) := by
    rw [show (451 / 1600 : ℝ) - Real.pi * Real.exp (901 / 800 : ℝ) =
      -(Real.pi * Real.exp (901 / 800 : ℝ) - (451 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (97010099259366657 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (97010099259366657 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell901_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (901 / 1600 : ℝ) (451 / 800 : ℝ)) :
    (25748079 / 500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (524206731 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell901_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell901_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell902_leftExp :
    (30879270247 / 10000000000 : ℝ) ≤ Real.exp (451 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (451 / 400 : ℝ) (207172492123 / 200000000000 : ℝ)
    (30879270247 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell902_rightExp :
    Real.exp (903 / 800 : ℝ) ≤ (3091789347 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (903 / 800 : ℝ) (1035902924783 / 1000000000000 : ℝ)
    (3091789347 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell902_denomUpper :
    Real.exp (9431268770009771 / 1000000000000000 : ℝ) ≤ (124723412297239 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9431268770009771 / 1000000000000000 : ℝ) (1342759935393
    / 1000000000000 : ℝ) (124723412297239 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell902_denomLower :
    (30795075482309 / 2500000000 : ℝ) ≤ Real.exp (11773524171726653 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11773524171726653 / 1250000000000000 : ℝ) (671118821633
    / 500000000000 : ℝ) (30795075482309 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell902_product_lower :
    (12126258546726653 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (451 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell902_leftExp
    (by norm_num : (0 : ℝ) ≤ (30879270247 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell902_product_upper :
    Real.pi * Real.exp (903 / 800 : ℝ) ≤ (9713143770009771 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell902_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell902_endpointLower :
    (127575123 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (451 / 800 : ℝ) (903 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12126258546726653 / 1250000000000000 : ℝ) (Real.pi * Real.exp (451 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell902_product_lower
  have hD : Real.exp (Real.pi * Real.exp (903 / 800 : ℝ) - (451 / 1600 : ℝ)) ≤
      (124723412297239 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell902_denomUpper
    linarith [hpThetaJensenCell902_product_upper]
  have hi : (1 / (124723412297239 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (903 / 800 : ℝ) - (451 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (124723412297239 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (124723412297239 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((451 / 1600 : ℝ) - Real.pi * Real.exp (903 / 800 : ℝ)) := by
    rw [show (451 / 1600 : ℝ) - Real.pi * Real.exp (903 / 800 : ℝ) =
      -(Real.pi * Real.exp (903 / 800 : ℝ) - (451 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (451 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (451 / 400 : ℝ)) := by
    have h := hpThetaJensenCell902_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (124723412297239 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell902_endpointUpper :
    hpThetaJensenKernelEndpointUpper (451 / 800 : ℝ) (903 / 1600 : ℝ) ≤ (259734831 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (903 / 800 : ℝ)) (9713143770009771 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (903 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell902_product_upper
  have hD : (30795075482309 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (451 / 400 : ℝ) - (903 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell902_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell902_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (451 / 400 : ℝ) - (903 / 3200 : ℝ)) ≤
      (1 / (30795075482309 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (30795075482309 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((903 / 3200 : ℝ) - Real.pi * Real.exp (451 / 400 : ℝ)) ≤
      (2 / (30795075482309 / 2500000000 : ℝ) : ℝ) := by
    rw [show (903 / 3200 : ℝ) - Real.pi * Real.exp (451 / 400 : ℝ) =
      -(Real.pi * Real.exp (451 / 400 : ℝ) - (903 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9713143770009771 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9713143770009771 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell902_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (451 / 800 : ℝ) (903 / 1600 : ℝ)) :
    (127575123 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (259734831 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell902_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell902_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell903_leftExp :
    (7729473367 / 2500000000 : ℝ) ≤ Real.exp (903 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (903 / 800 : ℝ) (517951462391 / 500000000000 : ℝ)
    (7729473367 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell903_rightExp :
    Real.exp (113 / 100 : ℝ) ≤ (15478282501 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (113 / 100 : ℝ) (258985847633 / 250000000000 : ℝ)
    (15478282501 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell903_denomUpper :
    Real.exp (47215526457164093 / 5000000000000000 : ℝ) ≤ (15776059411327 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (47215526457164093 / 5000000000000000 : ℝ) (1343256702473
    / 1000000000000 : ℝ) (15776059411327 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell903_denomLower :
    (124645099061373 / 10000000000 : ℝ) ≤ Real.exp (2947075211747533 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2947075211747533 / 312500000000000 : ℝ) (1342733580109 /
    1000000000000 : ℝ) (124645099061373 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell903_product_lower :
    (3035356461747533 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (903 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell903_leftExp
    (by norm_num : (0 : ℝ) ≤ (7729473367 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell903_product_upper :
    Real.pi * Real.exp (113 / 100 : ℝ) ≤ (48626463957164093 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell903_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell903_endpointLower :
    (505673747 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (903 / 1600 : ℝ) (113 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3035356461747533 / 312500000000000 : ℝ) (Real.pi * Real.exp (903 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell903_product_lower
  have hD : Real.exp (Real.pi * Real.exp (113 / 100 : ℝ) - (903 / 3200 : ℝ)) ≤
      (15776059411327 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell903_denomUpper
    linarith [hpThetaJensenCell903_product_upper]
  have hi : (1 / (15776059411327 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (113 / 100 : ℝ) - (903 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (15776059411327 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (15776059411327 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((903 / 3200 : ℝ) - Real.pi * Real.exp (113 / 100 : ℝ)) := by
    rw [show (903 / 3200 : ℝ) - Real.pi * Real.exp (113 / 100 : ℝ) =
      -(Real.pi * Real.exp (113 / 100 : ℝ) - (903 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (903 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (903 / 800 : ℝ)) := by
    have h := hpThetaJensenCell903_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (15776059411327 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell903_endpointUpper :
    hpThetaJensenKernelEndpointUpper (903 / 1600 : ℝ) (113 / 200 : ℝ) ≤ (514767423 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (113 / 100 : ℝ)) (48626463957164093 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (113 / 200 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell903_product_upper
  have hD : (124645099061373 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (903 / 800 : ℝ) - (113 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell903_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell903_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (903 / 800 : ℝ) - (113 / 400 : ℝ)) ≤
      (1 / (124645099061373 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (124645099061373 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((113 / 400 : ℝ) - Real.pi * Real.exp (903 / 800 : ℝ)) ≤
      (2 / (124645099061373 / 10000000000 : ℝ) : ℝ) := by
    rw [show (113 / 400 : ℝ) - Real.pi * Real.exp (903 / 800 : ℝ) =
      -(Real.pi * Real.exp (903 / 800 : ℝ) - (113 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48626463957164093 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (48626463957164093 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell903_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (903 / 1600 : ℝ) (113 / 200 : ℝ)) :
    (505673747 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (514767423 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell903_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell903_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell904_leftExp :
    (6191313 / 2000000 : ℝ) ≤ Real.exp (113 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (113 / 100 : ℝ) (1035943390531 / 1000000000000 : ℝ)
    (6191313 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell904_rightExp :
    Real.exp (181 / 160 : ℝ) ≤ (3874410613 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (181 / 160 : ℝ) (1035983857861 / 1000000000000 : ℝ)
    (3874410613 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell904_denomUpper :
    Real.exp (11818696260926509 / 1250000000000000 : ℝ) ≤ (63856580703 / 5000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11818696260926509 / 1250000000000000 : ℝ) (1343754291447
    / 1000000000000 : ℝ) (63856580703 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell904_denomLower :
    (126129229102177 / 10000000000 : ℝ) ≤ Real.exp (2360619298787 / 250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2360619298787 / 250000000000 : ℝ) (335807584319 /
    250000000000 : ℝ) (126129229102177 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell904_product_lower :
    (2431322423787 / 250000000000 : ℝ) ≤ Real.pi * Real.exp (113 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell904_leftExp
    (by norm_num : (0 : ℝ) ≤ (6191313 / 2000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell904_product_upper :
    Real.pi * Real.exp (181 / 160 : ℝ) ≤ (12171821260926509 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell904_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell904_endpointLower :
    (31317573 / 625000000 : ℝ) ≤ hpThetaTraceEndpointLower (113 / 200 : ℝ) (181 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2431322423787 / 250000000000 : ℝ) (Real.pi * Real.exp (113 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell904_product_lower
  have hD : Real.exp (Real.pi * Real.exp (181 / 160 : ℝ) - (113 / 400 : ℝ)) ≤
      (63856580703 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell904_denomUpper
    linarith [hpThetaJensenCell904_product_upper]
  have hi : (1 / (63856580703 / 5000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (181 / 160 : ℝ) - (113 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (63856580703 / 5000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (63856580703 / 5000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((113 / 400 : ℝ) - Real.pi * Real.exp (181 / 160 : ℝ)) := by
    rw [show (113 / 400 : ℝ) - Real.pi * Real.exp (181 / 160 : ℝ) =
      -(Real.pi * Real.exp (181 / 160 : ℝ) - (113 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (113 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (113 / 100 : ℝ)) := by
    have h := hpThetaJensenCell904_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (63856580703 / 5000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell904_endpointUpper :
    hpThetaJensenKernelEndpointUpper (113 / 200 : ℝ) (181 / 320 : ℝ) ≤ (127524959 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (181 / 160 : ℝ)) (12171821260926509 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (181 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell904_product_upper
  have hD : (126129229102177 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (113 / 100 : ℝ) - (181 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell904_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell904_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (113 / 100 : ℝ) - (181 / 640 : ℝ)) ≤
      (1 / (126129229102177 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (126129229102177 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((181 / 640 : ℝ) - Real.pi * Real.exp (113 / 100 : ℝ)) ≤
      (2 / (126129229102177 / 10000000000 : ℝ) : ℝ) := by
    rw [show (181 / 640 : ℝ) - Real.pi * Real.exp (113 / 100 : ℝ) =
      -(Real.pi * Real.exp (113 / 100 : ℝ) - (181 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12171821260926509 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (12171821260926509 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell904_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (113 / 200 : ℝ) (181 / 320 : ℝ)) :
    (31317573 / 625000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (127524959 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell904_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell904_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell905_leftExp :
    (15497642451 / 5000000000 : ℝ) ≤ Real.exp (181 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (181 / 160 : ℝ) (51799192893 / 50000000000 : ℝ)
    (15497642451 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell905_rightExp :
    Real.exp (453 / 400 : ℝ) ≤ (6206810647 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (453 / 400 : ℝ) (1036024326771 / 1000000000000 : ℝ)
    (6206810647 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell905_denomUpper :
    Real.exp (18933647880940671 / 2000000000000000 : ℝ) ≤ (129237752993937 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (18933647880940671 / 2000000000000000 : ℝ) (1344252703871
    / 1000000000000 : ℝ) (129237752993937 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell905_denomLower :
    (127632969932841 / 10000000000 : ℝ) ≤ Real.exp (5908955567865249 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5908955567865249 / 625000000000000 : ℝ) (1343727916321 /
    1000000000000 : ℝ) (127632969932841 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell905_product_lower :
    (6085908692865249 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (181 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell905_leftExp
    (by norm_num : (0 : ℝ) ≤ (15497642451 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell905_product_upper :
    Real.pi * Real.exp (453 / 400 : ℝ) ≤ (19499272880940671 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell905_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell905_endpointLower :
    (496522577 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (181 / 320 : ℝ) (453 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6085908692865249 / 625000000000000 : ℝ) (Real.pi * Real.exp (181 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell905_product_lower
  have hD : Real.exp (Real.pi * Real.exp (453 / 400 : ℝ) - (181 / 640 : ℝ)) ≤
      (129237752993937 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell905_denomUpper
    linarith [hpThetaJensenCell905_product_upper]
  have hi : (1 / (129237752993937 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (453 / 400 : ℝ) - (181 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (129237752993937 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (129237752993937 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((181 / 640 : ℝ) - Real.pi * Real.exp (453 / 400 : ℝ)) := by
    rw [show (181 / 640 : ℝ) - Real.pi * Real.exp (453 / 400 : ℝ) =
      -(Real.pi * Real.exp (453 / 400 : ℝ) - (181 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (181 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (181 / 160 : ℝ)) := by
    have h := hpThetaJensenCell905_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (129237752993937 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell905_endpointUpper :
    hpThetaJensenKernelEndpointUpper (181 / 320 : ℝ) (453 / 800 : ℝ) ≤ (3159167 / 62500000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (453 / 400 : ℝ)) (19499272880940671 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (453 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell905_product_upper
  have hD : (127632969932841 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (181 / 160 : ℝ) - (453 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell905_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell905_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (181 / 160 : ℝ) - (453 / 1600 : ℝ)) ≤
      (1 / (127632969932841 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (127632969932841 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((453 / 1600 : ℝ) - Real.pi * Real.exp (181 / 160 : ℝ)) ≤
      (2 / (127632969932841 / 10000000000 : ℝ) : ℝ) := by
    rw [show (453 / 1600 : ℝ) - Real.pi * Real.exp (181 / 160 : ℝ) =
      -(Real.pi * Real.exp (181 / 160 : ℝ) - (453 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19499272880940671 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (19499272880940671 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell905_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (181 / 320 : ℝ) (453 / 800 : ℝ)) :
    (496522577 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3159167 / 62500000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell905_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell905_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell906_leftExp :
    (31034053233 / 10000000000 : ℝ) ≤ Real.exp (453 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (453 / 400 : ℝ) (103602432677 / 100000000000 : ℝ)
    (31034053233 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell906_rightExp :
    Real.exp (907 / 800 : ℝ) ≤ (3884108757 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (907 / 800 : ℝ) (1036064797261 / 1000000000000 : ℝ)
    (3884108757 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell906_denomUpper :
    Real.exp (11848382632229901 / 1250000000000000 : ℝ) ≤ (65391268425561 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11848382632229901 / 1250000000000000 : ℝ) (1344751941329
    / 1000000000000 : ℝ) (65391268425561 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell906_denomLower :
    (64578301861719 / 5000000000 : ℝ) ≤ Real.exp (11832744795545867 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11832744795545867 / 1250000000000000 : ℝ) (1344226318799
    / 1000000000000 : ℝ) (64578301861719 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell906_product_lower :
    (12187041670545867 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (453 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell906_leftExp
    (by norm_num : (0 : ℝ) ≤ (31034053233 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell906_product_upper :
    Real.pi * Real.exp (907 / 800 : ℝ) ≤ (12202288882229901 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell906_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell906_endpointLower :
    (245998899 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (453 / 800 : ℝ) (907 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12187041670545867 / 1250000000000000 : ℝ) (Real.pi * Real.exp (453 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell906_product_lower
  have hD : Real.exp (Real.pi * Real.exp (907 / 800 : ℝ) - (453 / 1600 : ℝ)) ≤
      (65391268425561 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell906_denomUpper
    linarith [hpThetaJensenCell906_product_upper]
  have hi : (1 / (65391268425561 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (907 / 800 : ℝ) - (453 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (65391268425561 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (65391268425561 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((453 / 1600 : ℝ) - Real.pi * Real.exp (907 / 800 : ℝ)) := by
    rw [show (453 / 1600 : ℝ) - Real.pi * Real.exp (907 / 800 : ℝ) =
      -(Real.pi * Real.exp (907 / 800 : ℝ) - (453 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (453 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (453 / 400 : ℝ)) := by
    have h := hpThetaJensenCell906_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (65391268425561 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell906_endpointUpper :
    hpThetaJensenKernelEndpointUpper (453 / 800 : ℝ) (907 / 1600 : ℝ) ≤ (500867897 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (907 / 800 : ℝ)) (12202288882229901 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (907 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell906_product_upper
  have hD : (64578301861719 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (453 / 400 : ℝ) - (907 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell906_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell906_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (453 / 400 : ℝ) - (907 / 3200 : ℝ)) ≤
      (1 / (64578301861719 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (64578301861719 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((907 / 3200 : ℝ) - Real.pi * Real.exp (453 / 400 : ℝ)) ≤
      (2 / (64578301861719 / 5000000000 : ℝ) : ℝ) := by
    rw [show (907 / 3200 : ℝ) - Real.pi * Real.exp (453 / 400 : ℝ) =
      -(Real.pi * Real.exp (453 / 400 : ℝ) - (907 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12202288882229901 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (12202288882229901 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell906_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (453 / 800 : ℝ) (907 / 1600 : ℝ)) :
    (245998899 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (500867897 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell906_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell906_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell907_leftExp :
    (15536435027 / 5000000000 : ℝ) ≤ Real.exp (907 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (907 / 800 : ℝ) (51803239863 / 50000000000 : ℝ)
    (15536435027 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell907_rightExp :
    Real.exp (227 / 200 : ℝ) ≤ (3111173543 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (227 / 200 : ℝ) (1036105269333 / 1000000000000 : ℝ)
    (3111173543 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell907_denomUpper :
    Real.exp (9490603524473999 / 1000000000000000 : ℝ) ≤ (132347804309493 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9490603524473999 / 1000000000000000 : ℝ) (1345252005437
    / 1000000000000 : ℝ) (132347804309493 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell907_denomLower :
    (130700417096593 / 10000000000 : ℝ) ≤ Real.exp (5923798748667873 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5923798748667873 / 625000000000000 : ℝ) (168090693287 /
    125000000000 : ℝ) (130700417096593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell907_product_lower :
    (6101142498667873 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (907 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell907_leftExp
    (by norm_num : (0 : ℝ) ≤ (15536435027 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell907_product_upper :
    Real.pi * Real.exp (227 / 200 : ℝ) ≤ (9774041024473999 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell907_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell907_endpointLower :
    (121876663 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (907 / 1600 : ℝ) (227 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6101142498667873 / 625000000000000 : ℝ) (Real.pi * Real.exp (907 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell907_product_lower
  have hD : Real.exp (Real.pi * Real.exp (227 / 200 : ℝ) - (907 / 3200 : ℝ)) ≤
      (132347804309493 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell907_denomUpper
    linarith [hpThetaJensenCell907_product_upper]
  have hi : (1 / (132347804309493 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (227 / 200 : ℝ) - (907 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (132347804309493 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (132347804309493 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((907 / 3200 : ℝ) - Real.pi * Real.exp (227 / 200 : ℝ)) := by
    rw [show (907 / 3200 : ℝ) - Real.pi * Real.exp (227 / 200 : ℝ) =
      -(Real.pi * Real.exp (227 / 200 : ℝ) - (907 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (907 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (907 / 800 : ℝ)) := by
    have h := hpThetaJensenCell907_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (132347804309493 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell907_endpointUpper :
    hpThetaJensenKernelEndpointUpper (907 / 1600 : ℝ) (227 / 400 : ℝ) ≤ (124075797 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (227 / 200 : ℝ)) (9774041024473999 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (227 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell907_product_upper
  have hD : (130700417096593 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (907 / 800 : ℝ) - (227 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell907_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell907_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (907 / 800 : ℝ) - (227 / 800 : ℝ)) ≤
      (1 / (130700417096593 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (130700417096593 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((227 / 800 : ℝ) - Real.pi * Real.exp (907 / 800 : ℝ)) ≤
      (2 / (130700417096593 / 10000000000 : ℝ) : ℝ) := by
    rw [show (227 / 800 : ℝ) - Real.pi * Real.exp (907 / 800 : ℝ) =
      -(Real.pi * Real.exp (907 / 800 : ℝ) - (227 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9774041024473999 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (9774041024473999 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell907_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (907 / 1600 : ℝ) (227 / 400 : ℝ)) :
    (121876663 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (124075797 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell907_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell907_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell908_leftExp :
    (7777933857 / 2500000000 : ℝ) ≤ Real.exp (227 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (227 / 200 : ℝ) (259026317333 / 250000000000 : ℝ)
    (7777933857 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell908_rightExp :
    Real.exp (909 / 800 : ℝ) ≤ (3893831177 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (909 / 800 : ℝ) (518072871493 / 500000000000 : ℝ)
    (3893831177 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell908_denomUpper :
    Real.exp (11878145268844961 / 1250000000000000 : ℝ) ≤ (133933851037811 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (11878145268844961 / 1250000000000000 : ℝ) (336438224439
    / 250000000000 : ℝ) (133933851037811 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell908_denomLower :
    (33066175297183 / 2500000000 : ℝ) ≤ Real.exp (2965617316460043 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2965617316460043 / 312500000000000 : ℝ) (168153200053 /
    125000000000 : ℝ) (33066175297183 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell908_product_lower :
    (3054386847710043 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (227 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell908_leftExp
    (by norm_num : (0 : ℝ) ≤ (7777933857 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell908_product_upper :
    Real.pi * Real.exp (909 / 800 : ℝ) ≤ (12232832768844961 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell908_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell908_endpointLower :
    (96609793 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (227 / 400 : ℝ) (909 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (3054386847710043 / 312500000000000 : ℝ) (Real.pi * Real.exp (227 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell908_product_lower
  have hD : Real.exp (Real.pi * Real.exp (909 / 800 : ℝ) - (227 / 800 : ℝ)) ≤
      (133933851037811 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell908_denomUpper
    linarith [hpThetaJensenCell908_product_upper]
  have hi : (1 / (133933851037811 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (909 / 800 : ℝ) - (227 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (133933851037811 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (133933851037811 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((227 / 800 : ℝ) - Real.pi * Real.exp (909 / 800 : ℝ)) := by
    rw [show (227 / 800 : ℝ) - Real.pi * Real.exp (909 / 800 : ℝ) =
      -(Real.pi * Real.exp (909 / 800 : ℝ) - (227 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (227 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (227 / 200 : ℝ)) := by
    have h := hpThetaJensenCell908_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (133933851037811 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell908_endpointUpper :
    hpThetaJensenKernelEndpointUpper (227 / 400 : ℝ) (909 / 1600 : ℝ) ≤ (245886207 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (909 / 800 : ℝ)) (12232832768844961 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (909 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell908_product_upper
  have hD : (33066175297183 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (227 / 200 : ℝ) - (909 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell908_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell908_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (227 / 200 : ℝ) - (909 / 3200 : ℝ)) ≤
      (1 / (33066175297183 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (33066175297183 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((909 / 3200 : ℝ) - Real.pi * Real.exp (227 / 200 : ℝ)) ≤
      (2 / (33066175297183 / 2500000000 : ℝ) : ℝ) := by
    rw [show (909 / 3200 : ℝ) - Real.pi * Real.exp (227 / 200 : ℝ) =
      -(Real.pi * Real.exp (227 / 200 : ℝ) - (909 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12232832768844961 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (12232832768844961 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell908_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (227 / 400 : ℝ) (909 / 1600 : ℝ)) :
    (96609793 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (245886207 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell908_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell908_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell909_leftExp :
    (15575324707 / 5000000000 : ℝ) ≤ Real.exp (909 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (909 / 800 : ℝ) (207229148597 / 200000000000 : ℝ)
    (15575324707 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell909_rightExp :
    Real.exp (91 / 80 : ℝ) ≤ (15594806037 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (91 / 80 : ℝ) (1036186218219 / 1000000000000 : ℝ)
    (15594806037 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell909_denomUpper :
    Real.exp (47572220982196941 / 5000000000000000 : ℝ) ≤ (135540977350567 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (47572220982196941 / 5000000000000000 : ℝ) (336563654967
    / 250000000000 : ℝ) (135540977350567 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell909_denomLower :
    (66924875747633 / 5000000000 : ℝ) ≤ Real.exp (5938680062114193 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5938680062114193 / 625000000000000 : ℝ) (336431620687 /
    250000000000 : ℝ) (66924875747633 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell909_product_lower :
    (6116414437114193 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (909 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell909_leftExp
    (by norm_num : (0 : ℝ) ≤ (15575324707 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell909_product_upper :
    Real.pi * Real.exp (91 / 80 : ℝ) ≤ (48992533482196941 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell909_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell909_endpointLower :
    (478624559 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (909 / 1600 : ℝ) (91 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6116414437114193 / 625000000000000 : ℝ) (Real.pi * Real.exp (909 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell909_product_lower
  have hD : Real.exp (Real.pi * Real.exp (91 / 80 : ℝ) - (909 / 3200 : ℝ)) ≤
      (135540977350567 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell909_denomUpper
    linarith [hpThetaJensenCell909_product_upper]
  have hi : (1 / (135540977350567 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (91 / 80 : ℝ) - (909 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (135540977350567 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (135540977350567 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((909 / 3200 : ℝ) - Real.pi * Real.exp (91 / 80 : ℝ)) := by
    rw [show (909 / 3200 : ℝ) - Real.pi * Real.exp (91 / 80 : ℝ) =
      -(Real.pi * Real.exp (91 / 80 : ℝ) - (909 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (909 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (909 / 800 : ℝ)) := by
    have h := hpThetaJensenCell909_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (135540977350567 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell909_endpointUpper :
    hpThetaJensenKernelEndpointUpper (909 / 1600 : ℝ) (91 / 160 : ℝ) ≤ (487275397 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (91 / 80 : ℝ)) (48992533482196941 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (91 / 160 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell909_product_upper
  have hD : (66924875747633 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (909 / 800 : ℝ) - (91 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell909_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell909_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (909 / 800 : ℝ) - (91 / 320 : ℝ)) ≤
      (1 / (66924875747633 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (66924875747633 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((91 / 320 : ℝ) - Real.pi * Real.exp (909 / 800 : ℝ)) ≤
      (2 / (66924875747633 / 5000000000 : ℝ) : ℝ) := by
    rw [show (91 / 320 : ℝ) - Real.pi * Real.exp (909 / 800 : ℝ) =
      -(Real.pi * Real.exp (909 / 800 : ℝ) - (91 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (48992533482196941 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (48992533482196941 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell909_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (909 / 1600 : ℝ) (91 / 160 : ℝ)) :
    (478624559 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (487275397 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell909_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell909_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell910_leftExp :
    (3898701509 / 1250000000 : ℝ) ≤ Real.exp (91 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (91 / 80 : ℝ) (518093109109 / 500000000000 : ℝ)
    (3898701509 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell910_rightExp :
    Real.exp (911 / 800 : ℝ) ≤ (15614311733 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (911 / 800 : ℝ) (518113347517 / 500000000000 : ℝ)
    (15614311733 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell910_denomUpper :
    Real.exp (47631937440210669 / 5000000000000000 : ℝ) ≤ (137169488300191 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (47631937440210669 / 5000000000000000 : ℝ) (67337858669 /
    50000000000 : ℝ) (137169488300191 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell910_denomLower :
    (105824896981 / 7812500 : ℝ) ≤ Real.exp (1486533762007791 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1486533762007791 / 156250000000000 : ℝ) (42069631089 /
    31250000000 : ℝ) (105824896981 / 7812500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell910_product_lower :
    (1531016183882791 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (91 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell910_leftExp
    (by norm_num : (0 : ℝ) ≤ (3898701509 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell910_product_upper :
    Real.pi * Real.exp (911 / 800 : ℝ) ≤ (49053812440210669 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell910_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell910_endpointLower :
    (474233259 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 160 : ℝ) (911 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1531016183882791 / 156250000000000 : ℝ) (Real.pi * Real.exp (91 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell910_product_lower
  have hD : Real.exp (Real.pi * Real.exp (911 / 800 : ℝ) - (91 / 320 : ℝ)) ≤
      (137169488300191 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell910_denomUpper
    linarith [hpThetaJensenCell910_product_upper]
  have hi : (1 / (137169488300191 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (911 / 800 : ℝ) - (91 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (137169488300191 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (137169488300191 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((91 / 320 : ℝ) - Real.pi * Real.exp (911 / 800 : ℝ)) := by
    rw [show (91 / 320 : ℝ) - Real.pi * Real.exp (911 / 800 : ℝ) =
      -(Real.pi * Real.exp (911 / 800 : ℝ) - (91 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (91 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (91 / 80 : ℝ)) := by
    have h := hpThetaJensenCell910_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (137169488300191 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell910_endpointUpper :
    hpThetaJensenKernelEndpointUpper (91 / 160 : ℝ) (911 / 1600 : ℝ) ≤ (12070299 / 250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (911 / 800 : ℝ)) (49053812440210669 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (911 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell910_product_upper
  have hD : (105824896981 / 7812500 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (91 / 80 : ℝ) - (911 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell910_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell910_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (91 / 80 : ℝ) - (911 / 3200 : ℝ)) ≤
      (1 / (105824896981 / 7812500 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (105824896981 / 7812500 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((911 / 3200 : ℝ) - Real.pi * Real.exp (91 / 80 : ℝ)) ≤
      (2 / (105824896981 / 7812500 : ℝ) : ℝ) := by
    rw [show (911 / 3200 : ℝ) - Real.pi * Real.exp (91 / 80 : ℝ) =
      -(Real.pi * Real.exp (91 / 80 : ℝ) - (911 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49053812440210669 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (49053812440210669 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell910_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (91 / 160 : ℝ) (911 / 1600 : ℝ)) :
    (474233259 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (12070299 / 250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell910_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell910_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell911_leftExp :
    (3903577933 / 1250000000 : ℝ) ≤ Real.exp (911 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (911 / 800 : ℝ) (1036226695033 / 1000000000000 : ℝ)
    (3903577933 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell911_rightExp :
    Real.exp (57 / 50 : ℝ) ≤ (31267683653 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (57 / 50 : ℝ) (103626717343 / 100000000000 : ℝ)
    (31267683653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell911_denomUpper :
    Real.exp (95383461090479229 / 10000000000000000 : ℝ) ≤ (2776393872927 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (95383461090479229 / 10000000000000000 : ℝ) (134726055989
    / 100000000000 : ℝ) (2776393872927 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell911_denomLower :
    (68541677985323 / 5000000000 : ℝ) ≤ Real.exp (1488399900711167 / 156250000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1488399900711167 / 156250000000000 : ℝ) (1346730738331 /
    1000000000000 : ℝ) (68541677985323 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell911_product_lower :
    (1532931150711167 / 156250000000000 : ℝ) ≤ Real.pi * Real.exp (911 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell911_leftExp
    (by norm_num : (0 : ℝ) ≤ (3903577933 / 1250000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell911_product_upper :
    Real.pi * Real.exp (57 / 50 : ℝ) ≤ (98230336090479229 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell911_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell911_endpointLower :
    (469874889 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (911 / 1600 : ℝ) (57 / 100 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1532931150711167 / 156250000000000 : ℝ) (Real.pi * Real.exp (911 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell911_product_lower
  have hD : Real.exp (Real.pi * Real.exp (57 / 50 : ℝ) - (911 / 3200 : ℝ)) ≤
      (2776393872927 / 200000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell911_denomUpper
    linarith [hpThetaJensenCell911_product_upper]
  have hi : (1 / (2776393872927 / 200000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (57 / 50 : ℝ) - (911 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (2776393872927 / 200000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (2776393872927 / 200000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((911 / 3200 : ℝ) - Real.pi * Real.exp (57 / 50 : ℝ)) := by
    rw [show (911 / 3200 : ℝ) - Real.pi * Real.exp (57 / 50 : ℝ) =
      -(Real.pi * Real.exp (57 / 50 : ℝ) - (911 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (911 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (911 / 800 : ℝ)) := by
    have h := hpThetaJensenCell911_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (2776393872927 / 200000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell911_endpointUpper :
    hpThetaJensenKernelEndpointUpper (911 / 1600 : ℝ) (57 / 100 : ℝ) ≤ (119595481 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (57 / 50 : ℝ)) (98230336090479229 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (57 / 100 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell911_product_upper
  have hD : (68541677985323 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (911 / 800 : ℝ) - (57 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell911_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell911_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (911 / 800 : ℝ) - (57 / 200 : ℝ)) ≤
      (1 / (68541677985323 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (68541677985323 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((57 / 200 : ℝ) - Real.pi * Real.exp (911 / 800 : ℝ)) ≤
      (2 / (68541677985323 / 5000000000 : ℝ) : ℝ) := by
    rw [show (57 / 200 : ℝ) - Real.pi * Real.exp (911 / 800 : ℝ) =
      -(Real.pi * Real.exp (911 / 800 : ℝ) - (57 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (98230336090479229 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (98230336090479229 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell911_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (911 / 1600 : ℝ) (57 / 100 : ℝ)) :
    (469874889 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (119595481 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell911_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell911_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell912_leftExp :
    (31267683651 / 10000000000 : ℝ) ≤ Real.exp (57 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (57 / 50 : ℝ) (1036267173429 / 1000000000000 : ℝ)
    (31267683651 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell912_rightExp :
    Real.exp (913 / 800 : ℝ) ≤ (3913349087 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (913 / 800 : ℝ) (1036307653407 / 1000000000000 : ℝ)
    (3913349087 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell912_denomUpper :
    Real.exp (11937900098275591 / 1250000000000000 : ℝ) ≤ (140491907975679 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (11937900098275591 / 1250000000000000 : ℝ) (1347764781 /
    1000000000 : ℝ) (140491907975679 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell912_denomLower :
    (27746504914341 / 2000000000 : ℝ) ≤ Real.exp (11922147477064049 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11922147477064049 / 1250000000000000 : ℝ) (1347234114797
    / 1000000000000 : ℝ) (27746504914341 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell912_product_lower :
    (12278788102064049 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (57 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell912_leftExp
    (by norm_num : (0 : ℝ) ≤ (31267683651 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell912_product_upper :
    Real.pi * Real.exp (913 / 800 : ℝ) ≤ (12294150098275591 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell912_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell912_endpointLower :
    (465549273 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 100 : ℝ) (913 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12278788102064049 / 1250000000000000 : ℝ) (Real.pi * Real.exp (57 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell912_product_lower
  have hD : Real.exp (Real.pi * Real.exp (913 / 800 : ℝ) - (57 / 200 : ℝ)) ≤
      (140491907975679 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell912_denomUpper
    linarith [hpThetaJensenCell912_product_upper]
  have hi : (1 / (140491907975679 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (913 / 800 : ℝ) - (57 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (140491907975679 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (140491907975679 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((57 / 200 : ℝ) - Real.pi * Real.exp (913 / 800 : ℝ)) := by
    rw [show (57 / 200 : ℝ) - Real.pi * Real.exp (913 / 800 : ℝ) =
      -(Real.pi * Real.exp (913 / 800 : ℝ) - (57 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (57 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (57 / 50 : ℝ)) := by
    have h := hpThetaJensenCell912_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (140491907975679 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell912_endpointUpper :
    hpThetaJensenKernelEndpointUpper (57 / 100 : ℝ) (913 / 1600 : ℝ) ≤ (59248139 / 1250000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (913 / 800 : ℝ)) (12294150098275591 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (913 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell912_product_upper
  have hD : (27746504914341 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (57 / 50 : ℝ) - (913 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell912_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell912_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (57 / 50 : ℝ) - (913 / 3200 : ℝ)) ≤
      (1 / (27746504914341 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (27746504914341 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((913 / 3200 : ℝ) - Real.pi * Real.exp (57 / 50 : ℝ)) ≤
      (2 / (27746504914341 / 2000000000 : ℝ) : ℝ) := by
    rw [show (913 / 3200 : ℝ) - Real.pi * Real.exp (57 / 50 : ℝ) =
      -(Real.pi * Real.exp (57 / 50 : ℝ) - (913 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (12294150098275591 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (12294150098275591 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell912_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (57 / 100 : ℝ) (913 / 1600 : ℝ)) :
    (465549273 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (59248139 / 1250000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell912_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell912_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell913_leftExp :
    (15653396347 / 5000000000 : ℝ) ≤ Real.exp (913 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (913 / 800 : ℝ) (518153826703 / 500000000000 : ℝ)
    (15653396347 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell913_rightExp :
    Real.exp (457 / 400 : ℝ) ≤ (6269190131 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (457 / 400 : ℝ) (207269626993 / 200000000000 : ℝ)
    (6269190131 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell913_denomUpper :
    Real.exp (19124618831218683 / 2000000000000000 : ℝ) ≤ (28437290145597 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19124618831218683 / 2000000000000000 : ℝ) (13482698383 /
    10000000000 : ℝ) (28437290145597 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell913_denomLower :
    (140403688317973 / 10000000000 : ℝ) ≤ Real.exp (5968557467070553 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (5968557467070553 / 625000000000000 : ℝ) (269547665169 /
    200000000000 : ℝ) (140403688317973 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell913_product_lower :
    (6147073092070553 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (913 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell913_leftExp
    (by norm_num : (0 : ℝ) ≤ (15653396347 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell913_product_upper :
    Real.pi * Real.exp (457 / 400 : ℝ) ≤ (19695243831218683 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell913_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell913_endpointLower :
    (461256237 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (913 / 1600 : ℝ) (457 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (6147073092070553 / 625000000000000 : ℝ) (Real.pi * Real.exp (913 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell913_product_lower
  have hD : Real.exp (Real.pi * Real.exp (457 / 400 : ℝ) - (913 / 3200 : ℝ)) ≤
      (28437290145597 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell913_denomUpper
    linarith [hpThetaJensenCell913_product_upper]
  have hi : (1 / (28437290145597 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (457 / 400 : ℝ) - (913 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (28437290145597 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (28437290145597 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((913 / 3200 : ℝ) - Real.pi * Real.exp (457 / 400 : ℝ)) := by
    rw [show (913 / 3200 : ℝ) - Real.pi * Real.exp (457 / 400 : ℝ) =
      -(Real.pi * Real.exp (457 / 400 : ℝ) - (913 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (913 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (913 / 800 : ℝ)) := by
    have h := hpThetaJensenCell913_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (28437290145597 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell913_endpointUpper :
    hpThetaJensenKernelEndpointUpper (913 / 1600 : ℝ) (457 / 800 : ℝ) ≤ (117405337 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (457 / 400 : ℝ)) (19695243831218683 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (457 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell913_product_upper
  have hD : (140403688317973 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (913 / 800 : ℝ) - (457 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell913_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell913_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (913 / 800 : ℝ) - (457 / 1600 : ℝ)) ≤
      (1 / (140403688317973 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (140403688317973 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((457 / 1600 : ℝ) - Real.pi * Real.exp (913 / 800 : ℝ)) ≤
      (2 / (140403688317973 / 10000000000 : ℝ) : ℝ) := by
    rw [show (457 / 1600 : ℝ) - Real.pi * Real.exp (913 / 800 : ℝ) =
      -(Real.pi * Real.exp (913 / 800 : ℝ) - (457 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19695243831218683 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (19695243831218683 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell913_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (913 / 1600 : ℝ) (457 / 800 : ℝ)) :
    (461256237 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (117405337 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell913_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell913_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell914_leftExp :
    (31345950653 / 10000000000 : ℝ) ≤ Real.exp (457 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (457 / 400 : ℝ) (259087033741 / 250000000000 : ℝ)
    (31345950653 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell914_rightExp :
    Real.exp (183 / 160 : ℝ) ≤ (31385157593 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (183 / 160 : ℝ) (207277723621 / 200000000000 : ℝ)
    (31385157593 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell914_denomUpper :
    Real.exp (95743141398065649 / 10000000000000000 : ℝ) ≤ (71951823231231 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (95743141398065649 / 10000000000000000 : ℝ)
    (1348775733423 / 1000000000000 : ℝ) (71951823231231 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell914_denomLower :
    (28419433290343 / 2000000000 : ℝ) ≤ Real.exp (11952101600482447 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11952101600482447 / 1250000000000000 : ℝ) (674121686533
    / 500000000000 : ℝ) (28419433290343 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell914_product_lower :
    (12309523475482447 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (457 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell914_leftExp
    (by norm_num : (0 : ℝ) ≤ (31345950653 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell914_product_upper :
    Real.pi * Real.exp (183 / 160 : ℝ) ≤ (98599391398065649 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell914_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell914_endpointLower :
    (91399121 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (457 / 800 : ℝ) (183 / 320 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12309523475482447 / 1250000000000000 : ℝ) (Real.pi * Real.exp (457 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell914_product_lower
  have hD : Real.exp (Real.pi * Real.exp (183 / 160 : ℝ) - (457 / 1600 : ℝ)) ≤
      (71951823231231 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell914_denomUpper
    linarith [hpThetaJensenCell914_product_upper]
  have hi : (1 / (71951823231231 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (183 / 160 : ℝ) - (457 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (71951823231231 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (71951823231231 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((457 / 1600 : ℝ) - Real.pi * Real.exp (183 / 160 : ℝ)) := by
    rw [show (457 / 1600 : ℝ) - Real.pi * Real.exp (183 / 160 : ℝ) =
      -(Real.pi * Real.exp (183 / 160 : ℝ) - (457 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (457 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (457 / 400 : ℝ)) := by
    have h := hpThetaJensenCell914_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (71951823231231 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell914_endpointUpper :
    hpThetaJensenKernelEndpointUpper (457 / 800 : ℝ) (183 / 320 : ℝ) ≤ (93058091 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (183 / 160 : ℝ)) (98599391398065649 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (183 / 320 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell914_product_upper
  have hD : (28419433290343 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (457 / 400 : ℝ) - (183 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell914_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell914_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (457 / 400 : ℝ) - (183 / 640 : ℝ)) ≤
      (1 / (28419433290343 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28419433290343 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((183 / 640 : ℝ) - Real.pi * Real.exp (457 / 400 : ℝ)) ≤
      (2 / (28419433290343 / 2000000000 : ℝ) : ℝ) := by
    rw [show (183 / 640 : ℝ) - Real.pi * Real.exp (457 / 400 : ℝ) =
      -(Real.pi * Real.exp (457 / 400 : ℝ) - (183 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (98599391398065649 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (98599391398065649 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell914_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (457 / 800 : ℝ) (183 / 320 : ℝ)) :
    (91399121 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (93058091 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell914_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell914_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell915_leftExp :
    (31385157591 / 10000000000 : ℝ) ≤ Real.exp (183 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (183 / 160 : ℝ) (129548577263 / 125000000000 : ℝ)
    (31385157591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell915_rightExp :
    Real.exp (229 / 200 : ℝ) ≤ (31424413569 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (229 / 200 : ℝ) (518214551413 / 500000000000 : ℝ)
    (31424413569 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell915_denomUpper :
    Real.exp (95863342697475417 / 10000000000000000 : ℝ) ≤ (72821912311883 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (95863342697475417 / 10000000000000000 : ℝ)
    (1349282467951 / 1000000000000 : ℝ) (72821912311883 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell915_denomLower :
    (143813283328117 / 10000000000 : ℝ) ≤ Real.exp (11967107500828109 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (11967107500828109 / 1250000000000000 : ℝ) (1348749258093
    / 1000000000000 : ℝ) (143813283328117 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell915_product_lower :
    (12324920000828109 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (183 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell915_leftExp
    (by norm_num : (0 : ℝ) ≤ (31385157591 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell915_product_upper :
    Real.pi * Real.exp (229 / 200 : ℝ) ≤ (98722717697475417 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell915_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell915_endpointLower :
    (452767203 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (183 / 320 : ℝ) (229 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12324920000828109 / 1250000000000000 : ℝ) (Real.pi * Real.exp (183 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell915_product_lower
  have hD : Real.exp (Real.pi * Real.exp (229 / 200 : ℝ) - (183 / 640 : ℝ)) ≤
      (72821912311883 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell915_denomUpper
    linarith [hpThetaJensenCell915_product_upper]
  have hi : (1 / (72821912311883 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (229 / 200 : ℝ) - (183 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (72821912311883 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (72821912311883 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((183 / 640 : ℝ) - Real.pi * Real.exp (229 / 200 : ℝ)) := by
    rw [show (183 / 640 : ℝ) - Real.pi * Real.exp (229 / 200 : ℝ) =
      -(Real.pi * Real.exp (229 / 200 : ℝ) - (183 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (183 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (183 / 160 : ℝ)) := by
    have h := hpThetaJensenCell915_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (72821912311883 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell915_endpointUpper :
    hpThetaJensenKernelEndpointUpper (183 / 320 : ℝ) (229 / 400 : ℝ) ≤ (92198451 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (229 / 200 : ℝ)) (98722717697475417 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (229 / 400 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell915_product_upper
  have hD : (143813283328117 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (183 / 160 : ℝ) - (229 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell915_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell915_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (183 / 160 : ℝ) - (229 / 800 : ℝ)) ≤
      (1 / (143813283328117 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (143813283328117 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((229 / 800 : ℝ) - Real.pi * Real.exp (183 / 160 : ℝ)) ≤
      (2 / (143813283328117 / 10000000000 : ℝ) : ℝ) := by
    rw [show (229 / 800 : ℝ) - Real.pi * Real.exp (183 / 160 : ℝ) =
      -(Real.pi * Real.exp (183 / 160 : ℝ) - (229 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (98722717697475417 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (98722717697475417 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell915_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (183 / 320 : ℝ) (229 / 400 : ℝ)) :
    (452767203 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (92198451 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell915_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell915_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell916_leftExp :
    (31424413567 / 10000000000 : ℝ) ≤ Real.exp (229 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (229 / 200 : ℝ) (41457164113 / 40000000000 : ℝ)
    (31424413567 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell916_rightExp :
    Real.exp (917 / 800 : ℝ) ≤ (31463718647 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (917 / 800 : ℝ) (1036469589129 / 1000000000000 : ℝ)
    (31463718647 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell916_denomUpper :
    Real.exp (95983698255384671 / 10000000000000000 : ℝ) ≤ (29481464007669 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (95983698255384671 / 10000000000000000 : ℝ) (84361877721
    / 62500000000 : ℝ) (29481464007669 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell916_denomLower :
    (36388092047051 / 2500000000 : ℝ) ≤ Real.exp (11982132658347333 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11982132658347333 / 1250000000000000 : ℝ) (1349255982509
    / 1000000000000 : ℝ) (36388092047051 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell916_product_lower :
    (12340335783347333 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (229 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell916_leftExp
    (by norm_num : (0 : ℝ) ≤ (31424413567 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell916_product_upper :
    Real.pi * Real.exp (917 / 800 : ℝ) ≤ (98846198255384671 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell916_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell916_endpointLower :
    (448570857 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (229 / 400 : ℝ) (917 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12340335783347333 / 1250000000000000 : ℝ) (Real.pi * Real.exp (229 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell916_product_lower
  have hD : Real.exp (Real.pi * Real.exp (917 / 800 : ℝ) - (229 / 800 : ℝ)) ≤
      (29481464007669 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell916_denomUpper
    linarith [hpThetaJensenCell916_product_upper]
  have hi : (1 / (29481464007669 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (917 / 800 : ℝ) - (229 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (29481464007669 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (29481464007669 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((229 / 800 : ℝ) - Real.pi * Real.exp (917 / 800 : ℝ)) := by
    rw [show (229 / 800 : ℝ) - Real.pi * Real.exp (917 / 800 : ℝ) =
      -(Real.pi * Real.exp (917 / 800 : ℝ) - (229 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (229 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (229 / 200 : ℝ)) := by
    have h := hpThetaJensenCell916_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (29481464007669 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell916_endpointUpper :
    hpThetaJensenKernelEndpointUpper (229 / 400 : ℝ) (917 / 1600 : ℝ) ≤ (228363287 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (917 / 800 : ℝ)) (98846198255384671 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (917 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell916_product_upper
  have hD : (36388092047051 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (229 / 200 : ℝ) - (917 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell916_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell916_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (229 / 200 : ℝ) - (917 / 3200 : ℝ)) ≤
      (1 / (36388092047051 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (36388092047051 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((917 / 3200 : ℝ) - Real.pi * Real.exp (229 / 200 : ℝ)) ≤
      (2 / (36388092047051 / 2500000000 : ℝ) : ℝ) := by
    rw [show (917 / 3200 : ℝ) - Real.pi * Real.exp (229 / 200 : ℝ) =
      -(Real.pi * Real.exp (229 / 200 : ℝ) - (917 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (98846198255384671 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (98846198255384671 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell916_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (229 / 400 : ℝ) (917 / 1600 : ℝ)) :
    (448570857 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (228363287 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell916_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell916_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell917_leftExp :
    (6292743729 / 2000000000 : ℝ) ≤ Real.exp (917 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (917 / 800 : ℝ) (129558698641 / 125000000000 : ℝ)
    (6292743729 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell917_rightExp :
    Real.exp (459 / 400 : ℝ) ≤ (31503072887 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (459 / 400 : ℝ) (1036510077013 / 1000000000000 : ℝ)
    (31503072887 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell917_denomUpper :
    Real.exp (96104208260288991 / 10000000000000000 : ℝ) ≤ (149194472582453 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (96104208260288991 / 10000000000000000 : ℝ) (675149230889
    / 500000000000 : ℝ) (149194472582453 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell917_denomLower :
    (147314755644591 / 10000000000 : ℝ) ≤ Real.exp (2399435419634571 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2399435419634571 / 250000000000000 : ℝ) (269952709593 /
    200000000000 : ℝ) (147314755644591 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell917_product_lower :
    (2471154169634571 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (917 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell917_leftExp
    (by norm_num : (0 : ℝ) ≤ (6292743729 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell917_product_upper :
    Real.pi * Real.exp (459 / 400 : ℝ) ≤ (98969833260288991 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell917_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell917_endpointLower :
    (444406393 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (917 / 1600 : ℝ) (459 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2471154169634571 / 250000000000000 : ℝ) (Real.pi * Real.exp (917 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell917_product_lower
  have hD : Real.exp (Real.pi * Real.exp (459 / 400 : ℝ) - (917 / 3200 : ℝ)) ≤
      (149194472582453 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell917_denomUpper
    linarith [hpThetaJensenCell917_product_upper]
  have hi : (1 / (149194472582453 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (459 / 400 : ℝ) - (917 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (149194472582453 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (149194472582453 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((917 / 3200 : ℝ) - Real.pi * Real.exp (459 / 400 : ℝ)) := by
    rw [show (917 / 3200 : ℝ) - Real.pi * Real.exp (459 / 400 : ℝ) =
      -(Real.pi * Real.exp (459 / 400 : ℝ) - (917 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (917 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (917 / 800 : ℝ)) := by
    have h := hpThetaJensenCell917_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (149194472582453 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell917_endpointUpper :
    hpThetaJensenKernelEndpointUpper (917 / 1600 : ℝ) (459 / 800 : ℝ) ≤ (90498647 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (459 / 400 : ℝ)) (98969833260288991 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (459 / 800 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell917_product_upper
  have hD : (147314755644591 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (917 / 800 : ℝ) - (459 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell917_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell917_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (917 / 800 : ℝ) - (459 / 1600 : ℝ)) ≤
      (1 / (147314755644591 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (147314755644591 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((459 / 1600 : ℝ) - Real.pi * Real.exp (917 / 800 : ℝ)) ≤
      (2 / (147314755644591 / 10000000000 : ℝ) : ℝ) := by
    rw [show (459 / 1600 : ℝ) - Real.pi * Real.exp (917 / 800 : ℝ) =
      -(Real.pi * Real.exp (917 / 800 : ℝ) - (459 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (98969833260288991 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (98969833260288991 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell917_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (917 / 1600 : ℝ) (459 / 800 : ℝ)) :
    (444406393 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (90498647 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell917_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell917_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell918_leftExp :
    (6300614577 / 2000000000 : ℝ) ≤ Real.exp (459 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (459 / 400 : ℝ) (259127519253 / 250000000000 : ℝ)
    (6300614577 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell918_rightExp :
    Real.exp (919 / 800 : ℝ) ≤ (31542476349 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (919 / 800 : ℝ) (518275283239 / 500000000000 : ℝ)
    (31542476349 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell918_denomUpper :
    Real.exp (96224872900683957 / 10000000000000000 : ℝ) ≤ (75502813731053 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (96224872900683957 / 10000000000000000 : ℝ) (675403862141
    / 500000000000 : ℝ) (75502813731053 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell918_denomLower :
    (149100785359901 / 10000000000 : ℝ) ≤ Real.exp (2402448168773323 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2402448168773323 / 250000000000000 : ℝ) (1350271956061 /
    1000000000000 : ℝ) (149100785359901 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell918_product_lower :
    (2474245043773323 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (459 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell918_leftExp
    (by norm_num : (0 : ℝ) ≤ (6300614577 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell918_product_upper :
    Real.pi * Real.exp (919 / 800 : ℝ) ≤ (99093622900683957 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell918_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell918_endpointLower :
    (220136819 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (459 / 800 : ℝ) (919 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2474245043773323 / 250000000000000 : ℝ) (Real.pi * Real.exp (459 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell918_product_lower
  have hD : Real.exp (Real.pi * Real.exp (919 / 800 : ℝ) - (459 / 1600 : ℝ)) ≤
      (75502813731053 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell918_denomUpper
    linarith [hpThetaJensenCell918_product_upper]
  have hi : (1 / (75502813731053 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (919 / 800 : ℝ) - (459 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (75502813731053 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (75502813731053 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((459 / 1600 : ℝ) - Real.pi * Real.exp (919 / 800 : ℝ)) := by
    rw [show (459 / 1600 : ℝ) - Real.pi * Real.exp (919 / 800 : ℝ) =
      -(Real.pi * Real.exp (919 / 800 : ℝ) - (459 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (459 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (459 / 400 : ℝ)) := by
    have h := hpThetaJensenCell918_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (75502813731053 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell918_endpointUpper :
    hpThetaJensenKernelEndpointUpper (459 / 800 : ℝ) (919 / 1600 : ℝ) ≤ (448292063 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (919 / 800 : ℝ)) (99093622900683957 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (919 / 1600 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell918_product_upper
  have hD : (149100785359901 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (459 / 400 : ℝ) - (919 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell918_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell918_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (459 / 400 : ℝ) - (919 / 3200 : ℝ)) ≤
      (1 / (149100785359901 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (149100785359901 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((919 / 3200 : ℝ) - Real.pi * Real.exp (459 / 400 : ℝ)) ≤
      (2 / (149100785359901 / 10000000000 : ℝ) : ℝ) := by
    rw [show (919 / 3200 : ℝ) - Real.pi * Real.exp (459 / 400 : ℝ) =
      -(Real.pi * Real.exp (459 / 400 : ℝ) - (919 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (99093622900683957 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (99093622900683957 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell918_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (459 / 800 : ℝ) (919 / 1600 : ℝ)) :
    (220136819 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (448292063 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell918_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell918_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell919_leftExp :
    (31542476347 / 10000000000 : ℝ) ≤ Real.exp (919 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (919 / 800 : ℝ) (1036550566477 / 1000000000000 : ℝ)
    (31542476347 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell919_rightExp :
    Real.exp (23 / 20 : ℝ) ≤ (15790964549 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (23 / 20 : ℝ) (518295528763 / 500000000000 : ℝ)
    (15790964549 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell919_denomUpper :
    Real.exp (48172846190386557 / 5000000000000000 : ℝ) ≤ (152841135533867 / 10000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_upper_scaled32 (48172846190386557 / 5000000000000000 : ℝ) (675658916361
    / 500000000000 : ℝ) (152841135533867 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell919_denomLower :
    (150910802323167 / 10000000000 : ℝ) ≤ Real.exp (12027323918990553 / 1250000000000000 : ℝ) :=
      by
  apply hpThetaJensen_exp_lower_scaled32 (12027323918990553 / 1250000000000000 : ℝ) (675390604201
    / 500000000000 : ℝ) (150910802323167 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell919_product_lower :
    (12386698918990553 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (919 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell919_leftExp
    (by norm_num : (0 : ℝ) ≤ (31542476347 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell919_product_upper :
    Real.pi * Real.exp (23 / 20 : ℝ) ≤ (49608783690386557 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell919_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell919_endpointLower :
    (436172419 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (919 / 1600 : ℝ) (23 / 40 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (12386698918990553 / 1250000000000000 : ℝ) (Real.pi * Real.exp (919 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell919_product_lower
  have hD : Real.exp (Real.pi * Real.exp (23 / 20 : ℝ) - (919 / 3200 : ℝ)) ≤
      (152841135533867 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell919_denomUpper
    linarith [hpThetaJensenCell919_product_upper]
  have hi : (1 / (152841135533867 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (23 / 20 : ℝ) - (919 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (152841135533867 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (152841135533867 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((919 / 3200 : ℝ) - Real.pi * Real.exp (23 / 20 : ℝ)) := by
    rw [show (919 / 3200 : ℝ) - Real.pi * Real.exp (23 / 20 : ℝ) =
      -(Real.pi * Real.exp (23 / 20 : ℝ) - (919 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (919 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (919 / 800 : ℝ)) := by
    have h := hpThetaJensenCell919_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (152841135533867 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell919_endpointUpper :
    hpThetaJensenKernelEndpointUpper (919 / 1600 : ℝ) (23 / 40 : ℝ) ≤ (444122883 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (23 / 20 : ℝ)) (49608783690386557 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (23 / 40 : ℝ) (by norm_num)
      norm_num at h ⊢
      exact h)
    hpThetaJensenCell919_product_upper
  have hD : (150910802323167 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (919 / 800 : ℝ) - (23 / 80 : ℝ)) := by
    apply le_trans hpThetaJensenCell919_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell919_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (919 / 800 : ℝ) - (23 / 80 : ℝ)) ≤
      (1 / (150910802323167 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (150910802323167 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((23 / 80 : ℝ) - Real.pi * Real.exp (919 / 800 : ℝ)) ≤
      (2 / (150910802323167 / 10000000000 : ℝ) : ℝ) := by
    rw [show (23 / 80 : ℝ) - Real.pi * Real.exp (919 / 800 : ℝ) =
      -(Real.pi * Real.exp (919 / 800 : ℝ) - (23 / 80 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (49608783690386557 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (49608783690386557 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell919_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (919 / 1600 : ℝ) (23 / 40 : ℝ)) :
    (436172419 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (444122883 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell919_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell919_endpointUpper

def hpThetaJensenCellsBatch045Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (519657191 / 10000000000 : ℝ)
  | 1 => (25748079 / 500000000 : ℝ)
  | 2 => (127575123 / 2500000000 : ℝ)
  | 3 => (505673747 / 10000000000 : ℝ)
  | 4 => (31317573 / 625000000 : ℝ)
  | 5 => (496522577 / 10000000000 : ℝ)
  | 6 => (245998899 / 5000000000 : ℝ)
  | 7 => (121876663 / 2500000000 : ℝ)
  | 8 => (96609793 / 2000000000 : ℝ)
  | 9 => (478624559 / 10000000000 : ℝ)
  | 10 => (474233259 / 10000000000 : ℝ)
  | 11 => (469874889 / 10000000000 : ℝ)
  | 12 => (465549273 / 10000000000 : ℝ)
  | 13 => (461256237 / 10000000000 : ℝ)
  | 14 => (91399121 / 2000000000 : ℝ)
  | 15 => (452767203 / 10000000000 : ℝ)
  | 16 => (448570857 / 10000000000 : ℝ)
  | 17 => (444406393 / 10000000000 : ℝ)
  | 18 => (220136819 / 5000000000 : ℝ)
  | 19 => (436172419 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch045Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (528978811 / 10000000000 : ℝ)
  | 1 => (524206731 / 10000000000 : ℝ)
  | 2 => (259734831 / 5000000000 : ℝ)
  | 3 => (514767423 / 10000000000 : ℝ)
  | 4 => (127524959 / 2500000000 : ℝ)
  | 5 => (3159167 / 62500000 : ℝ)
  | 6 => (500867897 / 10000000000 : ℝ)
  | 7 => (124075797 / 2500000000 : ℝ)
  | 8 => (245886207 / 5000000000 : ℝ)
  | 9 => (487275397 / 10000000000 : ℝ)
  | 10 => (12070299 / 250000000 : ℝ)
  | 11 => (119595481 / 2500000000 : ℝ)
  | 12 => (59248139 / 1250000000 : ℝ)
  | 13 => (117405337 / 2500000000 : ℝ)
  | 14 => (93058091 / 2000000000 : ℝ)
  | 15 => (92198451 / 2000000000 : ℝ)
  | 16 => (228363287 / 5000000000 : ℝ)
  | 17 => (90498647 / 2000000000 : ℝ)
  | 18 => (448292063 / 10000000000 : ℝ)
  | 19 => (444122883 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch045_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch045Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch045Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell900_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell901_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell902_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell903_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell904_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell905_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell906_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell907_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell908_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell909_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell910_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell911_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell912_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell913_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell914_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell915_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell916_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell917_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell918_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell919_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper] at h ⊢
    exact h

end HodgeProofHP
