import HodgeProofHP.Stage5ThetaJensenCell400Certificate

/-! Rational kernel certificates for twenty consecutive cells. -/

noncomputable section
namespace HodgeProofHP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell160_leftExp :
    (12214027581 / 10000000000 : ℝ) ≤ Real.exp (1 / 5 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1 / 5 : ℝ) (1006269572003 / 1000000000000 : ℝ)
    (12214027581 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell160_rightExp :
    Real.exp (161 / 800 : ℝ) ≤ (12229304663 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (161 / 800 : ℝ) (1006308880177 / 1000000000000 : ℝ)
    (12229304663 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell160_denomUpper :
    Real.exp (37919497924148159 / 10000000000000000 : ℝ) ≤ (443427752489 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (37919497924148159 / 10000000000000000 : ℝ)
    (1125805107727 / 1000000000000 : ℝ) (443427752489 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell160_denomLower :
    (220583111341 / 5000000000 : ℝ) ≤ Real.exp (4733545792031119 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4733545792031119 / 1250000000000000 : ℝ) (281406308491 /
    250000000000 : ℝ) (220583111341 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell160_product_lower :
    (4796436417031119 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (1 / 5 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell160_leftExp
    (by norm_num : (0 : ℝ) ≤ (12214027581 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell160_product_upper :
    Real.pi * Real.exp (161 / 800 : ℝ) ≤ (38419497924148159 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell160_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell160_endpointLower :
    (16179392873 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 10 : ℝ) (161 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4796436417031119 / 1250000000000000 : ℝ) (Real.pi * Real.exp (1 / 5 : ℝ))
    (by norm_num) hpThetaJensenCell160_product_lower
  have hD : Real.exp (Real.pi * Real.exp (161 / 800 : ℝ) - (1 / 20 : ℝ)) ≤
      (443427752489 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell160_denomUpper
    linarith [hpThetaJensenCell160_product_upper]
  have hi : (1 / (443427752489 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (161 / 800 : ℝ) - (1 / 20 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (443427752489 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (443427752489 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((1 / 20 : ℝ) - Real.pi * Real.exp (161 / 800 : ℝ)) := by
    rw [show (1 / 20 : ℝ) - Real.pi * Real.exp (161 / 800 : ℝ) =
      -(Real.pi * Real.exp (161 / 800 : ℝ) - (1 / 20 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (1 / 5 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 5 : ℝ)) := by
    have h := hpThetaJensenCell160_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (443427752489 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell160_endpointUpper :
    hpThetaJensenKernelEndpointUpper (1 / 10 : ℝ) (161 / 1600 : ℝ) ≤ (817954651 / 500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (161 / 800 : ℝ)) (38419497924148159 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (161 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell160_product_upper
  have hD : (220583111341 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (1 / 5 : ℝ) - (161 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell160_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell160_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (1 / 5 : ℝ) - (161 / 3200 : ℝ)) ≤
      (1 / (220583111341 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (220583111341 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((161 / 3200 : ℝ) - Real.pi * Real.exp (1 / 5 : ℝ)) ≤
      (2 / (220583111341 / 5000000000 : ℝ) : ℝ) := by
    rw [show (161 / 3200 : ℝ) - Real.pi * Real.exp (1 / 5 : ℝ) =
      -(Real.pi * Real.exp (1 / 5 : ℝ) - (161 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38419497924148159 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (38419497924148159 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell160_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (1 / 10 : ℝ) (161 / 1600 : ℝ)) :
    (16179392873 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (817954651 / 500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell160_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell160_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell161_leftExp :
    (6114652331 / 5000000000 : ℝ) ≤ Real.exp (161 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (161 / 800 : ℝ) (62894305011 / 62500000000 : ℝ)
    (6114652331 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell161_rightExp :
    Real.exp (81 / 400 : ℝ) ≤ (3061150213 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (81 / 400 : ℝ) (503174094943 / 500000000000 : ℝ)
    (3061150213 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell161_denomUpper :
    Real.exp (9491106831109309 / 2500000000000000 : ℝ) ≤ (445424529131 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9491106831109309 / 2500000000000000 : ℝ) (281490796697 /
    250000000000 : ℝ) (445424529131 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell161_denomLower :
    (443150154649 / 10000000000 : ℝ) ≤ Real.exp (2369577230731369 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2369577230731369 / 625000000000000 : ℝ) (562891538263 /
    500000000000 : ℝ) (443150154649 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell161_product_lower :
    (2401217855731369 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (161 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell161_leftExp
    (by norm_num : (0 : ℝ) ≤ (6114652331 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell161_product_upper :
    Real.pi * Real.exp (81 / 400 : ℝ) ≤ (9616888081109309 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell161_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell161_endpointLower :
    (16160126559 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (161 / 1600 : ℝ) (81 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2401217855731369 / 625000000000000 : ℝ) (Real.pi * Real.exp (161 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell161_product_lower
  have hD : Real.exp (Real.pi * Real.exp (81 / 400 : ℝ) - (161 / 3200 : ℝ)) ≤
      (445424529131 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell161_denomUpper
    linarith [hpThetaJensenCell161_product_upper]
  have hi : (1 / (445424529131 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (81 / 400 : ℝ) - (161 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (445424529131 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (445424529131 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((161 / 3200 : ℝ) - Real.pi * Real.exp (81 / 400 : ℝ)) := by
    rw [show (161 / 3200 : ℝ) - Real.pi * Real.exp (81 / 400 : ℝ) =
      -(Real.pi * Real.exp (81 / 400 : ℝ) - (161 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (161 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (161 / 800 : ℝ)) := by
    have h := hpThetaJensenCell161_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (445424529131 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell161_endpointUpper :
    hpThetaJensenKernelEndpointUpper (161 / 1600 : ℝ) (81 / 800 : ℝ) ≤ (8169841999 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (81 / 400 : ℝ)) (9616888081109309 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (81 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell161_product_upper
  have hD : (443150154649 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (161 / 800 : ℝ) - (81 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell161_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell161_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (161 / 800 : ℝ) - (81 / 1600 : ℝ)) ≤
      (1 / (443150154649 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (443150154649 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((81 / 1600 : ℝ) - Real.pi * Real.exp (161 / 800 : ℝ)) ≤
      (2 / (443150154649 / 10000000000 : ℝ) : ℝ) := by
    rw [show (81 / 1600 : ℝ) - Real.pi * Real.exp (161 / 800 : ℝ) =
      -(Real.pi * Real.exp (161 / 800 : ℝ) - (81 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9616888081109309 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9616888081109309 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell161_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (161 / 1600 : ℝ) (81 / 800 : ℝ)) :
    (16160126559 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8169841999 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell161_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell161_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell162_leftExp :
    (12244600851 / 10000000000 : ℝ) ≤ Real.exp (81 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (81 / 400 : ℝ) (201269637977 / 200000000000 : ℝ)
    (12244600851 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell162_rightExp :
    Real.exp (163 / 800 : ℝ) ≤ (12259916173 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (163 / 800 : ℝ) (100638750113 / 100000000000 : ℝ)
    (12259916173 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell162_denomUpper :
    Real.exp (38009416829683589 / 10000000000000000 : ℝ) ≤ (89486597329 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38009416829683589 / 10000000000000000 : ℝ)
    (1126121499563 / 1000000000000 : ℝ) (89486597329 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell162_denomLower :
    (89029136113 / 2000000000 : ℝ) ≤ Real.exp (4744770634586849 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4744770634586849 / 1250000000000000 : ℝ) (1125941152439
    / 1000000000000 : ℝ) (89029136113 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell162_product_lower :
    (4808442509586849 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (81 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell162_leftExp
    (by norm_num : (0 : ℝ) ≤ (12244600851 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell162_product_upper :
    Real.pi * Real.exp (163 / 800 : ℝ) ≤ (38515666829683589 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell162_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell162_endpointLower :
    (16140759673 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 800 : ℝ) (163 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4808442509586849 / 1250000000000000 : ℝ) (Real.pi * Real.exp (81 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell162_product_lower
  have hD : Real.exp (Real.pi * Real.exp (163 / 800 : ℝ) - (81 / 1600 : ℝ)) ≤
      (89486597329 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell162_denomUpper
    linarith [hpThetaJensenCell162_product_upper]
  have hi : (1 / (89486597329 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (163 / 800 : ℝ) - (81 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (89486597329 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (89486597329 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((81 / 1600 : ℝ) - Real.pi * Real.exp (163 / 800 : ℝ)) := by
    rw [show (81 / 1600 : ℝ) - Real.pi * Real.exp (163 / 800 : ℝ) =
      -(Real.pi * Real.exp (163 / 800 : ℝ) - (81 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (81 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (81 / 400 : ℝ)) := by
    have h := hpThetaJensenCell162_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (89486597329 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell162_endpointUpper :
    hpThetaJensenKernelEndpointUpper (81 / 800 : ℝ) (163 / 1600 : ℝ) ≤ (3264034663 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (163 / 800 : ℝ)) (38515666829683589 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (163 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell162_product_upper
  have hD : (89029136113 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (81 / 400 : ℝ) - (163 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell162_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell162_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (81 / 400 : ℝ) - (163 / 3200 : ℝ)) ≤
      (1 / (89029136113 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (89029136113 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((163 / 3200 : ℝ) - Real.pi * Real.exp (81 / 400 : ℝ)) ≤
      (2 / (89029136113 / 2000000000 : ℝ) : ℝ) := by
    rw [show (163 / 3200 : ℝ) - Real.pi * Real.exp (81 / 400 : ℝ) =
      -(Real.pi * Real.exp (81 / 400 : ℝ) - (163 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38515666829683589 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (38515666829683589 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell162_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (81 / 800 : ℝ) (163 / 1600 : ℝ)) :
    (16140759673 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3264034663 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell162_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell162_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell163_leftExp :
    (3064979043 / 2500000000 : ℝ) ≤ Real.exp (163 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (163 / 800 : ℝ) (1006387501129 / 1000000000000 : ℝ)
    (3064979043 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell163_rightExp :
    Real.exp (41 / 200 : ℝ) ≤ (245505013 / 200000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (41 / 200 : ℝ) (1006426813909 / 1000000000000 : ℝ)
    (245505013 / 200000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell163_denomUpper :
    Real.exp (761089330305709 / 200000000000000 : ℝ) ≤ (224726602639 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (761089330305709 / 200000000000000 : ℝ) (1126280046409 /
    1000000000000 : ℝ) (224726602639 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell163_denomLower :
    (447152880041 / 10000000000 : ℝ) ≤ Real.exp (1187598580207057 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1187598580207057 / 312500000000000 : ℝ) (563049731031 /
    500000000000 : ℝ) (447152880041 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell163_product_lower :
    (1203614205207057 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (163 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell163_leftExp
    (by norm_num : (0 : ℝ) ≤ (3064979043 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell163_product_upper :
    Real.pi * Real.exp (41 / 200 : ℝ) ≤ (771276830305709 / 200000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell163_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell163_endpointLower :
    (3224258517 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (163 / 1600 : ℝ) (41 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1203614205207057 / 312500000000000 : ℝ) (Real.pi * Real.exp (163 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell163_product_lower
  have hD : Real.exp (Real.pi * Real.exp (41 / 200 : ℝ) - (163 / 3200 : ℝ)) ≤
      (224726602639 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell163_denomUpper
    linarith [hpThetaJensenCell163_product_upper]
  have hi : (1 / (224726602639 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (41 / 200 : ℝ) - (163 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (224726602639 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (224726602639 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((163 / 3200 : ℝ) - Real.pi * Real.exp (41 / 200 : ℝ)) := by
    rw [show (163 / 3200 : ℝ) - Real.pi * Real.exp (41 / 200 : ℝ) =
      -(Real.pi * Real.exp (41 / 200 : ℝ) - (163 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (163 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (163 / 800 : ℝ)) := by
    have h := hpThetaJensenCell163_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (224726602639 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell163_endpointUpper :
    hpThetaJensenKernelEndpointUpper (163 / 1600 : ℝ) (41 / 400 : ℝ) ≤ (3260112269 / 2000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (41 / 200 : ℝ)) (771276830305709 / 200000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (41 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell163_product_upper
  have hD : (447152880041 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (163 / 800 : ℝ) - (41 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell163_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell163_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (163 / 800 : ℝ) - (41 / 800 : ℝ)) ≤
      (1 / (447152880041 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (447152880041 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((41 / 800 : ℝ) - Real.pi * Real.exp (163 / 800 : ℝ)) ≤
      (2 / (447152880041 / 10000000000 : ℝ) : ℝ) := by
    rw [show (41 / 800 : ℝ) - Real.pi * Real.exp (163 / 800 : ℝ) =
      -(Real.pi * Real.exp (163 / 800 : ℝ) - (41 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (771276830305709 / 200000000000000 : ℝ) ^ 2 - 6 *
      (771276830305709 / 200000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell163_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (163 / 1600 : ℝ) (41 / 400 : ℝ)) :
    (3224258517 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3260112269 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell163_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell163_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell164_leftExp :
    (12275250649 / 10000000000 : ℝ) ≤ Real.exp (41 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (41 / 200 : ℝ) (251606703477 / 250000000000 : ℝ)
    (12275250649 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell164_rightExp :
    Real.exp (33 / 160 : ℝ) ≤ (3072651077 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (33 / 160 : ℝ) (31452066507 / 31250000000 : ℝ)
    (3072651077 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell164_denomUpper :
    Real.exp (9524894114945661 / 2500000000000000 : ℝ) ≤ (451485266051 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9524894114945661 / 2500000000000000 : ℝ) (225287765539 /
    200000000000 : ℝ) (451485266051 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell164_denomLower :
    (28073239579 / 625000000 : ℝ) ≤ Real.exp (4756025529611651 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4756025529611651 / 1250000000000000 : ℝ) (1126258005751
    / 1000000000000 : ℝ) (28073239579 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell164_product_lower :
    (4820478654611651 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (41 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell164_leftExp
    (by norm_num : (0 : ℝ) ≤ (12275250649 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell164_product_upper :
    Real.pi * Real.exp (33 / 160 : ℝ) ≤ (9653019114945661 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell164_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell164_endpointLower :
    (16101725663 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 400 : ℝ) (33 / 320 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4820478654611651 / 1250000000000000 : ℝ) (Real.pi * Real.exp (41 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell164_product_lower
  have hD : Real.exp (Real.pi * Real.exp (33 / 160 : ℝ) - (41 / 800 : ℝ)) ≤
      (451485266051 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell164_denomUpper
    linarith [hpThetaJensenCell164_product_upper]
  have hi : (1 / (451485266051 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (33 / 160 : ℝ) - (41 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (451485266051 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (451485266051 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((41 / 800 : ℝ) - Real.pi * Real.exp (33 / 160 : ℝ)) := by
    rw [show (41 / 800 : ℝ) - Real.pi * Real.exp (33 / 160 : ℝ) =
      -(Real.pi * Real.exp (33 / 160 : ℝ) - (41 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (41 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (41 / 200 : ℝ)) := by
    have h := hpThetaJensenCell164_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (451485266051 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell164_endpointUpper :
    hpThetaJensenKernelEndpointUpper (41 / 400 : ℝ) (33 / 320 : ℝ) ≤ (3256169693 / 2000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (33 / 160 : ℝ)) (9653019114945661 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (33 / 320 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell164_product_upper
  have hD : (28073239579 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (41 / 200 : ℝ) - (33 / 640 : ℝ)) := by
    apply le_trans hpThetaJensenCell164_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell164_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (41 / 200 : ℝ) - (33 / 640 : ℝ)) ≤
      (1 / (28073239579 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28073239579 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((33 / 640 : ℝ) - Real.pi * Real.exp (41 / 200 : ℝ)) ≤
      (2 / (28073239579 / 625000000 : ℝ) : ℝ) := by
    rw [show (33 / 640 : ℝ) - Real.pi * Real.exp (41 / 200 : ℝ) =
      -(Real.pi * Real.exp (41 / 200 : ℝ) - (33 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9653019114945661 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9653019114945661 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell164_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (41 / 400 : ℝ) (33 / 320 : ℝ)) :
    (16101725663 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (3256169693 / 2000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell164_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell164_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell165_leftExp :
    (6145302153 / 5000000000 : ℝ) ≤ Real.exp (33 / 160 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (33 / 160 : ℝ) (1006466128223 / 1000000000000 : ℝ)
    (6145302153 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell165_rightExp :
    Real.exp (83 / 400 : ℝ) ≤ (12305977169 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (83 / 400 : ℝ) (40260217763 / 40000000000 : ℝ)
    (12305977169 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell165_denomUpper :
    Real.exp (38144746732290217 / 10000000000000000 : ℝ) ≤ (453529250193 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38144746732290217 / 10000000000000000 : ℝ) (563298921879
    / 500000000000 : ℝ) (453529250193 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell165_denomLower :
    (28200163817 / 625000000 : ℝ) ≤ Real.exp (2380832135180947 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2380832135180947 / 625000000000000 : ℝ) (225283356773 /
    200000000000 : ℝ) (28200163817 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell165_product_lower :
    (2413254010180947 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (33 / 160 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell165_leftExp
    (by norm_num : (0 : ℝ) ≤ (6145302153 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell165_product_upper :
    Real.pi * Real.exp (83 / 400 : ℝ) ≤ (38660371732290217 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell165_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell165_endpointLower :
    (16082059291 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 320 : ℝ) (83 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2413254010180947 / 625000000000000 : ℝ) (Real.pi * Real.exp (33 / 160 : ℝ))
    (by norm_num) hpThetaJensenCell165_product_lower
  have hD : Real.exp (Real.pi * Real.exp (83 / 400 : ℝ) - (33 / 640 : ℝ)) ≤
      (453529250193 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell165_denomUpper
    linarith [hpThetaJensenCell165_product_upper]
  have hi : (1 / (453529250193 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (83 / 400 : ℝ) - (33 / 640 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (453529250193 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (453529250193 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((33 / 640 : ℝ) - Real.pi * Real.exp (83 / 400 : ℝ)) := by
    rw [show (33 / 640 : ℝ) - Real.pi * Real.exp (83 / 400 : ℝ) =
      -(Real.pi * Real.exp (83 / 400 : ℝ) - (33 / 640 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (33 / 160 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (33 / 160 : ℝ)) := by
    have h := hpThetaJensenCell165_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (453529250193 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell165_endpointUpper :
    hpThetaJensenKernelEndpointUpper (33 / 320 : ℝ) (83 / 800 : ℝ) ≤ (16261035043 / 10000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (83 / 400 : ℝ)) (38660371732290217 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (83 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell165_product_upper
  have hD : (28200163817 / 625000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (33 / 160 : ℝ) - (83 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell165_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell165_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (33 / 160 : ℝ) - (83 / 1600 : ℝ)) ≤
      (1 / (28200163817 / 625000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (28200163817 / 625000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((83 / 1600 : ℝ) - Real.pi * Real.exp (33 / 160 : ℝ)) ≤
      (2 / (28200163817 / 625000000 : ℝ) : ℝ) := by
    rw [show (83 / 1600 : ℝ) - Real.pi * Real.exp (33 / 160 : ℝ) =
      -(Real.pi * Real.exp (33 / 160 : ℝ) - (83 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38660371732290217 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (38660371732290217 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell165_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (33 / 320 : ℝ) (83 / 800 : ℝ)) :
    (16082059291 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16261035043 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell165_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell165_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell166_leftExp :
    (769123573 / 625000000 : ℝ) ≤ Real.exp (83 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (83 / 400 : ℝ) (503252722037 / 500000000000 : ℝ)
    (769123573 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell166_rightExp :
    Real.exp (167 / 800 : ℝ) ≤ (12321369259 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (167 / 800 : ℝ) (503272380731 / 500000000000 : ℝ)
    (12321369259 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell166_denomUpper :
    Real.exp (38189977414489587 / 10000000000000000 : ℝ) ≤ (91117048023 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38189977414489587 / 10000000000000000 : ℝ) (563378547489
    / 500000000000 : ℝ) (91117048023 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell166_denomLower :
    (1770489551 / 39062500 : ℝ) ≤ Real.exp (297956909556027 / 78125000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (297956909556027 / 78125000000000 : ℝ) (1126575796773 /
    1000000000000 : ℝ) (1770489551 / 39062500 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell166_product_lower :
    (302034057993527 / 78125000000000 : ℝ) ≤ Real.pi * Real.exp (83 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell166_leftExp
    (by norm_num : (0 : ℝ) ≤ (769123573 / 625000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell166_product_upper :
    Real.pi * Real.exp (167 / 800 : ℝ) ≤ (38708727414489587 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell166_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell166_endpointLower :
    (8031146919 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 800 : ℝ) (167 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (302034057993527 / 78125000000000 : ℝ) (Real.pi * Real.exp (83 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell166_product_lower
  have hD : Real.exp (Real.pi * Real.exp (167 / 800 : ℝ) - (83 / 1600 : ℝ)) ≤
      (91117048023 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell166_denomUpper
    linarith [hpThetaJensenCell166_product_upper]
  have hi : (1 / (91117048023 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (167 / 800 : ℝ) - (83 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (91117048023 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (91117048023 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((83 / 1600 : ℝ) - Real.pi * Real.exp (167 / 800 : ℝ)) := by
    rw [show (83 / 1600 : ℝ) - Real.pi * Real.exp (167 / 800 : ℝ) =
      -(Real.pi * Real.exp (167 / 800 : ℝ) - (83 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (83 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (83 / 400 : ℝ)) := by
    have h := hpThetaJensenCell166_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (91117048023 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell166_endpointUpper :
    hpThetaJensenKernelEndpointUpper (83 / 800 : ℝ) (167 / 1600 : ℝ) ≤ (16241121459 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (167 / 800 : ℝ)) (38708727414489587 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (167 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell166_product_upper
  have hD : (1770489551 / 39062500 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (83 / 400 : ℝ) - (167 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell166_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell166_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (83 / 400 : ℝ) - (167 / 3200 : ℝ)) ≤
      (1 / (1770489551 / 39062500 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (1770489551 / 39062500 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((167 / 3200 : ℝ) - Real.pi * Real.exp (83 / 400 : ℝ)) ≤
      (2 / (1770489551 / 39062500 : ℝ) : ℝ) := by
    rw [show (167 / 3200 : ℝ) - Real.pi * Real.exp (83 / 400 : ℝ) =
      -(Real.pi * Real.exp (83 / 400 : ℝ) - (167 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38708727414489587 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (38708727414489587 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell166_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (83 / 800 : ℝ) (167 / 1600 : ℝ)) :
    (8031146919 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16241121459 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell166_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell166_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell167_leftExp :
    (12321369257 / 10000000000 : ℝ) ≤ Real.exp (167 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (167 / 800 : ℝ) (1006544761461 / 1000000000000 : ℝ)
    (12321369257 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell167_rightExp :
    Real.exp (21 / 100 : ℝ) ≤ (61683903 / 50000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (21 / 100 : ℝ) (201316816077 / 200000000000 : ℝ)
    (61683903 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell167_denomUpper :
    Real.exp (191176342877479 / 50000000000000 : ℝ) ≤ (91530663661 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (191176342877479 / 50000000000000 : ℝ) (281729145423 /
    250000000000 : ℝ) (91530663661 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell167_denomLower :
    (3557031461 / 78125000 : ℝ) ≤ Real.exp (4772964385854643 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4772964385854643 / 1250000000000000 : ℝ) (1126735044811
    / 1000000000000 : ℝ) (3557031461 / 78125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell167_product_lower :
    (4838589385854643 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (167 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell167_leftExp
    (by norm_num : (0 : ℝ) ≤ (12321369257 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell167_product_upper :
    Real.pi * Real.exp (21 / 100 : ℝ) ≤ (193785717877479 / 50000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell167_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell167_endpointLower :
    (4010607421 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (167 / 1600 : ℝ) (21 / 200 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4838589385854643 / 1250000000000000 : ℝ) (Real.pi * Real.exp (167 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell167_product_lower
  have hD : Real.exp (Real.pi * Real.exp (21 / 100 : ℝ) - (167 / 3200 : ℝ)) ≤
      (91530663661 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell167_denomUpper
    linarith [hpThetaJensenCell167_product_upper]
  have hi : (1 / (91530663661 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (21 / 100 : ℝ) - (167 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (91530663661 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (91530663661 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((167 / 3200 : ℝ) - Real.pi * Real.exp (21 / 100 : ℝ)) := by
    rw [show (167 / 3200 : ℝ) - Real.pi * Real.exp (21 / 100 : ℝ) =
      -(Real.pi * Real.exp (21 / 100 : ℝ) - (167 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (167 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (167 / 800 : ℝ)) := by
    have h := hpThetaJensenCell167_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (91530663661 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell167_endpointUpper :
    hpThetaJensenKernelEndpointUpper (167 / 1600 : ℝ) (21 / 200 : ℝ) ≤ (126727407 / 78125000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (21 / 100 : ℝ)) (193785717877479 / 50000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (21 / 200 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell167_product_upper
  have hD : (3557031461 / 78125000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (167 / 800 : ℝ) - (21 / 400 : ℝ)) := by
    apply le_trans hpThetaJensenCell167_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell167_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (167 / 800 : ℝ) - (21 / 400 : ℝ)) ≤
      (1 / (3557031461 / 78125000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (3557031461 / 78125000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((21 / 400 : ℝ) - Real.pi * Real.exp (167 / 800 : ℝ)) ≤
      (2 / (3557031461 / 78125000 : ℝ) : ℝ) := by
    rw [show (21 / 400 : ℝ) - Real.pi * Real.exp (167 / 800 : ℝ) =
      -(Real.pi * Real.exp (167 / 800 : ℝ) - (21 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (193785717877479 / 50000000000000 : ℝ) ^ 2 - 6 *
      (193785717877479 / 50000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell167_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (167 / 1600 : ℝ) (21 / 200 : ℝ)) :
    (4010607421 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (126727407 / 78125000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell167_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell167_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell168_leftExp :
    (12336780599 / 10000000000 : ℝ) ≤ Real.exp (21 / 100 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (21 / 100 : ℝ) (491496133 / 488281250 : ℝ) (12336780599 /
    10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell168_rightExp :
    Real.exp (169 / 800 : ℝ) ≤ (6176105609 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (169 / 800 : ℝ) (251655850211 / 250000000000 : ℝ)
    (6176105609 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell168_denomUpper :
    Real.exp (19140310148495137 / 5000000000000000 : ℝ) ≤ (57466696059 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19140310148495137 / 5000000000000000 : ℝ) (563538152141
    / 500000000000 : ℝ) (57466696059 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell168_denomLower :
    (114341702487 / 2500000000 : ℝ) ≤ Real.exp (4778625779446701 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4778625779446701 / 1250000000000000 : ℝ) (1126894528361
    / 1000000000000 : ℝ) (114341702487 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell168_product_lower :
    (4844641404446701 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (21 / 100 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell168_leftExp
    (by norm_num : (0 : ℝ) ≤ (12336780599 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell168_product_upper :
    Real.pi * Real.exp (169 / 800 : ℝ) ≤ (19402810148495137 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell168_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell168_endpointLower :
    (8011233603 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 200 : ℝ) (169 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4844641404446701 / 1250000000000000 : ℝ) (Real.pi * Real.exp (21 / 100 : ℝ))
    (by norm_num) hpThetaJensenCell168_product_lower
  have hD : Real.exp (Real.pi * Real.exp (169 / 800 : ℝ) - (21 / 400 : ℝ)) ≤
      (57466696059 / 1250000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell168_denomUpper
    linarith [hpThetaJensenCell168_product_upper]
  have hi : (1 / (57466696059 / 1250000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (169 / 800 : ℝ) - (21 / 400 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (57466696059 / 1250000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (57466696059 / 1250000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((21 / 400 : ℝ) - Real.pi * Real.exp (169 / 800 : ℝ)) := by
    rw [show (21 / 400 : ℝ) - Real.pi * Real.exp (169 / 800 : ℝ) =
      -(Real.pi * Real.exp (169 / 800 : ℝ) - (21 / 400 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (21 / 100 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (21 / 100 : ℝ)) := by
    have h := hpThetaJensenCell168_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (57466696059 / 1250000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell168_endpointUpper :
    hpThetaJensenKernelEndpointUpper (21 / 200 : ℝ) (169 / 1600 : ℝ) ≤ (16200995331 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (169 / 800 : ℝ)) (19402810148495137 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (169 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell168_product_upper
  have hD : (114341702487 / 2500000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (21 / 100 : ℝ) - (169 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell168_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell168_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (21 / 100 : ℝ) - (169 / 3200 : ℝ)) ≤
      (1 / (114341702487 / 2500000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (114341702487 / 2500000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((169 / 3200 : ℝ) - Real.pi * Real.exp (21 / 100 : ℝ)) ≤
      (2 / (114341702487 / 2500000000 : ℝ) : ℝ) := by
    rw [show (169 / 3200 : ℝ) - Real.pi * Real.exp (21 / 100 : ℝ) =
      -(Real.pi * Real.exp (21 / 100 : ℝ) - (169 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19402810148495137 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19402810148495137 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell168_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (21 / 200 : ℝ) (169 / 1600 : ℝ)) :
    (8011233603 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16200995331 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell168_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell168_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell169_leftExp :
    (12352211217 / 10000000000 : ℝ) ≤ Real.exp (169 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (169 / 800 : ℝ) (1006623400843 / 1000000000000 : ℝ)
    (12352211217 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell169_rightExp :
    Real.exp (17 / 80 : ℝ) ≤ (772978821 / 625000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (17 / 80 : ℝ) (503331361419 / 500000000000 : ℝ)
    (772978821 / 625000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell169_denomUpper :
    Real.exp (2395377040701853 / 625000000000000 : ℝ) ≤ (461826074529 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (2395377040701853 / 625000000000000 : ℝ) (140904532887 /
    125000000000 : ℝ) (461826074529 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell169_denomLower :
    (459445757091 / 10000000000 : ℝ) ≤ Real.exp (4784294742704683 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4784294742704683 / 1250000000000000 : ℝ) (1127054247771
    / 1000000000000 : ℝ) (459445757091 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell169_product_lower :
    (4850700992704683 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (169 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell169_leftExp
    (by norm_num : (0 : ℝ) ≤ (12352211217 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell169_product_upper :
    Real.pi * Real.exp (17 / 80 : ℝ) ≤ (2428384853201853 / 625000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell169_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell169_endpointLower :
    (3200481357 / 2000000000 : ℝ) ≤ hpThetaTraceEndpointLower (169 / 1600 : ℝ) (17 / 160 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4850700992704683 / 1250000000000000 : ℝ) (Real.pi * Real.exp (169 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell169_product_lower
  have hD : Real.exp (Real.pi * Real.exp (17 / 80 : ℝ) - (169 / 3200 : ℝ)) ≤
      (461826074529 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell169_denomUpper
    linarith [hpThetaJensenCell169_product_upper]
  have hi : (1 / (461826074529 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (17 / 80 : ℝ) - (169 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (461826074529 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (461826074529 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((169 / 3200 : ℝ) - Real.pi * Real.exp (17 / 80 : ℝ)) := by
    rw [show (169 / 3200 : ℝ) - Real.pi * Real.exp (17 / 80 : ℝ) =
      -(Real.pi * Real.exp (17 / 80 : ℝ) - (169 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (169 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (169 / 800 : ℝ)) := by
    have h := hpThetaJensenCell169_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (461826074529 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell169_endpointUpper :
    hpThetaJensenKernelEndpointUpper (169 / 1600 : ℝ) (17 / 160 : ℝ) ≤ (8090391773 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (17 / 80 : ℝ)) (2428384853201853 / 625000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (17 / 160 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell169_product_upper
  have hD : (459445757091 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (169 / 800 : ℝ) - (17 / 320 : ℝ)) := by
    apply le_trans hpThetaJensenCell169_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell169_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (169 / 800 : ℝ) - (17 / 320 : ℝ)) ≤
      (1 / (459445757091 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (459445757091 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((17 / 320 : ℝ) - Real.pi * Real.exp (169 / 800 : ℝ)) ≤
      (2 / (459445757091 / 10000000000 : ℝ) : ℝ) := by
    rw [show (17 / 320 : ℝ) - Real.pi * Real.exp (169 / 800 : ℝ) =
      -(Real.pi * Real.exp (169 / 800 : ℝ) - (17 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (2428384853201853 / 625000000000000 : ℝ) ^ 2 - 6 *
      (2428384853201853 / 625000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell169_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (169 / 1600 : ℝ) (17 / 160 : ℝ)) :
    (3200481357 / 2000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8090391773 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell169_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell169_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell170_leftExp :
    (2473532227 / 2000000000 : ℝ) ≤ Real.exp (17 / 80 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (17 / 80 : ℝ) (1006662722837 / 1000000000000 : ℝ)
    (2473532227 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell170_rightExp :
    Real.exp (171 / 800 : ℝ) ≤ (12383130379 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (171 / 800 : ℝ) (1006702046369 / 1000000000000 : ℝ)
    (12383130379 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell170_denomUpper :
    Real.exp (38371505716753747 / 10000000000000000 : ℝ) ≤ (18557236853 / 400000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38371505716753747 / 10000000000000000 : ℝ) (140924557313
    / 125000000000 : ℝ) (18557236853 / 400000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell170_denomLower :
    (461536952441 / 10000000000 : ℝ) ≤ Real.exp (957994257010673 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (957994257010673 / 250000000000000 : ℝ) (5636071017 /
    5000000000 : ℝ) (461536952441 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell170_product_lower :
    (971353632010673 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (17 / 80 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell170_leftExp
    (by norm_num : (0 : ℝ) ≤ (2473532227 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell170_product_upper :
    Real.pi * Real.exp (171 / 800 : ℝ) ≤ (38902755716753747 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell170_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell170_endpointLower :
    (7991124399 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 160 : ℝ) (171 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (971353632010673 / 250000000000000 : ℝ) (Real.pi * Real.exp (17 / 80 : ℝ))
    (by norm_num) hpThetaJensenCell170_product_lower
  have hD : Real.exp (Real.pi * Real.exp (171 / 800 : ℝ) - (17 / 320 : ℝ)) ≤
      (18557236853 / 400000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell170_denomUpper
    linarith [hpThetaJensenCell170_product_upper]
  have hi : (1 / (18557236853 / 400000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (171 / 800 : ℝ) - (17 / 320 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (18557236853 / 400000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (18557236853 / 400000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((17 / 320 : ℝ) - Real.pi * Real.exp (171 / 800 : ℝ)) := by
    rw [show (17 / 320 : ℝ) - Real.pi * Real.exp (171 / 800 : ℝ) =
      -(Real.pi * Real.exp (171 / 800 : ℝ) - (17 / 320 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (17 / 80 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (17 / 80 : ℝ)) := by
    have h := hpThetaJensenCell170_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (18557236853 / 400000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell170_endpointUpper :
    hpThetaJensenKernelEndpointUpper (17 / 160 : ℝ) (171 / 1600 : ℝ) ≤ (1616047313 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (171 / 800 : ℝ)) (38902755716753747 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (171 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell170_product_upper
  have hD : (461536952441 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (17 / 80 : ℝ) - (171 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell170_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell170_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (17 / 80 : ℝ) - (171 / 3200 : ℝ)) ≤
      (1 / (461536952441 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (461536952441 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((171 / 3200 : ℝ) - Real.pi * Real.exp (17 / 80 : ℝ)) ≤
      (2 / (461536952441 / 10000000000 : ℝ) : ℝ) := by
    rw [show (171 / 3200 : ℝ) - Real.pi * Real.exp (17 / 80 : ℝ) =
      -(Real.pi * Real.exp (17 / 80 : ℝ) - (171 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (38902755716753747 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (38902755716753747 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell170_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (17 / 160 : ℝ) (171 / 1600 : ℝ)) :
    (7991124399 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1616047313 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell170_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell170_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell171_leftExp :
    (6191565189 / 5000000000 : ℝ) ≤ Real.exp (171 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (171 / 800 : ℝ) (31459438949 / 31250000000 : ℝ)
    (6191565189 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell171_rightExp :
    Real.exp (43 / 200 : ℝ) ≤ (1239861897 / 1000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (43 / 200 : ℝ) (201348274287 / 200000000000 : ℝ)
    (1239861897 / 1000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell171_denomUpper :
    Real.exp (3841703956581921 / 1000000000000000 : ℝ) ≤ (4660481941 / 100000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (3841703956581921 / 1000000000000000 : ℝ) (140944611357 /
    125000000000 : ℝ) (4660481941 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell171_denomLower :
    (57955060099 / 1250000000 : ℝ) ≤ Real.exp (2397827708155111 / 625000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (2397827708155111 / 625000000000000 : ℝ) (563687197809 /
    500000000000 : ℝ) (57955060099 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell171_product_lower :
    (2431421458155111 / 625000000000000 : ℝ) ≤ Real.pi * Real.exp (171 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell171_leftExp
    (by norm_num : (0 : ℝ) ≤ (6191565189 / 5000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell171_product_upper :
    Real.pi * Real.exp (43 / 200 : ℝ) ≤ (3895141456581921 / 1000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell171_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell171_endpointLower :
    (7980996819 / 5000000000 : ℝ) ≤ hpThetaTraceEndpointLower (171 / 1600 : ℝ) (43 / 400 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (2431421458155111 / 625000000000000 : ℝ) (Real.pi * Real.exp (171 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell171_product_lower
  have hD : Real.exp (Real.pi * Real.exp (43 / 200 : ℝ) - (171 / 3200 : ℝ)) ≤
      (4660481941 / 100000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell171_denomUpper
    linarith [hpThetaJensenCell171_product_upper]
  have hi : (1 / (4660481941 / 100000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (43 / 200 : ℝ) - (171 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4660481941 / 100000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (4660481941 / 100000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((171 / 3200 : ℝ) - Real.pi * Real.exp (43 / 200 : ℝ)) := by
    rw [show (171 / 3200 : ℝ) - Real.pi * Real.exp (43 / 200 : ℝ) =
      -(Real.pi * Real.exp (43 / 200 : ℝ) - (171 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (171 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (171 / 800 : ℝ)) := by
    have h := hpThetaJensenCell171_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (4660481941 / 100000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell171_endpointUpper :
    hpThetaJensenKernelEndpointUpper (171 / 1600 : ℝ) (43 / 400 : ℝ) ≤ (16140064461 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (43 / 200 : ℝ)) (3895141456581921 / 1000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (43 / 400 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell171_product_upper
  have hD : (57955060099 / 1250000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (171 / 800 : ℝ) - (43 / 800 : ℝ)) := by
    apply le_trans hpThetaJensenCell171_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell171_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (171 / 800 : ℝ) - (43 / 800 : ℝ)) ≤
      (1 / (57955060099 / 1250000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (57955060099 / 1250000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((43 / 800 : ℝ) - Real.pi * Real.exp (171 / 800 : ℝ)) ≤
      (2 / (57955060099 / 1250000000 : ℝ) : ℝ) := by
    rw [show (43 / 800 : ℝ) - Real.pi * Real.exp (171 / 800 : ℝ) =
      -(Real.pi * Real.exp (171 / 800 : ℝ) - (43 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (3895141456581921 / 1000000000000000 : ℝ) ^ 2 - 6 *
      (3895141456581921 / 1000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell171_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (171 / 1600 : ℝ) (43 / 400 : ℝ)) :
    (7980996819 / 5000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16140064461 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell171_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell171_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell172_leftExp :
    (12398618969 / 10000000000 : ℝ) ≤ Real.exp (43 / 200 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (43 / 200 : ℝ) (503370685717 / 500000000000 : ℝ)
    (12398618969 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell172_rightExp :
    Real.exp (173 / 800 : ℝ) ≤ (6207063467 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (173 / 800 : ℝ) (503390349019 / 500000000000 : ℝ)
    (6207063467 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell172_denomUpper :
    Real.exp (19231317138482931 / 5000000000000000 : ℝ) ≤ (234088989517 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19231317138482931 / 5000000000000000 : ℝ) (1127717560523
    / 1000000000000 : ℝ) (234088989517 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell172_denomLower :
    (232878213673 / 5000000000 : ℝ) ≤ Real.exp (4801347145507331 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4801347145507331 / 1250000000000000 : ℝ) (140941853097 /
    125000000000 : ℝ) (232878213673 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell172_product_lower :
    (4868925270507331 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (43 / 200 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell172_leftExp
    (by norm_num : (0 : ℝ) ≤ (12398618969 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell172_product_upper :
    Real.pi * Real.exp (173 / 800 : ℝ) ≤ (19500067138482931 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell172_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell172_endpointLower :
    (199270521 / 125000000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 400 : ℝ) (173 / 1600 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4868925270507331 / 1250000000000000 : ℝ) (Real.pi * Real.exp (43 / 200 : ℝ))
    (by norm_num) hpThetaJensenCell172_product_lower
  have hD : Real.exp (Real.pi * Real.exp (173 / 800 : ℝ) - (43 / 800 : ℝ)) ≤
      (234088989517 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell172_denomUpper
    linarith [hpThetaJensenCell172_product_upper]
  have hi : (1 / (234088989517 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (173 / 800 : ℝ) - (43 / 800 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (234088989517 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (234088989517 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((43 / 800 : ℝ) - Real.pi * Real.exp (173 / 800 : ℝ)) := by
    rw [show (43 / 800 : ℝ) - Real.pi * Real.exp (173 / 800 : ℝ) =
      -(Real.pi * Real.exp (173 / 800 : ℝ) - (43 / 800 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (43 / 200 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (43 / 200 : ℝ)) := by
    have h := hpThetaJensenCell172_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (234088989517 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell172_endpointUpper :
    hpThetaJensenKernelEndpointUpper (43 / 400 : ℝ) (173 / 1600 : ℝ) ≤ (4029889483 / 2500000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (173 / 800 : ℝ)) (19500067138482931 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (173 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell172_product_upper
  have hD : (232878213673 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (43 / 200 : ℝ) - (173 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell172_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell172_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (43 / 200 : ℝ) - (173 / 3200 : ℝ)) ≤
      (1 / (232878213673 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (232878213673 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((173 / 3200 : ℝ) - Real.pi * Real.exp (43 / 200 : ℝ)) ≤
      (2 / (232878213673 / 5000000000 : ℝ) : ℝ) := by
    rw [show (173 / 3200 : ℝ) - Real.pi * Real.exp (43 / 200 : ℝ) =
      -(Real.pi * Real.exp (43 / 200 : ℝ) - (173 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19500067138482931 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19500067138482931 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell172_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (43 / 400 : ℝ) (173 / 1600 : ℝ)) :
    (199270521 / 125000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4029889483 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell172_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell172_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell173_leftExp :
    (12414126933 / 10000000000 : ℝ) ≤ Real.exp (173 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (173 / 800 : ℝ) (1006780698037 / 1000000000000 : ℝ)
    (12414126933 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell173_rightExp :
    Real.exp (87 / 400 : ℝ) ≤ (1553706787 / 1250000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (87 / 400 : ℝ) (503410013089 / 500000000000 : ℝ)
    (1553706787 / 1250000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell173_denomUpper :
    Real.exp (4813536241091691 / 1250000000000000 : ℝ) ≤ (94064072597 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (4813536241091691 / 1250000000000000 : ℝ) (1127878467877
    / 1000000000000 : ℝ) (94064072597 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell173_denomLower :
    (233942439113 / 5000000000 : ℝ) ≤ Real.exp (4807046482462167 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4807046482462167 / 1250000000000000 : ℝ) (225539098249 /
    200000000000 : ℝ) (233942439113 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell173_product_lower :
    (4875015232462167 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (173 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell173_leftExp
    (by norm_num : (0 : ℝ) ≤ (12414126933 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell173_product_upper :
    Real.pi * Real.exp (87 / 400 : ℝ) ≤ (4881114366091691 / 1250000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell173_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell173_endpointLower :
    (15921193311 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (173 / 1600 : ℝ) (87 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4875015232462167 / 1250000000000000 : ℝ) (Real.pi * Real.exp (173 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell173_product_lower
  have hD : Real.exp (Real.pi * Real.exp (87 / 400 : ℝ) - (173 / 3200 : ℝ)) ≤
      (94064072597 / 2000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell173_denomUpper
    linarith [hpThetaJensenCell173_product_upper]
  have hi : (1 / (94064072597 / 2000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (87 / 400 : ℝ) - (173 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (94064072597 / 2000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (94064072597 / 2000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((173 / 3200 : ℝ) - Real.pi * Real.exp (87 / 400 : ℝ)) := by
    rw [show (173 / 3200 : ℝ) - Real.pi * Real.exp (87 / 400 : ℝ) =
      -(Real.pi * Real.exp (87 / 400 : ℝ) - (173 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (173 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (173 / 800 : ℝ)) := by
    have h := hpThetaJensenCell173_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (94064072597 / 2000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell173_endpointUpper :
    hpThetaJensenKernelEndpointUpper (173 / 1600 : ℝ) (87 / 800 : ℝ) ≤ (1609895393 / 1000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (87 / 400 : ℝ)) (4881114366091691 / 1250000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (87 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell173_product_upper
  have hD : (233942439113 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (173 / 800 : ℝ) - (87 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell173_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell173_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (173 / 800 : ℝ) - (87 / 1600 : ℝ)) ≤
      (1 / (233942439113 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (233942439113 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((87 / 1600 : ℝ) - Real.pi * Real.exp (173 / 800 : ℝ)) ≤
      (2 / (233942439113 / 5000000000 : ℝ) : ℝ) := by
    rw [show (87 / 1600 : ℝ) - Real.pi * Real.exp (173 / 800 : ℝ) =
      -(Real.pi * Real.exp (173 / 800 : ℝ) - (87 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (4881114366091691 / 1250000000000000 : ℝ) ^ 2 - 6 *
      (4881114366091691 / 1250000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell173_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (173 / 1600 : ℝ) (87 / 800 : ℝ)) :
    (15921193311 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1609895393 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell173_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell173_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell174_leftExp :
    (2485930859 / 2000000000 : ℝ) ≤ Real.exp (87 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (87 / 400 : ℝ) (1006820026177 / 1000000000000 : ℝ)
    (2485930859 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell174_rightExp :
    Real.exp (7 / 32 : ℝ) ≤ (6222600539 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7 / 32 : ℝ) (1006859355853 / 1000000000000 : ℝ)
    (6222600539 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell174_denomUpper :
    Real.exp (19277003295118627 / 5000000000000000 : ℝ) ≤ (472475433047 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19277003295118627 / 5000000000000000 : ℝ) (1128039613257
    / 1000000000000 : ℝ) (472475433047 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell174_denomLower :
    (470025920213 / 10000000000 : ℝ) ≤ Real.exp (962550687398441 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (962550687398441 / 250000000000000 : ℝ) (225571279079 /
    200000000000 : ℝ) (470025920213 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell174_product_lower :
    (976222562398441 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (87 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell174_leftExp
    (by norm_num : (0 : ℝ) ≤ (2485930859 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell174_product_upper :
    Real.pi * Real.exp (7 / 32 : ℝ) ≤ (19548878295118627 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell174_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell174_endpointLower :
    (15900648931 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 800 : ℝ) (7 / 64 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (976222562398441 / 250000000000000 : ℝ) (Real.pi * Real.exp (87 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell174_product_lower
  have hD : Real.exp (Real.pi * Real.exp (7 / 32 : ℝ) - (87 / 1600 : ℝ)) ≤
      (472475433047 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell174_denomUpper
    linarith [hpThetaJensenCell174_product_upper]
  have hi : (1 / (472475433047 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (7 / 32 : ℝ) - (87 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (472475433047 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (472475433047 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((87 / 1600 : ℝ) - Real.pi * Real.exp (7 / 32 : ℝ)) := by
    rw [show (87 / 1600 : ℝ) - Real.pi * Real.exp (7 / 32 : ℝ) =
      -(Real.pi * Real.exp (7 / 32 : ℝ) - (87 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (87 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (87 / 400 : ℝ)) := by
    have h := hpThetaJensenCell174_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (472475433047 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell174_endpointUpper :
    hpThetaJensenKernelEndpointUpper (87 / 800 : ℝ) (7 / 64 : ℝ) ≤ (4019563209 / 2500000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (7 / 32 : ℝ)) (19548878295118627 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (7 / 64 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell174_product_upper
  have hD : (470025920213 / 10000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (87 / 400 : ℝ) - (7 / 128 : ℝ)) := by
    apply le_trans hpThetaJensenCell174_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell174_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (87 / 400 : ℝ) - (7 / 128 : ℝ)) ≤
      (1 / (470025920213 / 10000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (470025920213 / 10000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((7 / 128 : ℝ) - Real.pi * Real.exp (87 / 400 : ℝ)) ≤
      (2 / (470025920213 / 10000000000 : ℝ) : ℝ) := by
    rw [show (7 / 128 : ℝ) - Real.pi * Real.exp (87 / 400 : ℝ) =
      -(Real.pi * Real.exp (87 / 400 : ℝ) - (7 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19548878295118627 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19548878295118627 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell174_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (87 / 800 : ℝ) (7 / 64 : ℝ)) :
    (15900648931 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (4019563209 / 2500000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell174_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell174_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell175_leftExp :
    (12445201077 / 10000000000 : ℝ) ≤ Real.exp (7 / 32 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (7 / 32 : ℝ) (251714838963 / 250000000000 : ℝ)
    (12445201077 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell175_rightExp :
    Real.exp (11 / 50 : ℝ) ≤ (12460767307 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (11 / 50 : ℝ) (201379737413 / 200000000000 : ℝ)
    (12460767307 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell175_denomUpper :
    Real.exp (38599784346300051 / 10000000000000000 : ℝ) ≤ (118660819431 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38599784346300051 / 10000000000000000 : ℝ)
    (1128200997057 / 1000000000000 : ℝ) (118660819431 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell175_denomLower :
    (236089820179 / 5000000000 : ℝ) ≤ Real.exp (4818468017736823 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4818468017736823 / 1250000000000000 : ℝ) (564008768783 /
    500000000000 : ℝ) (236089820179 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell175_product_lower :
    (4887218017736823 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (7 / 32 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell175_leftExp
    (by norm_num : (0 : ℝ) ≤ (12445201077 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell175_product_upper :
    Real.pi * Real.exp (11 / 50 : ℝ) ≤ (39146659346300051 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell175_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell175_endpointLower :
    (3970002227 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 64 : ℝ) (11 / 100 : ℝ) := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4887218017736823 / 1250000000000000 : ℝ) (Real.pi * Real.exp (7 / 32 : ℝ))
    (by norm_num) hpThetaJensenCell175_product_lower
  have hD : Real.exp (Real.pi * Real.exp (11 / 50 : ℝ) - (7 / 128 : ℝ)) ≤
      (118660819431 / 2500000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell175_denomUpper
    linarith [hpThetaJensenCell175_product_upper]
  have hi : (1 / (118660819431 / 2500000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (11 / 50 : ℝ) - (7 / 128 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (118660819431 / 2500000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (118660819431 / 2500000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((7 / 128 : ℝ) - Real.pi * Real.exp (11 / 50 : ℝ)) := by
    rw [show (7 / 128 : ℝ) - Real.pi * Real.exp (11 / 50 : ℝ) =
      -(Real.pi * Real.exp (11 / 50 : ℝ) - (7 / 128 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (7 / 32 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (7 / 32 : ℝ)) := by
    have h := hpThetaJensenCell175_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (118660819431 / 2500000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell175_endpointUpper :
    hpThetaJensenKernelEndpointUpper (7 / 64 : ℝ) (11 / 100 : ℝ) ≤ (16057455059 / 10000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (11 / 50 : ℝ)) (39146659346300051 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (11 / 100 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell175_product_upper
  have hD : (236089820179 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (7 / 32 : ℝ) - (11 / 200 : ℝ)) := by
    apply le_trans hpThetaJensenCell175_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell175_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (7 / 32 : ℝ) - (11 / 200 : ℝ)) ≤
      (1 / (236089820179 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (236089820179 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((11 / 200 : ℝ) - Real.pi * Real.exp (7 / 32 : ℝ)) ≤
      (2 / (236089820179 / 5000000000 : ℝ) : ℝ) := by
    rw [show (11 / 200 : ℝ) - Real.pi * Real.exp (7 / 32 : ℝ) =
      -(Real.pi * Real.exp (7 / 32 : ℝ) - (11 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39146659346300051 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (39146659346300051 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell175_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (7 / 64 : ℝ) (11 / 100 : ℝ)) :
    (3970002227 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (16057455059 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell175_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell175_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell176_leftExp :
    (2492153461 / 2000000000 : ℝ) ≤ Real.exp (11 / 50 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (11 / 50 : ℝ) (125862335883 / 125000000000 : ℝ)
    (2492153461 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell176_rightExp :
    Real.exp (177 / 800 : ℝ) ≤ (2495270601 / 2000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (177 / 800 : ℝ) (1006938019813 / 1000000000000 : ℝ)
    (2495270601 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell176_denomUpper :
    Real.exp (7729124653207393 / 2000000000000000 : ℝ) ≤ (476823985483 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (7729124653207393 / 2000000000000000 : ℝ) (1128362619617
    / 1000000000000 : ℝ) (476823985483 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell176_denomLower :
    (237173063487 / 5000000000 : ℝ) ≤ Real.exp (964838046981239 / 250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (964838046981239 / 250000000000000 : ℝ) (564089459071 /
    500000000000 : ℝ) (237173063487 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell176_product_lower :
    (978666171981239 / 250000000000000 : ℝ) ≤ Real.pi * Real.exp (11 / 50 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell176_leftExp
    (by norm_num : (0 : ℝ) ≤ (2492153461 / 2000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell176_product_upper :
    Real.pi * Real.exp (177 / 800 : ℝ) ≤ (7839124653207393 / 2000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell176_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell176_endpointLower :
    (15859273651 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 100 : ℝ) (177 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (978666171981239 / 250000000000000 : ℝ) (Real.pi * Real.exp (11 / 50 : ℝ))
    (by norm_num) hpThetaJensenCell176_product_lower
  have hD : Real.exp (Real.pi * Real.exp (177 / 800 : ℝ) - (11 / 200 : ℝ)) ≤
      (476823985483 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell176_denomUpper
    linarith [hpThetaJensenCell176_product_upper]
  have hi : (1 / (476823985483 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (177 / 800 : ℝ) - (11 / 200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (476823985483 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (476823985483 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((11 / 200 : ℝ) - Real.pi * Real.exp (177 / 800 : ℝ)) := by
    rw [show (11 / 200 : ℝ) - Real.pi * Real.exp (177 / 800 : ℝ) =
      -(Real.pi * Real.exp (177 / 800 : ℝ) - (11 / 200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (11 / 50 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (11 / 50 : ℝ)) := by
    have h := hpThetaJensenCell176_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (476823985483 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell176_endpointUpper :
    hpThetaJensenKernelEndpointUpper (11 / 100 : ℝ) (177 / 1600 : ℝ) ≤ (1002285061 / 625000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (177 / 800 : ℝ)) (7839124653207393 / 2000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (177 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell176_product_upper
  have hD : (237173063487 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (11 / 50 : ℝ) - (177 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell176_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell176_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (11 / 50 : ℝ) - (177 / 3200 : ℝ)) ≤
      (1 / (237173063487 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (237173063487 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((177 / 3200 : ℝ) - Real.pi * Real.exp (11 / 50 : ℝ)) ≤
      (2 / (237173063487 / 5000000000 : ℝ) : ℝ) := by
    rw [show (177 / 3200 : ℝ) - Real.pi * Real.exp (11 / 50 : ℝ) =
      -(Real.pi * Real.exp (11 / 50 : ℝ) - (177 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (7839124653207393 / 2000000000000000 : ℝ) ^ 2 - 6 *
      (7839124653207393 / 2000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell176_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (11 / 100 : ℝ) (177 / 1600 : ℝ)) :
    (15859273651 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1002285061 / 625000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell176_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell176_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell177_leftExp :
    (12476353003 / 10000000000 : ℝ) ≤ Real.exp (177 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (177 / 800 : ℝ) (251734504953 / 250000000000 : ℝ)
    (12476353003 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell177_rightExp :
    Real.exp (89 / 400 : ℝ) ≤ (12491958197 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (89 / 400 : ℝ) (503488677049 / 500000000000 : ℝ)
    (12491958197 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell177_denomUpper :
    Real.exp (38691523427987821 / 10000000000000000 : ℝ) ≤ (479017645921 / 10000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (38691523427987821 / 10000000000000000 : ℝ) (112852448131
    / 100000000000 : ℝ) (479017645921 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell177_denomLower :
    (95305093751 / 2000000000 : ℝ) ≤ Real.exp (4829920097925097 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4829920097925097 / 1250000000000000 : ℝ) (282085134371 /
    250000000000 : ℝ) (95305093751 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell177_product_lower :
    (4899451347925097 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (177 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell177_leftExp
    (by norm_num : (0 : ℝ) ≤ (12476353003 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell177_product_upper :
    Real.pi * Real.exp (89 / 400 : ℝ) ≤ (39244648427987821 / 10000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell177_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell177_endpointLower :
    (3959610887 / 2500000000 : ℝ) ≤ hpThetaTraceEndpointLower (177 / 1600 : ℝ) (89 / 800 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4899451347925097 / 1250000000000000 : ℝ) (Real.pi * Real.exp (177 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell177_product_lower
  have hD : Real.exp (Real.pi * Real.exp (89 / 400 : ℝ) - (177 / 3200 : ℝ)) ≤
      (479017645921 / 10000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell177_denomUpper
    linarith [hpThetaJensenCell177_product_upper]
  have hi : (1 / (479017645921 / 10000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (89 / 400 : ℝ) - (177 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (479017645921 / 10000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (479017645921 / 10000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((177 / 3200 : ℝ) - Real.pi * Real.exp (89 / 400 : ℝ)) := by
    rw [show (177 / 3200 : ℝ) - Real.pi * Real.exp (89 / 400 : ℝ) =
      -(Real.pi * Real.exp (89 / 400 : ℝ) - (177 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (177 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (177 / 800 : ℝ)) := by
    have h := hpThetaJensenCell177_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (479017645921 / 10000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell177_endpointUpper :
    hpThetaJensenKernelEndpointUpper (177 / 1600 : ℝ) (89 / 800 : ℝ) ≤ (8007785493 / 5000000000 :
      ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (89 / 400 : ℝ)) (39244648427987821 / 10000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (89 / 800 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell177_product_upper
  have hD : (95305093751 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (177 / 800 : ℝ) - (89 / 1600 : ℝ)) := by
    apply le_trans hpThetaJensenCell177_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell177_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (177 / 800 : ℝ) - (89 / 1600 : ℝ)) ≤
      (1 / (95305093751 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (95305093751 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((89 / 1600 : ℝ) - Real.pi * Real.exp (177 / 800 : ℝ)) ≤
      (2 / (95305093751 / 2000000000 : ℝ) : ℝ) := by
    rw [show (89 / 1600 : ℝ) - Real.pi * Real.exp (177 / 800 : ℝ) =
      -(Real.pi * Real.exp (177 / 800 : ℝ) - (89 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (39244648427987821 / 10000000000000000 : ℝ) ^ 2 - 6 *
      (39244648427987821 / 10000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell177_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (177 / 1600 : ℝ) (89 / 800 : ℝ)) :
    (3959610887 / 2500000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (8007785493 / 5000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell177_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell177_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell178_leftExp :
    (3122989549 / 2500000000 : ℝ) ≤ Real.exp (89 / 400 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (89 / 400 : ℝ) (1006977354097 / 1000000000000 : ℝ)
    (3122989549 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell178_rightExp :
    Real.exp (179 / 800 : ℝ) ≤ (3126895727 / 2500000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (179 / 800 : ℝ) (1007016689919 / 1000000000000 : ℝ)
    (3126895727 / 2500000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell178_denomUpper :
    Real.exp (9684371227673111 / 2500000000000000 : ℝ) ≤ (240612174661 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9684371227673111 / 2500000000000000 : ℝ) (282171645627 /
    250000000000 : ℝ) (240612174661 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell178_denomLower :
    (95743551049 / 2000000000 : ℝ) ≤ Real.exp (1208914404152751 / 312500000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (1208914404152751 / 312500000000000 : ℝ) (225700479193 /
    200000000000 : ℝ) (95743551049 / 2000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell178_product_lower :
    (1226394872902751 / 312500000000000 : ℝ) ≤ Real.pi * Real.exp (89 / 400 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell178_leftExp
    (by norm_num : (0 : ℝ) ≤ (3122989549 / 2500000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell178_product_upper :
    Real.pi * Real.exp (179 / 800 : ℝ) ≤ (9823433727673111 / 2500000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell178_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell178_endpointLower :
    (1581751899 / 1000000000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 800 : ℝ) (179 / 1600 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (1226394872902751 / 312500000000000 : ℝ) (Real.pi * Real.exp (89 / 400 : ℝ))
    (by norm_num) hpThetaJensenCell178_product_lower
  have hD : Real.exp (Real.pi * Real.exp (179 / 800 : ℝ) - (89 / 1600 : ℝ)) ≤
      (240612174661 / 5000000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell178_denomUpper
    linarith [hpThetaJensenCell178_product_upper]
  have hi : (1 / (240612174661 / 5000000000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (179 / 800 : ℝ) - (89 / 1600 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (240612174661 / 5000000000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (240612174661 / 5000000000 : ℝ) : ℝ) ≤
      2 * Real.exp ((89 / 1600 : ℝ) - Real.pi * Real.exp (179 / 800 : ℝ)) := by
    rw [show (89 / 1600 : ℝ) - Real.pi * Real.exp (179 / 800 : ℝ) =
      -(Real.pi * Real.exp (179 / 800 : ℝ) - (89 / 1600 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (89 / 400 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (89 / 400 : ℝ)) := by
    have h := hpThetaJensenCell178_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (240612174661 / 5000000000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell178_endpointUpper :
    hpThetaJensenKernelEndpointUpper (89 / 800 : ℝ) (179 / 1600 : ℝ) ≤ (15994485483 / 10000000000
      : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (179 / 800 : ℝ)) (9823433727673111 / 2500000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (179 / 1600 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell178_product_upper
  have hD : (95743551049 / 2000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (89 / 400 : ℝ) - (179 / 3200 : ℝ)) := by
    apply le_trans hpThetaJensenCell178_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell178_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (89 / 400 : ℝ) - (179 / 3200 : ℝ)) ≤
      (1 / (95743551049 / 2000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (95743551049 / 2000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((179 / 3200 : ℝ) - Real.pi * Real.exp (89 / 400 : ℝ)) ≤
      (2 / (95743551049 / 2000000000 : ℝ) : ℝ) := by
    rw [show (179 / 3200 : ℝ) - Real.pi * Real.exp (89 / 400 : ℝ) =
      -(Real.pi * Real.exp (89 / 400 : ℝ) - (179 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (9823433727673111 / 2500000000000000 : ℝ) ^ 2 - 6 *
      (9823433727673111 / 2500000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell178_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (89 / 800 : ℝ) (179 / 1600 : ℝ)) :
    (1581751899 / 1000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (15994485483 / 10000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell178_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell178_endpointUpper

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell179_leftExp :
    (12507582907 / 10000000000 : ℝ) ≤ Real.exp (179 / 800 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (179 / 800 : ℝ) (503508344959 / 500000000000 : ℝ)
    (12507582907 / 10000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell179_rightExp :
    Real.exp (9 / 40 : ℝ) ≤ (6261613581 / 5000000000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (9 / 40 : ℝ) (251764006819 / 250000000000 : ℝ)
    (6261613581 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell179_denomUpper :
    Real.exp (19391753894774533 / 5000000000000000 : ℝ) ≤ (1510763083 / 31250000 : ℝ) := by
  apply hpThetaJensen_exp_upper_scaled32 (19391753894774533 / 5000000000000000 : ℝ) (45153956943 /
    40000000000 : ℝ) (1510763083 / 31250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact rational Taylor and power certificates need a larger tactic budget.
theorem hpThetaJensenCell179_denomLower :
    (240461538193 / 5000000000 : ℝ) ≤ Real.exp (4841402799995993 / 1250000000000000 : ℝ) := by
  apply hpThetaJensen_exp_lower_scaled32 (4841402799995993 / 1250000000000000 : ℝ) (70541530871 /
    62500000000 : ℝ) (240461538193 / 5000000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]
  · norm_num

theorem hpThetaJensenCell179_product_lower :
    (4911715299995993 / 1250000000000000 : ℝ) ≤ Real.pi * Real.exp (179 / 800 : ℝ) := by
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell179_leftExp
    (by norm_num : (0 : ℝ) ≤ (12507582907 / 10000000000 : ℝ)) (le_of_lt Real.pi_pos)
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell179_product_upper :
    Real.pi * Real.exp (9 / 40 : ℝ) ≤ (19671441394774533 / 5000000000000000 : ℝ) := by
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have h := mul_le_mul hpi hpThetaJensenCell179_rightExp
    (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ (3141593 / 1000000 : ℝ))
  norm_num at h ⊢
  exact h

theorem hpThetaJensenCell179_endpointLower :
    (15796500371 / 10000000000 : ℝ) ≤ hpThetaTraceEndpointLower (179 / 1600 : ℝ) (9 / 80 : ℝ) :=
      by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (4911715299995993 / 1250000000000000 : ℝ) (Real.pi * Real.exp (179 / 800 : ℝ))
    (by norm_num) hpThetaJensenCell179_product_lower
  have hD : Real.exp (Real.pi * Real.exp (9 / 40 : ℝ) - (179 / 3200 : ℝ)) ≤
      (1510763083 / 31250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hpThetaJensenCell179_denomUpper
    linarith [hpThetaJensenCell179_product_upper]
  have hi : (1 / (1510763083 / 31250000 : ℝ) : ℝ) ≤
      1 / Real.exp (Real.pi * Real.exp (9 / 40 : ℝ) - (179 / 3200 : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (1510763083 / 31250000 : ℝ))
      (Real.exp_pos _)).2
    simpa only [one_mul] using hD
  have hE : (2 / (1510763083 / 31250000 : ℝ) : ℝ) ≤
      2 * Real.exp ((179 / 3200 : ℝ) - Real.pi * Real.exp (9 / 40 : ℝ)) := by
    rw [show (179 / 3200 : ℝ) - Real.pi * Real.exp (9 / 40 : ℝ) =
      -(Real.pi * Real.exp (9 / 40 : ℝ) - (179 / 3200 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hP0 : 0 ≤ 4 * (Real.pi * Real.exp (179 / 800 : ℝ)) ^ 2 -
      6 * (Real.pi * Real.exp (179 / 800 : ℝ)) := by
    have h := hpThetaJensenCell179_product_lower
    nlinarith
  have h := mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 2 / (1510763083 / 31250000 : ℝ)) hP0
  unfold hpThetaTraceEndpointLower
  norm_num at h ⊢
  linarith

theorem hpThetaJensenCell179_endpointUpper :
    hpThetaJensenKernelEndpointUpper (179 / 1600 : ℝ) (9 / 80 : ℝ) ≤ (1597330487 / 1000000000 : ℝ)
      := by
  have hP := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (9 / 40 : ℝ)) (19671441394774533 / 5000000000000000 : ℝ)
    (by
      have h := hpThetaTrace_pi_exp_ge_three (9 / 80 : ℝ) (by norm_num)
      norm_num at h
      exact h)
    hpThetaJensenCell179_product_upper
  have hD : (240461538193 / 5000000000 : ℝ) ≤
      Real.exp (Real.pi * Real.exp (179 / 800 : ℝ) - (9 / 160 : ℝ)) := by
    apply le_trans hpThetaJensenCell179_denomLower (Real.exp_le_exp.mpr ?_)
    linarith [hpThetaJensenCell179_product_lower]
  have hi : 1 / Real.exp (Real.pi * Real.exp (179 / 800 : ℝ) - (9 / 160 : ℝ)) ≤
      (1 / (240461538193 / 5000000000 : ℝ) : ℝ) := by
    apply (div_le_div_iff₀ (Real.exp_pos _)
      (by norm_num : (0 : ℝ) < (240461538193 / 5000000000 : ℝ))).2
    simpa only [one_mul] using hD
  have hE : 2 * Real.exp ((9 / 160 : ℝ) - Real.pi * Real.exp (179 / 800 : ℝ)) ≤
      (2 / (240461538193 / 5000000000 : ℝ) : ℝ) := by
    rw [show (9 / 160 : ℝ) - Real.pi * Real.exp (179 / 800 : ℝ) =
      -(Real.pi * Real.exp (179 / 800 : ℝ) - (9 / 160 : ℝ)) by ring, Real.exp_neg]
    have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [div_eq_mul_inv, one_mul] using h
  have h := mul_le_mul hP hE (by positivity)
    (by norm_num : (0 : ℝ) ≤ 4 * (19671441394774533 / 5000000000000000 : ℝ) ^ 2 - 6 *
      (19671441394774533 / 5000000000000000 : ℝ))
  have hc := mul_le_mul_of_nonneg_left h
    (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
  unfold hpThetaJensenKernelEndpointUpper
  norm_num at hc ⊢
  linarith

theorem hpThetaJensenCell179_kernel_bounds (u : ℝ)
    (hu : u ∈ Set.Icc (179 / 1600 : ℝ) (9 / 80 : ℝ)) :
    (15796500371 / 10000000000 : ℝ) ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ (1597330487 / 1000000000 : ℝ) := by
  constructor
  · exact le_trans hpThetaJensenCell179_endpointLower
      (hpThetaJensenKernel_endpointLower_le _ _ u (by norm_num) hu.1 hu.2)
  · exact le_trans
      (hpThetaJensenKernel_le_endpointUpper _ _ u (by norm_num) hu.1 hu.2)
      hpThetaJensenCell179_endpointUpper

def hpThetaJensenCellsBatch008Lower (j : ℕ) : ℝ :=
  match j with
  | 0 => (16179392873 / 10000000000 : ℝ)
  | 1 => (16160126559 / 10000000000 : ℝ)
  | 2 => (16140759673 / 10000000000 : ℝ)
  | 3 => (3224258517 / 2000000000 : ℝ)
  | 4 => (16101725663 / 10000000000 : ℝ)
  | 5 => (16082059291 / 10000000000 : ℝ)
  | 6 => (8031146919 / 5000000000 : ℝ)
  | 7 => (4010607421 / 2500000000 : ℝ)
  | 8 => (8011233603 / 5000000000 : ℝ)
  | 9 => (3200481357 / 2000000000 : ℝ)
  | 10 => (7991124399 / 5000000000 : ℝ)
  | 11 => (7980996819 / 5000000000 : ℝ)
  | 12 => (199270521 / 125000000 : ℝ)
  | 13 => (15921193311 / 10000000000 : ℝ)
  | 14 => (15900648931 / 10000000000 : ℝ)
  | 15 => (3970002227 / 2500000000 : ℝ)
  | 16 => (15859273651 / 10000000000 : ℝ)
  | 17 => (3959610887 / 2500000000 : ℝ)
  | 18 => (1581751899 / 1000000000 : ℝ)
  | 19 => (15796500371 / 10000000000 : ℝ)
  | _ => 0

def hpThetaJensenCellsBatch008Upper (j : ℕ) : ℝ :=
  match j with
  | 0 => (817954651 / 500000000 : ℝ)
  | 1 => (8169841999 / 5000000000 : ℝ)
  | 2 => (3264034663 / 2000000000 : ℝ)
  | 3 => (3260112269 / 2000000000 : ℝ)
  | 4 => (3256169693 / 2000000000 : ℝ)
  | 5 => (16261035043 / 10000000000 : ℝ)
  | 6 => (16241121459 / 10000000000 : ℝ)
  | 7 => (126727407 / 78125000 : ℝ)
  | 8 => (16200995331 / 10000000000 : ℝ)
  | 9 => (8090391773 / 5000000000 : ℝ)
  | 10 => (1616047313 / 1000000000 : ℝ)
  | 11 => (16140064461 / 10000000000 : ℝ)
  | 12 => (4029889483 / 2500000000 : ℝ)
  | 13 => (1609895393 / 1000000000 : ℝ)
  | 14 => (4019563209 / 2500000000 : ℝ)
  | 15 => (16057455059 / 10000000000 : ℝ)
  | 16 => (1002285061 / 625000000 : ℝ)
  | 17 => (8007785493 / 5000000000 : ℝ)
  | 18 => (15994485483 / 10000000000 : ℝ)
  | 19 => (1597330487 / 1000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem hpThetaJensenCellsBatch008_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaJensenCellsBatch008Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ hpThetaJensenCellsBatch008Upper j.val := by
  fin_cases j
  · have h := hpThetaJensenCell160_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell161_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell162_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell163_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell164_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell165_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell166_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell167_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell168_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell169_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell170_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell171_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell172_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell173_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell174_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell175_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell176_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell177_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell178_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h
  · have h := hpThetaJensenCell179_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper] at h ⊢
    exact h

end HodgeProofHP
